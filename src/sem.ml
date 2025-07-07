open Typed

module Index : sig
  type t = private (int * int) list

  val compare : t -> t -> int

  val zero : t

  val add : t -> int -> t

  val push : t -> int -> t

  val to_string : t -> string

  module Map : Map.S with type key = t
end = struct
  type t = (int * int) list

  let compare = compare

  let zero = [ 0, 0 ]

  let add i k =
    match i with
    | [] -> assert false
    | (n, j) :: i' -> (n, j + k) :: i'
  ;;

  let push i n = (n, 0) :: i

  let to_string i =
    "\"" ^ (String.concat "__" @@ List.rev_map (fun (a, b) -> Printf.sprintf "%d.%d" a b) i) ^ "\""
  ;;

  module Map = Map.Make(struct
      type nonrec t = t
      let compare = compare
    end)
end

type fact = fact' Typed.loc_env

and fact' =
  | Channel of
      { channel : expr
      ; name : name
      ; args : expr list
      } (** Channel fact [ch :: name(args)] *)
  | Out of expr (** Attacker fact: Out *)
  | In of expr (** Attacker fact: In *)
  | Plain of name * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      } (** File fact [path.contents] *)
  | Fresh of ident
  | Constant of ident * ident option * expr
  | Init of string
  | Global of string * expr list
  | Structure of
      { name : name
      ; process : ident
      ; address : expr
      ; args : expr list
      } (** Structure fact [name(process, address, args)] *)
  | Loop of
      { mode : loop_mode
      ; process : ident
      ; index : name
      }
  | Access of { pid: ident; target: expr; syscall: ident option }
  | AccessX of { pid: ident; target: ident; parameter: expr option option; syscall: ident option }

let string_of_fact f =
  match f.desc with
  | Channel { channel= ({ desc= Ident _; _ } as channel); name; args } ->
      Printf.sprintf "%s::%s(%s)" (string_of_expr channel) name (String.concat ", " @@ List.map string_of_expr args)
  | Channel { channel; name; args } ->
      Printf.sprintf "(%s)::%s(%s)" (string_of_expr channel) name (String.concat ", " @@ List.map string_of_expr args)
  | Out e -> Printf.sprintf "Out(%s)" @@ string_of_expr e
  | In e -> Printf.sprintf "In(%s)" @@ string_of_expr e
  | Plain (s, args) -> Printf.sprintf "%s(%s)" s (String.concat ", " @@ List.map string_of_expr args)
  | Eq (e1, e2) -> Printf.sprintf "%s = %s" (string_of_expr e1) (string_of_expr e2)
  | Neq (e1, e2) -> Printf.sprintf "%s != %s" (string_of_expr e1) (string_of_expr e2)
  | File { path; contents } ->
      let path =
        match path.desc with
        | Ident _ -> string_of_expr path
        | _ -> "(" ^ string_of_expr path ^ ")"
      in
      let contents =
        match contents.desc with
        | Ident _ -> string_of_expr contents
        | _ -> "(" ^ string_of_expr contents ^ ")"
      in
      path ^ "." ^ contents
  | Fresh id -> "Fr " ^ Ident.to_string id
  | Constant (id, None, e) -> Printf.sprintf "Const(%s, %s)" (Ident.to_string id) (string_of_expr e)
  | Constant (id, Some p, e) -> Printf.sprintf "Const(%s<%s>, %s)" (Ident.to_string id) (Ident.to_string p) (string_of_expr e)
  | Init s -> Printf.sprintf "Init %s" s
  | Global (s, args) -> Printf.sprintf "::%s(%s)" s (String.concat ", " @@ List.map string_of_expr args)
  | Structure { name; process; address; args } ->
      Printf.sprintf "Structure(%s, %s, %s, %s)" name (Ident.to_string process) (string_of_expr address) (String.concat "," (List.map string_of_expr args))
  | Loop { mode; process; index } ->
      let mode = match mode with
        | In -> "In"
        | Back -> "Back"
        | Out -> "Out"
      in
      Printf.sprintf "Loop%s(%s, %s)" mode (Ident.to_string process) index
  | Access { pid; target; syscall } ->
      let syscall =
        match syscall with
        | None -> "."
        | Some syscall -> Ident.to_string syscall
      in
      Printf.sprintf "Access(%s, %s, %s)" (Ident.to_string pid) (string_of_expr target) syscall
  | AccessX { pid; target; parameter; syscall } ->
      let parameter =
        match parameter with
        | None -> "None"
        | Some None -> "Some (None)"
        | Some (Some parameter) -> string_of_expr parameter
      in
      let syscall =
        match syscall with
        | None -> "."
        | Some syscall -> Ident.to_string syscall
      in
      Printf.sprintf "AccessX(%s, %s, %s, %s)" (Ident.to_string pid) (Ident.to_string target) parameter syscall

let fact_of_typed (f : Typed.fact) : fact =
  let desc : fact' =
    match f.desc with
    | Channel { channel; name; args} -> Channel { channel; name; args }
    | Out e -> Out e
    | In e -> In e
    | Plain (name, es) -> Plain (name, es)
    | Eq (e1, e2) -> Eq (e1, e2)
    | Neq (e1, e2) -> Neq (e1, e2)
    | File { path; contents } -> File { path; contents }
    | Global (name, es) -> Global (name, es)
  in
  { f with desc }

type update =
  { register : expr option (* None: \rho *)
  ; mutable_overrides : (Ident.t * expr option (* None: \rho *)) list
  ; drops : Ident.t list
  }

let string_of_update u =
  String.concat "; " @@
  (Printf.sprintf "ret= %s" (match u.register with None -> "R" | Some e -> string_of_expr e))
  ::
    List.map (fun (id, eo) ->
      Printf.sprintf "%s= %s" (Ident.to_string id) (match eo with None -> "R" | Some e -> string_of_expr e))
      u.mutable_overrides
  @ List.map (fun id -> Printf.sprintf "%s= _" (Ident.to_string id)) u.drops

(**
                      update  tag
                          ↓   ↓
                          f, [T]
   [A]^i_{\Gamma_i} -----------------> [B]^j_{\Gamma_j}
    ↑  ↑      ↑                         ↑  ↑      ↑
   pre |      |                      post  |      |
     source source_env                 target target_env
*)
type edge =
  { id : Ident.t
  ; source : Index.t
  ; source_env : Env.t
  ; pre : fact list
  ; update : update
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  }

let check_edge_invariants (e : edge) =
  List.iter (fun (v, _) ->
      (* Overridden variables must be in [target_env] *)
      (match List.assoc_opt v e.target_env.vars with
       | Some (Var _) -> ()
       | _ -> assert false);
      (* Overridden variables can be in [source_env] *)
      (match List.assoc_opt v e.source_env.vars with
       | Some (Var _) -> ()
       | None -> ()
       | _ -> assert false);
    ) e.update.mutable_overrides;
  List.iter (fun v ->
      (* Dropped/Popped-up variables must be in source_env *)
      match List.assoc_opt v e.source_env.vars with
      | Some (Var _) -> ()
      | _ -> assert false
    ) e.update.drops

type graph = edge list

let evar env id =
    { env
    ; loc = Location.nowhere
    ; desc = Ident { id; desc = Var (Loc (snd id)); param = None }
    }
;;

(* <\Gamma |- c>i *)
let rec graph_cmd find_def ~process i (c : cmd) : graph * Index.t * Env.t =
  let env = c.env in
  let update_unit =
    { register = Some { env; loc = Location.nowhere; desc = Unit }
    ; mutable_overrides = []
    ; drops = []
    }
  in
  let update_id = { register = None; mutable_overrides = []; drops = [] } in
  let fact env desc : fact = { env; desc; loc = Location.nowhere } in
  match c.desc with
  | Skip ->
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "skip"
          ; source = i (* transition_from *)
          ; source_env = env
          ; pre = [] (* transition_pre *)
          ; update = update_unit (* transition_state_transition *)
          ; tag = [] (* transition_label *)
          ; post = [] (* transition_post *)
          ; target = i_1 (* transition_to *)
          ; target_env = env
          }
        ]
      , i_1, env )
  | Sequence (c1, c2) ->
      let g1, j, _ = graph_cmd find_def ~process i c1 in
      let g2, k, env_k = graph_cmd find_def ~process j c2 in
      g1 @ g2, k, env_k
  | Put fs ->
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "put"
          ; source = i
          ; source_env = env
          ; pre = []
          ; update = update_unit
          ; tag = []
          ; post = List.map fact_of_typed fs
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | Let (x, e, c) ->
      (* var x := e in c *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd find_def ~process i_1 c in
      let j_1 = Index.add j 1 in
      ( { id = Ident.local ("let_def_" ^ fst x)
        ; source = i
        ; source_env = env
        ; pre = []
        ; update = { update_unit with mutable_overrides = [ x, Some e ] }
        ; tag = []
        ; post = []
        ; target = i_1
        ; target_env = c.env
        }
        :: { id = Ident.local ("let_exit_" ^ fst x)
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = { update_id with drops= [x] }
           ; tag = []
           ; post = []
           ; target = j_1
           ; target_env = env
           }
        :: g
      , j_1, env )
  | Assign (Some x, ({ desc= Apply _; _ } as app)) ->
      let g, j, env_j = graph_application ~process find_def i app in
      let j_1 = Index.add j 1 in
      (  { id = Ident.local "assign_call"
         ; source = j
         ; source_env = env_j
         ; pre = []
         ; update = { update_unit with mutable_overrides = [ x, None (* \rho *) ] }
         ; tag = []
         ; post = []
         ; target = j_1
         ; target_env = env
         }
         :: g
      , j_1, env )
  | Assign (None, ({ desc= Apply _; _ } as app)) ->
      let g, j, env_j = graph_application ~process find_def i app in
      let j_1 = Index.add j 1 in
      (  { id = Ident.local "call"
         ; source = j
         ; source_env = env_j
         ; pre = []
         ; update = update_unit
         ; tag = []
         ; post = []
         ; target = j_1
         ; target_env = env
         }
         :: g
      , j_1, env )
  | Assign (Some x, e) ->
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "assign"
          ; source = i
          ; source_env = env
          ; pre = []
          ; update = { update_unit with mutable_overrides = [ x, Some e ] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env)
  | Assign (None, _e) ->
      (* XXX e is lost... *)
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "ignore"
          ; source = i
          ; source_env = env
          ; pre = []
          ; update = update_unit
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | Event facts ->
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "event"
          ; source = i
          ; source_env = env
          ; pre = []
          ; update = update_unit
          ; tag = List.map fact_of_typed facts
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | Return e ->
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "return"
          ; source = i
          ; source_env = env
          ; pre = []
          ; update = { register = Some e; mutable_overrides = []; drops = [] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | New (x, _, eopt, c) ->
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd find_def ~process i_1 c in
      let j_1 = Index.add j 1 in
      ( { id = Ident.local "new_intro"
        ; source = i
        ; source_env = env
        ; pre = [ fact c.env @@ Fresh x ]
        ; update = update_unit
        ; tag = []
        ; post = []
        ; target = i_1
        ; target_env = c.env
        }
        :: { id = Ident.local "new_out"
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = { update_id with drops= [x] }
           ; tag = []
           ; post =
               (match eopt with
                | None -> []
                | Some (s, es) ->
                    [ fact c.env
                      @@ Structure
                           { name = s; process; address = evar c.env x; args = es }
                    ])
           ; target = j_1
           ; target_env = env
           }
        :: g (* XXX No drop of x? *)
      , j_1, env )
  | Get (xs, e, s, c) ->
      (* [let x1,..,xn := e.S in c] *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd find_def ~process i_1 c in
      let j_1 = Index.add j 1 in
      let pre_and_post : fact list =
        [ fact env
          @@ Structure { name = s; process; address = e; args = List.map (evar c.env) xs }
        ]
      in
      ( { id = Ident.local "get_intro"
        ; source = i
        ; source_env = env
        ; pre = pre_and_post
        ; update = update_unit
        ; tag = []
        ; post = pre_and_post
        ; target = i_1
        ; target_env = c.env
        }
        :: { id = Ident.local "get_out"
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = { update_id with drops= xs }
           ; tag = []
           ; post = []
           ; target = j_1
           ; target_env = env
           }
        :: g
      , j_1, env )
  | Del (e, s) ->
      let i_1 = Index.add i 1 in
      let arity =
        match Env.find_fact_opt env s with
        | Some (Structure, Some arity) -> arity
        | _ -> assert false (* XXX *)
      in
      let xs =
        List.init arity
        @@ fun i ->
        let id = Ident.local (Printf.sprintf "x%d" i) in

          { env (* XXX vars are not defied in env *)
          ; loc = Location.nowhere
          ; desc = Ident { id; desc = Var (Loc (snd id)); param = None }
          }
      in
      ( [ { id = Ident.local "del"
          ; source = i
          ; source_env = env
          ; pre = [ fact env @@ Structure { name = s; process; address = e; args = xs } ]
          ; update = update_unit
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | Case cases ->
      let i_1 = Index.add i 1 in
      let es =
        List.concat
        @@ List.mapi
             (fun j (case : case) ->
                (* XXX case.cmd.env == case.fresh @ env *)
                let ij = Index.push i j in
                let gj, bj (* bold j *), env_bj = graph_cmd find_def ~process ij case.cmd in
                { id= Ident.local "case_in"
                ; source = i
                ; source_env = env
                ; pre = List.map fact_of_typed case.facts
                ; update = update_unit
                ; tag = []
                ; post = []
                ; target = ij
                ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                }
                :: { id= Ident.local "case_out"
                   ; source = bj
                   ; source_env = env_bj
                   ; pre = []
                   ; update = { update_id with drops= case.fresh }
                   ; tag = []
                   ; post = []
                   ; target = i_1
                   ; target_env = env
                   }
                :: gj)
             cases
      in
      es, i_1, env
  | While (cases, cases') ->
      let i_1 = Index.add i 1 in
      let i_2 = Index.add i 2 in
      let n = List.length cases in
      let es =
        ({ id= Ident.local "repeat_in"
         ; source = i
         ; source_env = env
         ; pre = []
         ; update = update_unit
         ; tag = [ fact env @@ Loop { mode = In; process; index = Index.to_string i } ]
         ; post = []
         ; target = i_1
         ; target_env = env
         }
         :: List.concat
              (List.mapi
                 (fun j (case : case) ->
                    (* XXX case.cmd.env == case.fresh @ env *)
                    let i_1j = Index.push i_1 j in
                    let gj, bj (* bold j *), env_bj = graph_cmd find_def ~process i_1j case.cmd in
                    { id= Ident.local "repeat_in"
                    ; source = i_1
                    ; source_env = env
                    ; pre = List.map fact_of_typed case.facts
                    ; update = update_unit
                    ; tag = []
                    ; post = []
                    ; target = i_1j
                    ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                    }
                    :: { id= Ident.local "repeat_out"
                       ; source = bj
                       ; source_env = env_bj
                       ; pre = []
                       ; update = { update_unit with drops= case.fresh }
                       ; tag =
                           [ fact case.cmd.env
                             @@ Loop { mode = Back; process; index = Index.to_string i }
                           ]
                       ; post = []
                       ; target = i_1
                       ; target_env = env
                       }
                    :: gj)
                 cases))
        @ List.concat
            (List.mapi
               (fun j (case : case) ->
                  (* XXX case.cmd.env == case.fresh @ env *)
                  let i_1jn = Index.push i_1 (j + n) in
                  let gj, bj (* bold j *), env_bj = graph_cmd find_def ~process i_1jn case.cmd in
                  { id= Ident.local "until_in"
                  ; source = i_1
                  ; source_env = env
                  ; pre = List.map fact_of_typed case.facts
                  ; update = update_unit
                  ; tag = []
                  ; post = []
                  ; target = i_1jn
                  ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                  }
                  :: { id= Ident.local "until_out"
                     ; source = bj
                     ; source_env = env_bj
                     ; pre = []
                     ; update = { update_id with drops= case.fresh }
                     ; tag =
                         [ fact case.cmd.env
                           @@ Loop { mode = Out; process; index = Index.to_string i }
                         ]
                     ; post = []
                     ; target = i_2
                     ; target_env = env
                     }
                  :: gj)
               cases')
      in
      es, i_2, env

and graph_application find_def ~process i (app : expr) : graph * Index.t * Env.t =
  match app.desc with
  | Apply (f, es) ->
      (match Env.find_opt_by_id app.env f with
       | Some (ExtFun _) ->
           (* ExtFun has no definition *)
           [], i, app.env
       | Some (ExtSyscall _ | Function _) ->
           let args, cmd = find_def f in
           let i_1 = Index.add i 1 in
           let g, j, env_j = graph_cmd find_def ~process i_1 cmd in
           let j_1 = Index.add j 1 in
           { id= Ident.local "app_in"
           ; source = i
           ; source_env = app.env
           ; pre = []
           ; update = { register = Some { env= app.env; loc = Location.nowhere; desc = Unit }
                      ; mutable_overrides = List.combine args (List.map Option.some es)
                      ; drops= []
                      }
           ; tag = []
           ; post = []
           ; target = i_1
           ; target_env = cmd.env
           }
           ::
           { id= Ident.local "app_out"
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = { register = None; mutable_overrides = []; drops= args }
           ; tag = []
           ; post = []
           ; target = j_1
           ; target_env = app.env
           }
           :: g, j_1, app.env
       | None | Some _ -> assert false)
  | _ -> assert false
;;

let check_edges es =
  let vs = Index.Map.empty in
  List.fold_left (fun vs (e : edge) ->
      Format.eprintf "Check edge %t@." (Ident.print e.id);
      check_edge_invariants e;
      let check is_source vs v env =
        match Index.Map.find_opt v vs with
        | None ->
            Index.Map.add v (e.id, is_source, env) vs
        | Some (id', is_source', env') ->
            if not (env = env') then (
              Format.eprintf "Error %b %t with %b %t@."
                is_source (Ident.print e.id)
                is_source' (Ident.print id');
              assert false);
            vs
      in
      let vs = check true vs e.source e.source_env in
      let vs = check false vs e.target e.target_env in
      vs) vs es

let graph_files_and_vars
  ~loc
  env
  (decls : Typed.decl list)
  (proc : Typed.Subst.instantiated_process)
  (i : Index.t) =
  let fact fact' : fact = { env; desc=fact'; loc } in
  let files : fact list =
    List.concat_map (fun (path, fty, contents) ->
        let f = fact @@ File { path; contents } in
        let fs : fact list =
          List.concat_map (fun (decl : Typed.decl) ->
              match decl.desc with
              | Allow { process_typ; target_typs; syscalls= Some syscalls } ->
                  if process_typ = proc.typ && List.mem fty target_typs then
                    List.map (fun syscall ->
                        fact (Access { pid= proc.id; target= path; syscall= Some syscall })) syscalls
                  else
                    []
              | Allow { process_typ; target_typs; syscalls= None } ->
                  if process_typ = proc.typ && List.mem fty target_typs then
                    [ fact (Access { pid= proc.id; target= path; syscall= None }) ]
                  else
                    []
              | _ -> []) decls
        in
        f :: fs) proc.files
  in
  let i_1 = Index.add i 1 in
  [{ id= Ident.local "init_process"
  ; source = i
  ; source_env = env
  ; pre = []
  ; update = { register = Some { env; loc = Location.nowhere; desc = Unit }
             ; mutable_overrides = List.map (fun (id,e) -> id, Some e) proc.vars
             ; drops = []
             }
  ; tag = []
  ; post = files
  ; target = i_1
  ; target_env = proc.main.env
  }],
  i_1

let graph_process ~loc env decls syscalls (proc : Subst.instantiated_process) =
  let funcs = List.map (fun (f, args, cmd) -> f, (args, cmd)) proc.Subst.funcs in
  let find_def n = List.assoc n (syscalls @ funcs) in
  let g, i = graph_files_and_vars ~loc env decls proc Index.zero in
  let g', _j, _env = graph_cmd find_def ~process:proc.id i proc.main in
  let g = g @ g' in
  ignore (check_edges g);
  Format.eprintf "%t: %d edges@." (Ident.print proc.id) (List.length g);
  List.iter (fun e ->
      Format.eprintf "  %t@." (Ident.print e.id)
    ) g;
  g

type rule =
  { name : string
  ; role : string
  ; pre : fact list
  ; label : fact list
  ; post : fact list
  }

let const_rules decls =
  List.filter_map (fun (decl : Typed.decl) ->
      let fact desc = { env= decl.env; loc=Location.nowhere; desc } in
      match decl.desc with
      | Init { id; desc } ->
          (match desc with
          | Value e -> (* [const n = e] *)
              let name = Printf.sprintf "Const_%s" (Ident.to_string id) in
              Some { name
              ; role = ""
              ; pre = []
              ; label = [ fact @@ Constant (id, None, e) ]
              ; post = [ fact @@ Constant (id, None, e) ]
              }
          | Value_with_param (p, e) -> (* [const n<p> = e] *)
              let name = Printf.sprintf "Const_%s" (Ident.to_string id) in
              Some { name
                   ; role = ""
                   ; pre = []
                   ; label = [ fact @@ Constant (id, Some p, e) ]
                   ; post = [ fact @@ Constant (id, Some p, e) ]
                   }
          | Fresh -> (* [const fresh n] *)
              let name = Printf.sprintf "Const_%s" (Ident.to_string id) in
              Some { name
              ; role = ""
              ; pre = [ fact @@ Fresh id ]
              ; label = [ fact @@ Init name ]
(*
                   [ InitFact [ String ("Const" ^ sep ^ v) ]
                   ; InitFact [ List [ String ("Const" ^ sep ^ v); Var v ] ]
                   ; mk_constant_fact v
                   ]
*)
              ; post = [ fact @@ Constant (id, None, evar decl.env id) ]
              }
          | Fresh_with_param -> (* [const fresh n<>] *)
              let name = Printf.sprintf "Const_%s" (Ident.to_string id) in
              Some { name
              ; role = ""
              ; pre = [ fact @@ Fresh id ]
              ; label = [ fact @@ Init name ]
              ; post = [ fact @@ Constant (id, None, evar decl.env id) ]
              }
          )
      | _ -> None) decls


let _ppp
    decls
    env
    (chan_args : Typed.chan_arg list)
    (p : Typed.Subst.instantiated_process) =
  let fact desc = { env; loc=Location.nowhere; desc } in
  List.map (fun { channel; parameter; typ } ->
      ( parameter = Some None
      , List.concat_map (fun decl ->
            match decl.desc with
            | Allow { process_typ; target_typs; syscalls } ->
                if p.typ = process_typ && List.mem typ target_typs then
                  let syscalls =
                    match syscalls with
                    | None -> [None]
                    | Some syscalls -> List.map Option.some syscalls
                  in
                  List.map (fun syscall ->
                      fact @@ AccessX { pid= p.id; target= channel; parameter; syscall })
                    syscalls
                else []
            | _ -> []) decls )) chan_args


let graphs_system (decls : decl list) (sys : decl) =
  let syscalls =
    List.filter_map (fun decl ->
        match decl.desc with
        | Syscall { id; fun_sig; cmd } ->
          let args = syscall_member_fun_desc_to_ident_list fun_sig in  
          Some (id, (args, cmd))
        | _ -> None) decls
  in
  match sys.desc with
  | System (procs, _lemmas) ->
      let procs = List.concat_map (Subst.instantiate_proc decls) procs in
      let rev_gs =
        List.fold_left (fun rev_gs proc ->
            let g = graph_process ~loc:sys.loc sys.env decls syscalls proc in
            ((proc.id, g) :: rev_gs)) [] procs
      in
      List.rev rev_gs
  | _ -> assert false

(* access control

  let t = add_comment t "Access control:" in
  let facts_gv_list : (bool * fact list * fact list) list =
    List.fold_left
      (fun facts_gv_list p ->
         let namespace =
           String.capitalize_ascii
             (p.Context.proc_name
              ^ if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)
         in
         let new_pol =
           pol.Context.pol_access
           @ List.map (fun (a, b) -> a, b, "") pol.Context.pol_access_all
         in
         let facts_gv_list' =
           List.fold_left
             (fun facts_gv_list c ->
                (* List.fold_left  *)
                (match c with
                 | Syntax.ChanArg { id = cname; typ = cty; param = None } ->
                     ( false
                     , List.map
                         (fun (_, _, scall) ->
                            AccessFact
                              (namespace, String !fresh_string, String cname, scall))
                         (List.filter
                            (fun (pty, tyl, _scall) ->
                               pty = p.Context.proc_type
                               && List.exists (fun v -> v = cty) tyl)
                            new_pol)
                     , [] )
                 | Syntax.ChanArg { id = cname; typ = cty; param = Some None } ->
                     ( true
                     , List.map
                         (fun (_, _, scall) ->
                            AccessFact
                              ( namespace
                              , String !fresh_string
                              , List [ String cname; Var !fresh_ident ]
                              , scall ))
                         (List.filter
                            (fun (pty, tyl, _scall) ->
                               pty = p.Context.proc_type
                               && List.exists (fun v -> v = cty) tyl)
                            new_pol)
                     , [] )
                 | Syntax.ChanArg { id = cname; typ = cty; param = Some (Some e) } ->
                     let e, gv', _ = translate_expr2 e in
                     ( false
                     , List.map
                         (fun (_, _, scall) ->
                            AccessFact
                              ( namespace
                              , String !fresh_string
                              , List [ String cname; e ]
                              , scall ))
                         (List.filter
                            (fun (pty, tyl, _scall) ->
                               pty = p.Context.proc_type
                               && List.exists (fun v -> v = cty) tyl)
                            new_pol)
                     , gv' ))
                :: facts_gv_list)
             []
             p.Context.proc_channels
         in
         facts_gv_list @ facts_gv_list')
      []
      (List.rev proc)
  in
*)



(*
  (* process signature *)
  let t =
    List.fold_left
      (fun t (f, arity) -> add_fun t (f, arity))
      t
      (List.rev ctx.Context.ctx_ext_func)
  in


  let t =
    List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const)
  in


  let t =
    List.fold_left
      (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2))
      t
      (List.rev def.Context.def_ext_eq)
  in


  let mos =
    List.map (fun p ->
        translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol) proc
  in


  let t =
    add_rule
      t
      { name = "Init" ^ !separator ^ "system"
      ; role = "system"
      ; pre = []
      ; label = [ InitFact [ String "system" ] ]
      ; post =
          (* initializing tokens..  *)
          List.map
            (fun m ->
               let st = m.model_init_state in
               if !Config.tag_transition
               then
                 mk_state_fact
                   ~param:!fresh_string
                   st
                   empty_state_desc
                   (Some (mk_transition_expr `Initial))
               else mk_state_fact ~param:!fresh_string st empty_state_desc None)
            mos
          @ [ AccessGenFact ("system" ^ !separator, String !fresh_string) ]
      }
  in
  let t, _ =
    List.fold_left
      (fun (t, n) (b, (facts : fact list), gv) ->
         List.fold_left
           (fun (t, n) (fact : fact) ->
              ( add_rule
                  t
                  { name =
                      "Init"
                      ^ !separator
                      ^ "system"
                      ^ !separator
                      ^ "ACP"
                      ^ !separator
                      ^ string_of_int n
                  ; role = "system"
                  ; pre =
                      gv @ [ AccessGenFact ("system" ^ !separator, String !fresh_string) ]
                  ; label =
                      [ (if b
                         then
                           InitFact
                             [ List
                                 [ String
                                     ("system"
                                      ^ !separator
                                      ^ "ACP"
                                      ^ !separator
                                      ^ string_of_int n)
                                 ; Var !fresh_ident
                                 ]
                             ]
                         else
                           InitFact
                             [ String
                                 ("system"
                                  ^ !separator
                                  ^ "ACP"
                                  ^ !separator
                                  ^ string_of_int n)
                             ])
                      ]
                  ; post = [ fact ]
                  }
              , n + 1 ))
           (t, n)
           facts)
      (t, 0)
      facts_gv_list
  in
  let t = List.fold_left add_model t mos in
  let t, _ =
    List.fold_left
      (fun (t, n) pl ->
         let mos =
           List.fold_left
             (fun mos p ->
                translate_process
                  p
                  def.Context.def_ext_syscall
                  def.Context.def_ext_attack
                  pol
                :: mos)
             []
             (List.rev pl)
         in
         let facts_gv_list =
           List.fold_left
             (fun facts_gv_list p ->
                let namespace =
                  String.capitalize_ascii
                    (p.Context.proc_name
                     ^
                     if p.Context.proc_pid = 0
                     then ""
                     else string_of_int p.Context.proc_pid)
                in
                (* print_string namespace; *)
                let new_pol =
                  pol.Context.pol_access
                  @ List.map (fun (a, b) -> a, b, "") pol.Context.pol_access_all
                in
                let facts_gv_list' =
                  List.fold_left
                    (fun facts_gv_list c ->
                       (match c with
                        | Syntax.ChanArg { id = cname; typ = cty; param = None } ->
                            ( false
                            , List.map
                                (fun (_, _, scall) ->
                                   AccessFact (namespace, Param, String cname, scall))
                                (List.filter
                                   (fun (pty, tyl, _scall) ->
                                      pty = p.Context.proc_type
                                      && List.exists (fun v -> v = cty) tyl)
                                   new_pol)
                            , [] )
                        | Syntax.ChanArg { id = cname; typ = cty; param = Some None } ->
                            ( true
                            , List.map
                                (fun (_, _, scall) ->
                                   AccessFact
                                     ( namespace
                                     , Param
                                     , List [ String cname; Var !fresh_ident ]
                                     , scall ))
                                (List.filter
                                   (fun (pty, tyl, _scall) ->
                                      pty = p.Context.proc_type
                                      && List.exists (fun v -> v = cty) tyl)
                                   new_pol)
                            , [] )
                        | Syntax.ChanArg { id = cname; typ = cty; param = Some (Some e) }
                          ->
                            let e, gv', _ = translate_expr2 e in
                            ( false
                            , List.map
                                (fun (_, _, scall) ->
                                   AccessFact
                                     (namespace, Param, List [ String cname; e ], scall))
                                (List.filter
                                   (fun (pty, tyl, _scall) ->
                                      pty = p.Context.proc_type
                                      && List.exists (fun v -> v = cty) tyl)
                                   new_pol)
                            , gv' ))
                       :: facts_gv_list)
                    []
                    p.Context.proc_channels
                in
                facts_gv_list @ facts_gv_list')
             []
             (List.rev pl)
         in
         let t =
           add_rule
             t
             { name = "Init" ^ !separator ^ "system" ^ string_of_int n
             ; role = "system" ^ string_of_int n
             ; pre =
                 [ FreshFact' Param ]
                 (* XXX This produce the same compilation but not sure it is semantically correct *)
             ; label =
                 [ InitFact [ List [ String ("system" ^ string_of_int n); Param ] ] ]
             ; post =
                 [ AccessGenFact ("system" ^ string_of_int n ^ !separator, Param) ]
                 @ List.map
                     (fun m ->
                        let st = m.model_init_state in
                        if !Config.tag_transition
                        then
                          mk_state_fact
                            st
                            empty_state_desc
                            (Some (mk_transition_expr `Initial))
                        else mk_state_fact st empty_state_desc None)
                     mos
             }
         in
         let t, _ =
           List.fold_left
             (fun (t, m) (b, facts, gv) ->
                List.fold_left
                  (fun (t, m) (fact : fact) ->
                     ( add_rule
                         t
                         { name =
                             "Init"
                             ^ !separator
                             ^ "system"
                             ^ string_of_int n
                             ^ !separator
                             ^ "ACP"
                             ^ !separator
                             ^ string_of_int m
                         ; role = "system" ^ string_of_int n
                         ; pre =
                             gv
                             @ [ AccessGenFact
                                   ("system" ^ string_of_int n ^ !separator, Param)
                               ]
                         ; label =
                             [ (if b
                                then
                                  InitFact
                                    [ List
                                        [ String
                                            ("system"
                                             ^ string_of_int n
                                             ^ !separator
                                             ^ "ACP"
                                             ^ !separator
                                             ^ string_of_int m)
                                        ; Param
                                        ; Var !fresh_ident
                                        ]
                                    ]
                                else
                                  InitFact
                                    [ List
                                        [ String
                                            ("system"
                                             ^ string_of_int n
                                             ^ !separator
                                             ^ "ACP"
                                             ^ !separator
                                             ^ string_of_int m)
                                        ; Param
                                        ]
                                    ])
                             ]
                         ; post = [ fact ]
                         }
                     , m + 1 ))
                  (t, m)
                  facts)
             (t, 0)
             facts_gv_list
         in
         let t = List.fold_left (fun t m -> add_model t m) t mos in
         t, n + 1)
      (t, 1)
      (List.rev param_proc)
  in
  (* translating lemmas now *)
  let t =
    List.fold_left
      (fun t l ->
         let l =
           match l.Location.data with
           | Syntax.PlainLemma { name=l; desc= p } -> PlainLemma (l, p)
           | Syntax.ReachabilityLemma { name= l; facts= fs; _ } ->
               let fs, gv, _, _ = translate_facts "" fs in
               ReachabilityLemma (l, gv, fs)
           | Syntax.CorrespondenceLemma {name= l; fresh_variables= vl; premise= a; conclusion= b } ->
               let a, gva =
                 match translate_facts "" [ a ] with
                 | [ a ], gva, _, _ -> a, gva
                 | _ -> assert false
               in
               let b, gvb =
                 match translate_facts "" [ b ] with
                 | [ b ], gvb, _, _ -> b, gvb
                 | _ -> assert false
               in
               CorrespondenceLemma (l, vl, (gva, a), (gvb, b))
           (* | Syntax.CorrespondenceLemma (l, vars, e1, e2) ->
        CorrespondenceLemma (l, vars,
            (match e1.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)),
            (match e2.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)))
           *)
         in
         add_lemma t l)
      t
      lem
  in
  t
;;
*)
