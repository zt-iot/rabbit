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
    String.concat "__" @@ List.map (fun (a, b) -> Printf.sprintf "%d.%d" a b) i
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
  }

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
    }
  in
  let update_id = { register = None; mutable_overrides = [] } in
  let fact env desc : fact = { env; desc; loc = Location.nowhere } in
  match c.desc with
  | Skip ->
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "skip"
          ; source = i (* transition_from *)
          ; source_env = env
          ; pre = [] (* transition_pre *)
          ; update = update_unit (* transitino_state_transition *)
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
           ; update = update_id
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
          ; update = { register = Some e; mutable_overrides = [] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | New (x, eopt, c) ->
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd find_def ~process i_1 c in
      let j_1 = Index.add j 1 in
      ( { id = Ident.local "new_fresh"
        ; source = i
        ; source_env = env
        ; pre = [ fact c.env @@ Fresh x ]
        ; update = update_unit
        ; tag = []
        ; post = []
        ; target = i_1
        ; target_env = c.env
        }
        :: { id = Ident.local "new_structure"
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = update_id
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
        :: g
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
      ( { id = Ident.local "get_structure"
        ; source = i
        ; source_env = env
        ; pre = pre_and_post
        ; update = update_unit
        ; tag = []
        ; post = pre_and_post
        ; target = i_1
        ; target_env = c.env
        }
        :: { id = Ident.local "get_close"
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = update_id
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
                   ; update = update_id
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
        ({ id= Ident.local "loop_init"
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
                    { id= Ident.local "loop_case_in"
                    ; source = i_1
                    ; source_env = env
                    ; pre = List.map fact_of_typed case.facts
                    ; update = update_unit
                    ; tag = []
                    ; post = []
                    ; target = i_1j
                    ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                    }
                    :: { id= Ident.local "loop_case_out"
                       ; source = bj
                       ; source_env = env_bj
                       ; pre = []
                       ; update = update_unit
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
                  { id= Ident.local "loop_until_in"
                  ; source = i_1
                  ; source_env = env
                  ; pre = List.map fact_of_typed case.facts
                  ; update = update_unit
                  ; tag = []
                  ; post = []
                  ; target = i_1jn
                  ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                  }
                  :: { id= Ident.local "loop_until_out"
                     ; source = bj
                     ; source_env = env_bj
                     ; pre = []
                     ; update = update_id
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
           ; update = { register = None; mutable_overrides = [] }
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

let graph_consts decls =
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


let graph_system (decls : decl list) (sys : decl) =
  let syscalls =
    List.filter_map (fun decl ->
        match decl.desc with
        | Syscall { id; args; cmd } -> Some (id, (args, cmd))
        | _ -> None) decls
  in
  match sys.desc with
  | System (procs, _lemmas) ->
      let procs = List.concat_map (Subst.instantiate_proc decls) procs in
      let rev_gs =
        List.fold_left (fun rev_gs proc ->
            let g = graph_process ~loc:sys.loc sys.env decls syscalls proc in
            (g :: rev_gs)) [] procs
      in
      List.rev rev_gs
  | _ -> assert false
