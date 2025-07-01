(* The semantics *)
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

(* Typed.fact' + internal facts *)
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
let rec graph_cmd ~process:(process : Typed.Subst.instantiated_process) find_def decls i (c : cmd) : graph * Index.t * Env.t =
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
      (* i =skip=> i+1 *)
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
      (* i =c1=> j =c2=> k *)
      let g1, j, _ = graph_cmd ~process find_def decls i c1 in
      let g2, k, env_k = graph_cmd ~process find_def decls j c2 in
      g1 @ g2, k, env_k
  | Put fs ->
      (* i =put=> i+1 *)
      (* XXX requires access policy check *)
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
  | Let (x, ({ desc= Apply _; _ } as app), c) ->
      (* var x := f(e) in c *)
      (* i =f(e)=> j =let_def=> j+1 =c=> k =let_exit=> k+1 *)
      let g, j, env_j = graph_application ~process find_def decls i app in
      let j_1 = Index.add j 1 in
      let g', k, env_k = graph_cmd ~process find_def decls j_1 c in
      let k_1 = Index.add k 1 in
      ( { id = Ident.local ("let_def_" ^ fst x)
        ; source = j
        ; source_env = env_j
        ; pre = []
        ; update = { update_unit with mutable_overrides = [ x, None (* \rho *) ] }
        ; tag = []
        ; post = []
        ; target = j_1
        ; target_env = c.env
        }
        :: { id = Ident.local ("let_exit_" ^ fst x)
           ; source = k
           ; source_env = env_k
           ; pre = []
           ; update = { update_id with drops= [x] }
           ; tag = []
           ; post = []
           ; target = k_1
           ; target_env = env
           }
        :: g @ g'
      , k_1, env )
  | Let (x, e, c) ->
      (* var x := e in c *)
      (* i =let_def=> i+1 =c=> j =let_exit=> j+1 *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd ~process find_def decls i_1 c in
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
      (* i =f(e)=> j =assign_call=> j+1 *)
      (* x := f(e) *)
      let g, j, env_j = graph_application ~process find_def decls i app in
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
      (* i =f(e)=> j =call=> j+1 *)
      (* _ := f(e) *)
      let g, j, env_j = graph_application ~process find_def decls i app in
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
      (* i =assign=> i+1 *)
      (* x := e *)
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
      (* XXX e is lost... Should be rejected *)
      (* i =ignore=> i+1 *)
      (* _ := e *)
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
      (* i =event=> i+1 *)
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
      (* i =return=> i+1 *)
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
  | New (x, eopt, c) ->
      (* i =new_intro=> i+1 =c=> j =new_out=> j+1 *)
      (* new x in c *)
      (* new x = e in c *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd ~process find_def decls i_1 c in
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
                           { name = s; process=process.id; address = evar c.env x; args = es }
                    ])
           ; target = j_1
           ; target_env = env
           }
        :: g (* XXX No drop of x? *)
      , j_1, env )
  | Get (xs, e, s, c) ->
      (* i =get_intro=> i+1 =c=> j =get_out=> j+1 *)
      (* [let x1,..,xn := e.S in c] *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd ~process find_def decls i_1 c in
      let j_1 = Index.add j 1 in
      let pre_and_post : fact list =
        [ fact env
          @@ Structure { name = s; process= process.id; address = e; args = List.map (evar c.env) xs }
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
      (* i =del=> i+1 *)
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
          ; pre = [ fact env @@ Structure { name = s; process= process.id; address = e; args = xs } ]
          ; update = update_unit
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1, env )
  | Case cases ->
      (* i { =case_in=> i:j =case.cmd=> bj =case_out=> }_j i+1 *)
      let i_1 = Index.add i 1 in
      let es =
        List.concat
        @@ List.mapi
             (fun j (case : case) ->
                (* XXX case.cmd.env == case.fresh @ env *)
                let ij = Index.push i j in
                let gj, bj (* bold j *), env_bj = graph_cmd ~process find_def decls ij case.cmd in
                (* XXX requires access policy check *)
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
      (* i =repeat_in=> i+1 { =case_in=> i+1:j =c=> bj => }_j i+1 (* loops back *)
                            { =until_in=> i+1:(j+n) =c=> bj => }_j i+2 (* exit *)
      *)
      let i_1 = Index.add i 1 in
      let i_2 = Index.add i 2 in
      let n = List.length cases in
      let es =
        ({ id= Ident.local "repeat_in"
         ; source = i
         ; source_env = env
         ; pre = []
         ; update = update_unit
         ; tag = [ fact env @@ Loop { mode = In; process= process.id; index = Index.to_string i } ]
         ; post = []
         ; target = i_1
         ; target_env = env
         }
         :: List.concat
              (List.mapi
                 (fun j (case : case) ->
                    (* XXX case.cmd.env == case.fresh @ env *)
                    let i_1j = Index.push i_1 j in
                    let gj, bj (* bold j *), env_bj = graph_cmd ~process find_def decls i_1j case.cmd in
                    (* XXX requires access policy check *)
                    { id= Ident.local "case_in"
                    ; source = i_1
                    ; source_env = env
                    ; pre = List.map fact_of_typed case.facts
                    ; update = update_unit
                    ; tag = []
                    ; post = []
                    ; target = i_1j
                    ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                    }
                    :: { id= Ident.local "case_out"
                       ; source = bj
                       ; source_env = env_bj
                       ; pre = []
                       ; update = { update_unit with drops= case.fresh }
                       ; tag =
                           [ fact case.cmd.env
                             @@ Loop { mode = Back; process= process.id; index = Index.to_string i }
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
                  let gj, bj (* bold j *), env_bj = graph_cmd ~process find_def decls i_1jn case.cmd in
                  (* XXX requires access policy check *)
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
                           @@ Loop { mode = Out; process= process.id; index = Index.to_string i }
                         ]
                     ; post = []
                     ; target = i_2
                     ; target_env = env
                     }
                  :: gj)
               cases')
      in
      es, i_2, env

and graph_application ~process find_def (decls : decl list) i (app : expr) : graph * Index.t * Env.t =
  match app.desc with
  | Apply (f, es) ->
      (match Env.find_opt_by_id app.env f with
       | Some (ExtFun _) ->
           (* i =extfun=> i+1 *)
           (* ExtFun has no definition *)
           let i_1 = Index.add i 1 in
           ( [ { id = Ident.local "extfun"
               ; source = i
               ; source_env = app.env
               ; pre = []
               ; update = { register = Some app; mutable_overrides = []; drops= [] }
               ; tag = []
               ; post = []
               ; target = i_1
               ; target_env = app.env
               }
             ]
           , i_1, app.env)

       | Some (ExtSyscall _ | Function _ as desc) ->
           (* System calls can be attacked, therefore branching is possible *)
           let i_1 = Index.add i 1 in (* the point of the confluence *)
           let g_attacks =
             match desc with
             | ExtSyscall _ ->
                 (* Inefficiency: all the decls are scanned for each system call *)
                 let attacks =
                   let possible_attacks = List.concat_map (fun d ->
                       match d.desc with
                       | AllowAttack { process_typs; attacks } ->
                           if List.mem process.typ process_typs then attacks
                           else []
                       | _ -> []) decls
                   in
                   List.filter_map (fun d ->
                       match d.desc with
                       | Attack { id; syscall; args; cmd } when List.mem id possible_attacks && syscall = f ->
                           Some (id, args, cmd)
                       | _ -> None) decls
                 in
                 let attacks = List.mapi (fun i a -> (i+1), a) attacks in
                 List.fold_left (fun g (k, (attack_id, args, cmd)) ->
                     (* i => ik => ... => j => i_1 *)
                     let ik = Index.push i k in
                     (* XXX dupe: same as the normal applications *)
                     let g', j, env_j = graph_cmd ~process find_def decls ik cmd in
                     (* XXX should check env_j = app.env *)
                     { id= Ident.local ((Ident.to_string attack_id) ^ "_attack_in")
                     ; source = i
                     ; source_env = app.env
                     ; pre = []
                     ; update = { register = Some { env= app.env; loc = Location.nowhere; desc = Unit }
                                ; mutable_overrides = List.combine args (List.map Option.some es)
                                ; drops= []
                                }
                     ; tag = []
                     ; post = []
                     ; target = ik
                     ; target_env = cmd.env
                     }
                     ::
                     { id= Ident.local ((Ident.to_string attack_id) ^ "_attack_out")
                     ; source = j
                     ; source_env = env_j
                     ; pre = []
                     ; update = { register = None; mutable_overrides = []; drops= args }
                     ; tag = []
                     ; post = []
                     ; target = i_1
                     ; target_env = app.env
                     }
                     :: g' @ g)
                   [] attacks
             | Function _ -> []
             | _ -> assert false
           in

           let args, cmd = find_def f in
           (* i => i0 => ... => j => i_1 *)
           let i0 = Index.push i 0 in
           let g, j, env_j = graph_cmd ~process find_def decls i0 cmd in
           { id= Ident.local (Ident.to_string f ^ "_app_in")
           ; source = i
           ; source_env = app.env
           ; pre = []
           ; update = { register = Some { env= app.env; loc = Location.nowhere; desc = Unit }
                      ; mutable_overrides = List.combine args (List.map Option.some es)
                      ; drops= []
                      }
           ; tag = []
           ; post = []
           ; target = i0
           ; target_env = cmd.env
           }
           ::
           { id= Ident.local (Ident.to_string f ^ "app_out")
           ; source = j
           ; source_env = env_j
           ; pre = []
           ; update = { register = None; mutable_overrides = []; drops= args }
           ; tag = []
           ; post = []
           ; target = i_1
           ; target_env = app.env
           }
           :: g_attacks @ g, i_1, app.env
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

type model =
  { id : Ident.t
  ; edges : edge list
  }

let model_process ~loc env decls syscalls (proc : Subst.instantiated_process) =
  let funcs = List.map (fun (f, args, cmd) -> f, (args, cmd)) proc.Subst.funcs in
  let find_def n = List.assoc n (syscalls @ funcs) in
  let g, i = graph_files_and_vars ~loc env decls proc Index.zero in
  let g', _j, _env = graph_cmd ~process:proc find_def decls i proc.main in
  let g = g @ g' in
  ignore (check_edges g);
  Format.eprintf "%t: %d edges@." (Ident.print proc.id) (List.length g);
  List.iter (fun (e : edge) ->
      Format.eprintf "  %t@." (Ident.print e.id)
    ) g;
  { id= proc.id; edges= g }

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


let models_system (decls : decl list) (sys : decl) : model list =
  let syscalls =
    List.filter_map (fun decl ->
        match decl.desc with
        | Syscall { id; args; cmd } -> Some (id, (args, cmd))
        | _ -> None) decls
  in
  match sys.desc with
  | System (procs, _lemmas) ->
      let procs = List.concat_map (Subst.instantiate_proc decls) procs in
      let rev_ms =
        List.fold_left (fun rev_ms proc ->
            let m = model_process ~loc:sys.loc sys.env decls syscalls proc in
            (m :: rev_ms)) [] procs
      in
      List.rev rev_ms
  | _ -> assert false

let lemmas_system (sys : decl) =
  match sys.desc with
  | System (_procs, lemmas) -> lemmas
  | _ -> assert false

type signature =
  { functions : (Ident.t * int) list
  ; equations : (Typed.expr * Typed.expr) list
  }

let functions_of_decls (decls : decl list) =
  List.filter_map (fun d ->
      match d.desc with
      | Function { id; arity } -> Some (id,arity)
      | _ -> None) decls

let equations_of_decls (decls : decl list) =
  List.filter_map (fun d ->
      match d.desc with
      | Equation (e1, e2) -> Some (e1, e2)
      | _ -> None) decls

let signature_of_decls (decls : decl list) =
  { functions = functions_of_decls decls
  ; equations = equations_of_decls decls
  }

type tamarin =
  { signature : signature
  ; models : model list
  ; constants : (ident * Typed.init_desc) list
  ; lemmas : (Ident.t * lemma) list
  }

(*
let rec translate_expr (e : Typed.expr) : Tamarin2.expr * (Ident.t * Tamarin2.expr option) list =
  match e.desc with
  | Ident { id; desc= Var _; param= None } -> Ident id, []
  | Ident { id; desc= Const false; param= None } -> Ident id, [ (id, None) ]
  | Ident { id; desc= Const true; param= Some e } ->
      let e, cs = translate_expr e in
      Ident id, (id, Some e) :: cs
  | Ident { id; desc= ExtConst; param= None } -> Apply (id, []), []
  | Ident { id; desc= Channel (false, _cty); param= None } ->
      String (Ident.to_string id), []
  | Ident { id; desc= Channel (true, _cty); param= Some e } ->
      let e, cs = translate_expr e in
      List [String (Ident.to_string id); e], cs
  | String s -> String s, []
  | Integer i -> Integer i, []
  | Boolean _b -> assert false
  | Float _f -> assert false
  | Apply (f, es) ->
      let rev_es, cs =
        List.fold_left (fun (rev_es, cs) e ->
            let e, cs' = translate_expr e  in
            e :: rev_es, cs @ cs') ([], []) es
      in
      Apply (f, List.rev rev_es), cs
  | Tuple es ->
      let rev_es, cs =
        List.fold_left (fun (rev_es, cs) e ->
            let e, cs' = translate_expr e  in
            e :: rev_es, cs @ cs') ([], []) es
      in
      List (List.rev rev_es), cs
  | _ -> assert false
*)

let get_constants (decls : decl list) : (Typed.ident * Typed.init_desc) list =
  List.filter_map (fun (d : decl) ->
      match d.desc with
      | Init { id; desc } -> Some (id, desc)
      | _ -> None) decls

(*
let add_model_inits n_opt t models =
  let pre =
    match n_opt with
    | None -> []
    | Some _ -> [ FreshFact' Param ]
  in
  let label =
    match n_opt with
    | None -> [ InitFact [ String (system n_opt) ] ]
    | Some _ -> [ InitFact [ List [ String (system n_opt); Param ] ] ]
  in
  let param_string =
    match n_opt with
    | None -> Some !fresh_string (* rab *)
    | Some _ -> None
  in
    let t = add_comment t ("Add model inits: "
                         ^ String.concat "," (List.map (fun m -> m.model_name) models))
  in
  add_rule
    t
    { name = !!["Init" ; system n_opt] (* Init_systemn *)
    ; role = system n_opt
    ; pre
    ; label
    ; post =
        AccessGenFact (!![system n_opt; ""] (* systemn_ *)
                      , param_expr n_opt)
        :: List.map
          (fun m ->
             let st = m.model_init_state in
             if !Config.tag_transition
             then
               mk_state_fact
                 ?param:param_string
                 st
                 empty_state_desc
                 (Some (mk_transition_expr `Initial))
             else mk_state_fact ~param:!fresh_string st empty_state_desc None)
          models
    }
*)


let tamarin_of_decls (decls : decl list) =
  (* functions *)
  (* equations *)
  (* constants *)
  (* for each process:
     - model inits
     - access control
     - model
  *)
  let sys =
    match
      List.filter (fun d ->
          match d.desc with
          | System _ -> true
          | _ -> false) decls
    with
    | [sys] -> sys
    | [] -> assert false
    | _ -> assert false
  in
  let signature = signature_of_decls decls in
  let models = models_system decls sys in
  let constants = get_constants decls in
  let lemmas = lemmas_system sys in
  { signature; models; constants; lemmas }

(*
let translate_sys
    { Context.sys_ctx = ctx
    ; Context.sys_def = def
    ; Context.sys_pol = pol
    ; Context.sys_proc = proc
    ; Context.sys_param_proc = param_proc
    ; Context.sys_lemma = lem
    }
    (used_idents, used_string)
  =
  (* global constants *)
  let t = translate_global_constants ~sep t def in

  let param_expr n_opt =
    match n_opt with
    | None -> String !fresh_string (* rab *)
    | Some _ -> Param (* param *)
  in

  let system n_opt =
    match n_opt with
    | None -> "system"
    | Some n -> "system" ^ string_of_int n
  in

  let add_model_inits n_opt t models =
    let pre =
      match n_opt with
      | None -> []
      | Some _ -> [ FreshFact' Param ]
    in
    let label =
      match n_opt with
      | None -> [ InitFact [ String (system n_opt) ] ]
      | Some _ -> [ InitFact [ List [ String (system n_opt); Param ] ] ]
    in
    let param_string =
      match n_opt with
      | None -> Some !fresh_string (* rab *)
      | Some _ -> None
    in
    let t = add_comment t ("Add model inits: "
                           ^ String.concat "," (List.map (fun m -> m.model_name) models))
    in
    add_rule
      t
      { name = !!["Init" ; system n_opt] (* Init_systemn *)
      ; role = system n_opt
      ; pre
      ; label
      ; post =
          AccessGenFact (!![system n_opt; ""] (* systemn_ *)
                        , param_expr n_opt)
          :: List.map
            (fun m ->
               let st = m.model_init_state in
               if !Config.tag_transition
               then
                 mk_state_fact
                   ?param:param_string
v                   st
                   empty_state_desc
                   (Some (mk_transition_expr `Initial))
               else mk_state_fact ~param:!fresh_string st empty_state_desc None)
            models
      }
  in

  let get_access_control proc param :
    ((string (* namespace *) * Name.ident (* channel *))
     * (bool (* parameter *)
        * fact list (* facts *)
        * fact list (* global vars *))) list =

    let pol' =
      List.map (fun (i, is, i') -> i, is, Some i') pol.Context.pol_access
      @ List.map (fun (i, is) -> i, is, None) pol.Context.pol_access_all
    in

    let filter_pol' ~chan_ty ~proc_ty =
      List.filter
        (fun (pty, tyl, _scall) ->
           pty = proc_ty
           && List.exists (fun v -> v = chan_ty) tyl)
        pol'
    in

    let chan p namespace = function
      | Syntax.ChanArg { id = cname; typ = cty; param = None } ->
          ( false
          , List.map
              (fun (_, _, scall_opt) ->
                 AccessFact (namespace, param, String cname, Option.value scall_opt ~default:""))
              (filter_pol' ~chan_ty:cty ~proc_ty: p.Context.proc_type)
          , [] )
      | Syntax.ChanArg { id = cname; typ = cty; param = Some None } ->
          ( true
          , List.map
              (fun (_, _, scall_opt) ->
                 AccessFact
                   ( namespace, param, List [ String cname; Var !fresh_ident ], Option.value scall_opt ~default:""))
              (filter_pol' ~chan_ty:cty ~proc_ty: p.Context.proc_type)
          , [] )
      | Syntax.ChanArg { id = cname; typ = cty; param = Some (Some e) }
        ->
          let e, gv', _ = translate_expr2 e in
          ( false
          , List.map
              (fun (_, _, scall_opt) ->
                 AccessFact
                   (namespace, param, List [ String cname; e ], Option.value scall_opt ~default:""))
              (filter_pol' ~chan_ty:cty ~proc_ty: p.Context.proc_type)
          , gv' )
    in

    List.concat_map (fun p ->
        let namespace =
          String.capitalize_ascii
            (p.Context.proc_name
             ^ if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)
        in
        List.map (fun (Syntax.ChanArg {id; _} as c) ->
            (namespace, id), chan p namespace c) p.Context.proc_channels
      ) proc
  in

  let add_access_control n_opt t facts_gv_list =
    let add_fact n_opt t m with_param fact gv =
      let m = string_of_int m in
      let system_acp_m = String (!![system n_opt; "ACP"; m]) (* 'rab_systemn_ACP_m' *) in
      let init_fact =
        match n_opt, with_param with
        | None, false ->
            (* 'rab_system_ACP_m' *)
            system_acp_m
        | None, true ->
            (* '<rab_system_ACP_m, rab>' *)
            List [ system_acp_m; Var !fresh_ident ]
        | Some _, false ->
            (* <'rab_systemn_ACP_m', param> *)
            List [ system_acp_m; Param ]
        | Some _, true ->
            (* '<rab_systemn_ACP_m, param, rab>' *)
            List [ system_acp_m; Param; Var !fresh_ident ]
      in
      let t = add_comment t ("Fact: " ^ string_of_fact fact) in
      add_rule
        t
        { name = !!["Init"; system n_opt; "ACP"; m] (* 'Init_systemn_ACP_m' *)
        ; role = system n_opt
        ; pre = gv @ [ AccessGenFact (!![system n_opt; ""], param_expr n_opt) ]
        ; label = [ InitFact [ init_fact ] ]
        ; post = [ fact ]
        }
    in
    fst @@
    List.fold_left
      (fun (t, m) (name, (b, facts, gv)) ->
         let t = add_comment t (Printf.sprintf "Access control of %s:%s" (fst name) (snd name)) in
         List.fold_left
           (fun (t, m) fact ->
              add_fact n_opt t m b fact gv, m + 1)
           (t, m)
           facts)
      (t, 0)
      facts_gv_list
  in

  let translate_processes n_opt procs t =
    let models =
      List.map (fun p ->
          translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol) procs
    in
    let t = add_model_inits n_opt t models in
    let t = add_access_control n_opt t @@ get_access_control procs (param_expr n_opt) in
    let t = List.fold_left add_model t models in
    t
  in

  let t = translate_processes None proc t in

  let t =
    fst @@ List.fold_left
      (fun (t, n) procs -> translate_processes (Some n) procs t, n+1)
      (t, 1)
      (List.rev param_proc)
  in

  (* translating lemmas now *)
  let t = translate_lemmas t lem in
  t
;;
*)
