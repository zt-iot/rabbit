(* The semantics *)
open Typed

module Index : sig
  type t = private (int * int) list

  val compare : t -> t -> int

  val zero : t

  val add : t -> int -> t

  val push : t -> int -> t

  val to_string : t -> string

  module Set : Set.S with type elt = t
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
    String.concat "__" @@ List.rev_map (fun (a, b) -> Printf.sprintf "%d.%d" a b) i
  ;;

  module Map = Map.Make(struct
      type nonrec t = t
      let compare = compare
    end)

  module Set = Set.Make(struct
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
      }
  | Out of expr
  | In of expr
  | Plain of name * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      }
  | Global of string * expr list

  (* New additions at Sem level *)

  | Fresh of ident
  | Structure of
      { name : name
      ; proc_id : Subst.proc_id
      ; address : expr
      ; args : expr list
      }
  | Loop of
      { mode : loop_mode
      ; proc_id : Subst.proc_id
      ; param : Subst.param_id option
      ; index : Index.t
      }
  | Access of
      { proc_id: Subst.proc_id
      ; param : Subst.param_id option
      ; channel: expr
      ; syscall: ident option
      }

let is_global_fact f =
  match f.desc with
  | Channel _ -> true
  | Global _ -> true
  | _ -> false

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
  | Global (s, args) -> Printf.sprintf "::%s(%s)" s (String.concat ", " @@ List.map string_of_expr args)
  | Structure { name; proc_id; address; args } ->
      Printf.sprintf "Structure(%s, %s, %s, %s)"
        name (Ident.to_string (proc_id :> Ident.t)) (string_of_expr address) (String.concat "," (List.map string_of_expr args))
  | Loop { mode; proc_id; param; index } ->
      let mode = Typed.string_of_loop_mode mode in
      Printf.sprintf
        "Loop%s(%s, %s, %s)"
        mode
        (Ident.to_string (proc_id :> Ident.t))
        (match param with None -> "None" | Some p -> Ident.to_string (p :> Ident.t))
        (Index.to_string index)
  | Access { proc_id; param; channel; syscall } ->
      let syscall =
        match syscall with
        | None -> "."
        | Some syscall -> Ident.to_string syscall
      in
      Printf.sprintf
        "Access(%s, %s, %s, %s)"
        (Ident.to_string (proc_id :> Ident.t))
        (match param with None -> "None" | Some p -> Ident.to_string (p :> Ident.t))
        (string_of_expr channel)
        syscall

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

type update_desc =
  | New of expr
  | Update of expr
  | Drop

type update =
  { rho : Ident.t
  ; register : expr
  ; items : (Ident.t * update_desc) list
  }

let string_of_update u =
  String.concat "; " @@
  Printf.sprintf "ret %s" (string_of_expr u.register)
  :: List.filter_map (function
      | id, New e ->
          Some (Printf.sprintf "new %s = %s"
                  (Ident.to_string id)
                  (string_of_expr e))
      | _ -> None) u.items
  @ List.filter_map (function
      | id, Update e ->
          Some (Printf.sprintf "%s := %s"
                  (Ident.to_string id)
                  (string_of_expr e))
      | _ -> None) u.items
  @ List.filter_map (function
      | id, Drop ->
          Some (Printf.sprintf "drop %s"
                  (Ident.to_string id))
      | _ -> None) u.items

type edge_id = Ident.t

let edge_id = Fun.id

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
  { id : edge_id
  ; source : Index.t
  ; source_env : Env.t
  ; source_vars : Ident.t list
  ; pre : fact list
  ; update : update
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  ; target_vars : Ident.t list
  ; loop_back : bool
  }

let check_edge_invariants (e : edge) =
  let mutable_vars_of_env (env : Env.t) =
    List.filter_map (function
        | (id, Env.Var) -> Some id
        | _ -> None) env.vars
  in
  let vars =
    List.sort_uniq compare
    @@ e.source_vars
    @ e.target_vars
    @ mutable_vars_of_env e.source_env
    @ mutable_vars_of_env e.target_env
    @ Typed.mutable_vars_of_expr e.update.register
    @ List.map fst e.update.items
    @ List.concat_map (function
        | _, (New e | Update e) -> Typed.mutable_vars_of_expr e
        | _, Drop -> []) e.update.items
  in
  List.iter (fun v ->
      match
        List.assoc_opt v e.source_env.vars,
        List.mem v e.source_vars,
        List.assoc_opt v e.target_env.vars,
        List.mem v e.target_vars,
        List.assoc_opt v e.update.items
      with
      | Some _, false, _, _, _ ->
          Format.eprintf "XXXX %s@." (Ident.to_string  v);
          assert false (* if mutable var [v] is in [source_env], it must be in [source_vars] *)
      | _, _, Some _, false, _ -> assert false (* if mutable var [v] is in [target_env], it must be in [target_vars] *)
      | _, false, _, false, Some _ -> assert false (* An unknown variable to source and target is in update *)
      | _, true, _, false, Some Drop -> () (* drop *)
      | _, false, _, true, Some (New _) -> () (* new *)
      | _, true, _, true, Some (Update _) -> () (* update *)
      | _, true, _, true, None -> () (* no change *)
      | _, true, _, true, Some (Drop | New _) -> assert false
      | _, true, _, false, Some (New _ | Update _) -> assert false
      | _, true, _, false, None -> assert false
      | _, false, _, true, Some (Drop | Update _) -> assert false
      | _, false, _, true, None -> assert false
      | _, false, _, false, None ->
          assert (fst v = "rho") (* XXX *)
    ) vars

type graph = edge list

let unit env = { env; loc= Location.nowhere; desc= Unit }

let evar env id =
    { env
    ; loc = Location.nowhere
    ; desc = Ident { id; desc = Var; param = None }
    }
;;

let rho (env : Env.t) id =
  { env = { env with vars= (id, Env.Rho) :: env.vars }
  ; loc = Location.nowhere
  ; desc = Ident { id; desc = Var; param = None }
  }
;;

let channel_access ~proc:(proc : Subst.instantiated_proc) ~syscaller (f : Typed.fact) =
  match f.desc with
  | Channel { channel; _ } ->
      Some { f with desc= Access { proc_id= proc.id; param= proc.param; channel; syscall= syscaller } }
  | _ -> None

let update_unit env =
  { rho = Ident.local "rho"
  ; register = unit env
  ; items = []
  }

let update_id env =
  let id = Ident.local "rho" in
  { rho = id
  ; register = rho env id
  ; items= [] }

(* <\Gamma |- c>i *)
let rec graph_cmd ~vars ~proc:(proc : Subst.instantiated_proc) ~syscaller find_def decls i (c : cmd) : graph * Index.t * Env.t =
  (* For each edge, we have at most 1 transition variable.
     Therefore, no worry of name crash of transition variables *)
  let env = c.env in
  let fact env desc : fact = { env; desc; loc = Location.nowhere } in
  match c.desc with
  | Skip ->
      (* i =skip=> i+1 *)
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "skip"
          ; source = i (* transition_from *)
          ; source_env = env
          ; source_vars = vars
          ; pre = [] (* transition_pre *)
          ; update = update_unit env (* transition_state_transition *)
          ; tag = [] (* transition_label *)
          ; post = [] (* transition_post *)
          ; target = i_1 (* transition_to *)
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          }
        ]
      , i_1, env )
  | Sequence (c1, c2) ->
      (* i =c1=> j =c2=> k *)
      let g1, j, _ = graph_cmd ~vars ~proc ~syscaller find_def decls i c1 in
      let g2, k, env_k = graph_cmd ~vars ~proc ~syscaller find_def decls j c2 in
      g1 @ g2, k, env_k
  | Put fs ->
      (* i =put=> i+1 *)
      (* XXX ??? requires access policy check *)
      let i_1 = Index.add i 1 in
      let pre = List.filter_map (channel_access ~proc ~syscaller) fs in
      ( [ { id = Ident.local "put"
          ; source = i
          ; source_env = env
          ; source_vars = vars
          ; pre
          ; update = update_unit env
          ; tag = []
          ; post = List.map fact_of_typed fs
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          }
        ]
      , i_1, env )
  | Let (x, ({ desc= Apply _; _ } as app), c) ->
      (* var x := f(e) in c *)
      (* i =f(e)=> j =let_def=> j+1 =c=> k =let_exit=> k+1 *)
      let g, j, env_j = graph_application ~vars ~proc ~syscaller find_def decls i app in
      let j_1 = Index.add j 1 in
      let g', k, env_k = graph_cmd ~vars:(x :: vars) ~proc ~syscaller find_def decls j_1 c in
      let k_1 = Index.add k 1 in
      ( List.concat [
            g;
            [ { id = Ident.local ("let_def_" ^ fst x)
              ; source = j
              ; source_env = env_j
              ; source_vars = vars
              ; pre = []
              ; update =
                  (let update = update_unit env_j in
                   { update with items = [ x, New (rho env_j update.rho) ] })
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = c.env
              ; target_vars = x :: vars
              ; loop_back = false
              } ];
            g';
            [ { id = Ident.local ("let_exit_" ^ fst x)
              ; source = k
              ; source_env = env_k
              ; source_vars = x :: vars
              ; pre = []
              ; update = { (update_id env_k) with items = [ x, Drop ] }
              ; tag = []
              ; post = []
              ; target = k_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              } ]
          ]
      , k_1, env)
  | Let (x, e, c) ->
      (* var x := e in c *)
      (* i =let_def=> i+1 =c=> j =let_exit=> j+1 *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd ~vars:(x :: vars) ~proc ~syscaller find_def decls i_1 c in
      let j_1 = Index.add j 1 in
      ( List.concat [
            [ { id = Ident.local ("let_def_" ^ fst x)
              ; source = i
              ; source_env = env
              ; source_vars = vars
              ; pre = []
              ; update = { (update_unit env) with items = [ x, New e ] }
              ; tag = []
              ; post = []
              ; target = i_1
              ; target_env = c.env
              ; target_vars = x :: vars
              ; loop_back = false
              } ];
            g;
            [ { id = Ident.local ("let_exit_" ^ fst x)
              ; source = j
              ; source_env = env_j
              ; source_vars = x :: vars
              ; pre = []
              ; update = { (update_id env_j) with items = [ x, Drop ] }
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              }
            ]
          ],
        j_1, env )
  | Assign (Some x, ({ desc= Apply _; _ } as app)) ->
      (* i =f(e)=> j =assign_call=> j+1 *)
      (* x := f(e) *)
      let g, j, env_j = graph_application ~vars ~proc ~syscaller find_def decls i app in
      let j_1 = Index.add j 1 in
      ( List.concat [
            g;
            [ { id = Ident.local "assign_call"
              ; source = j
              ; source_env = env_j
              ; source_vars = vars
              ; pre = []
              ; update =
                  (let update = update_unit env_j in
                   { update with items = [ x, Update (rho env_j update.rho) ] })
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              } ]
          ]
      , j_1, env )
  | Assign (None, ({ desc= Apply _; _ } as app)) ->
      (* i =f(e)=> j =call=> j+1 *)
      (* _ := f(e) *)
      let g, j, env_j = graph_application ~vars ~proc ~syscaller find_def decls i app in
      let j_1 = Index.add j 1 in
      ( List.concat [
            g;
            [ { id = Ident.local "call"
              ; source = j
              ; source_env = env_j
              ; source_vars = vars
              ; pre = []
              ; update = update_unit env_j
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              } ]
          ]
      , j_1, env)
  | Assign (Some x, e) ->
      (* i =assign=> i+1 *)
      (* x := e *)
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "assign"
          ; source = i
          ; source_env = env
          ; source_vars = vars
          ; pre = []
          ; update = { (update_unit env) with items = [ x, Update e ] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          }
        ]
      , i_1, env)
  | Assign (None, _e) ->
      (* _ := e, e is pure *)
      assert false
  | Event facts ->
      (* i =event=> i+1 *)
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "event"
          ; source = i
          ; source_env = env
          ; source_vars = vars
          ; pre = []
          ; update = update_unit env
          ; tag = List.map fact_of_typed facts
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          }
        ]
      , i_1, env )
  | Return e ->
      (* i =return=> i+1 *)
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "return"
          ; source = i
          ; source_env = env
          ; source_vars = vars
          ; pre = []
          ; update = { (update_id env) with register = e }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          }
        ]
      , i_1, env )
  | New (x, eopt, c) ->
      (* i =new_intro=> i+1 =c=> j =new_out=> j+1 *)
      (* new x in c *)
      (* new x = e in c *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd ~vars:(x :: vars) ~proc ~syscaller find_def decls i_1 c in
      let j_1 = Index.add j 1 in
      ( List.concat [
            [ { id = Ident.local "new_intro"
              ; source = i
              ; source_env = env
              ; source_vars = vars
              ; pre = [ fact c.env @@ Fresh x ]
              ; update = { (update_unit env) with items = [x, New (evar c.env x)] }
              ; tag = []
              ; post =
                  (match eopt with
                   | None -> []
                   | Some (s, es) ->
                       [ fact c.env
                         @@ Structure
                           { name = s; proc_id=proc.id; address = evar c.env x; args = es }
                       ])
              ; target = i_1
              ; target_env = c.env
              ; target_vars = x :: vars
              ; loop_back = false
              } ];
            g;
            [ { id = Ident.local "new_out"
              ; source = j
              ; source_env = env_j
              ; source_vars = x :: vars
              ; pre = []
              ; update = { (update_id env_j) with items= [x, Drop] }
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              }
            ]
          ]
      , j_1, env )
  | Get (xs, e, s, c) ->
      (* i =get_intro=> i+1 =c=> j =get_out=> j+1 *)
      (* [let x1,..,xn := e.S in c] *)
      let i_1 = Index.add i 1 in
      let g, j, env_j = graph_cmd ~vars:(xs @ vars) ~proc ~syscaller find_def decls i_1 c in
      let j_1 = Index.add j 1 in
      let pre_and_post : fact list =
        [ fact env
          @@ Structure { name = s; proc_id= proc.id; address = e; args = List.map (evar c.env) xs }
        ]
      in
      ( List.concat [
            [ { id = Ident.local "get_intro"
              ; source = i
              ; source_env = env
              ; source_vars = vars
              ; pre = pre_and_post
              ; update = { (update_unit env) with items = List.map (fun x -> x, New (evar c.env x)) xs }
              ; tag = []
              ; post = pre_and_post
              ; target = i_1
              ; target_env = c.env
              ; target_vars = xs @ vars
              ; loop_back = false
              } ];
            g;
            [ { id = Ident.local "get_out"
              ; source = j
              ; source_env = env_j
              ; source_vars = xs @ vars
              ; pre = []
              ; update = { (update_id env_j) with items = List.map (fun x -> x, Drop) xs }
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              } ]
          ]
      , j_1, env )
  | Del (e, s) ->
      (* i =del=> i+1 *)
      let i_1 = Index.add i 1 in
      let arity =
        match Env.find_fact_opt env s with
        | Some (Structure, Some arity) -> arity
        | _ -> assert false
      in
      let xs =
        List.init arity
        @@ fun i ->
        let id = Ident.local (Printf.sprintf "x%d" i) in

        { env (* XXX id is not defied in env, which may cause problems later invariant check... *)
        ; loc = Location.nowhere
        ; desc = Ident { id; desc = Var; param = None }
        }
      in
      ( [ { id = Ident.local "del"
          ; source = i
          ; source_env = env
          ; source_vars = vars
          ; pre = [ fact env @@ Structure { name = s; proc_id= proc.id; address = e; args = xs } ]
          ; update = update_unit env
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
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
                let ij = Index.push i j in
                let gj, bj (* bold j *), env_bj = graph_cmd ~vars:(case.fresh @ vars) ~proc ~syscaller find_def decls ij case.cmd in
                (* XXX ??? requires access policy check *)
                ( List.concat [
                      [ { id= Ident.local "case_in"
                        ; source = i
                        ; source_env = env
                        ; source_vars = vars
                        ; pre =
                            List.map fact_of_typed case.facts
                            @ List.filter_map (channel_access ~proc ~syscaller) case.facts
                        ; update = { (update_unit env) with items = List.map (fun x -> x, New (evar case.cmd.env x)) case.fresh }
                        ; tag = []
                        ; post = []
                        ; target = ij
                        ; target_env = case.cmd.env
                        ; target_vars = case.fresh @ vars
                        ; loop_back = false
                        } ];
                      gj;
                      [ { id= Ident.local "case_out"
                        ; source = bj
                        ; source_env = env_bj
                        ; source_vars = case.fresh @ vars
                        ; pre = []
                        ; update = { (update_id env_bj) with items = List.map (fun id -> id, Drop) case.fresh }
                        ; tag = []
                        ; post = []
                        ; target = i_1
                        ; target_env = env
                        ; target_vars = vars
                        ; loop_back = false
                        } ]
                    ]))
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
         ; source_vars = vars
         ; pre = []
         ; update = update_unit env
         ; tag = [ fact env @@ Loop { mode = In; proc_id= proc.id; param= proc.param; index = i } ]
         ; post = []
         ; target = i_1
         ; target_env = env
         ; target_vars = vars
         ; loop_back = false
         }
         :: List.concat
              (List.mapi
                 (fun j (case : case) ->
                    let i_1j = Index.push i_1 j in
                    let gj, bj (* bold j *), env_bj = graph_cmd ~vars:(case.fresh @ vars) ~proc ~syscaller find_def decls i_1j case.cmd in
                    (* XXX ??? requires access policy check *)
                    List.concat [
                      [ { id= Ident.local "case_in"
                        ; source = i_1
                        ; source_env = env
                        ; source_vars = vars
                        ; pre =
                            List.map fact_of_typed case.facts
                            @ List.filter_map (channel_access ~proc ~syscaller) case.facts
                        ; update = { (update_unit env) with items = List.map (fun x -> x, New (evar case.cmd.env x)) case.fresh }
                        ; tag = []
                        ; post = []
                        ; target = i_1j
                        ; target_env = case.cmd.env
                        ; target_vars = case.fresh @ vars
                        ; loop_back = false
                        } ];
                      gj;
                      [ { id= Ident.local "case_out"
                        ; source = bj
                        ; source_env = env_bj
                        ; source_vars = case.fresh @ vars
                        ; pre = []
                        ; update = { (update_unit env_bj) with items = List.map (fun id -> id, Drop) case.fresh }
                        ; tag =
                            [ fact case.cmd.env
                              @@ Loop { mode = Back; proc_id= proc.id; param= proc.param; index = i }
                            ]
                        ; post = []
                        ; target = i_1
                        ; target_env = env
                        ; target_vars = vars
                        ; loop_back = false
                        } ]
                    ])
                 cases))
        @ List.concat
            (List.mapi
               (fun j (case : case) ->
                  let i_1jn = Index.push i_1 (j + n) in
                  let gj, bj (* bold j *), env_bj = graph_cmd ~vars:(case.fresh @ vars) ~proc ~syscaller find_def decls i_1jn case.cmd in
                  (* XXX ??? requires access policy check *)
                  List.concat [
                    [ { id= Ident.local "until_in"
                      ; source = i_1
                      ; source_env = env
                      ; source_vars = vars
                      ; pre =
                          List.map fact_of_typed case.facts
                          @ List.filter_map (channel_access ~proc ~syscaller) case.facts
                      ; update = { (update_unit env) with items = List.map (fun x -> x, New (evar case.cmd.env x)) case.fresh }
                      ; tag = []
                      ; post = []
                      ; target = i_1jn
                      ; target_env = case.cmd.env
                      ; target_vars = case.fresh @ vars
                      ; loop_back = false
                      } ];
                    gj;
                    [ { id= Ident.local "until_out"
                      ; source = bj
                      ; source_env = env_bj
                      ; source_vars = case.fresh @ vars
                      ; pre = []
                      ; update = { (update_id env_bj) with items = List.map (fun id -> id, Drop) case.fresh }
                      ; tag =
                          [ fact case.cmd.env
                            @@ Loop { mode = Out; proc_id= proc.id; param= proc.param; index = i }
                          ]
                      ; post = []
                      ; target = i_2
                      ; target_env = env
                      ; target_vars = vars
                      ; loop_back = true (* To increment the transition counter *)
                      }
                    ]
                  ])
               cases')
      in
      es, i_2, env

and graph_application ~vars ~proc ~syscaller find_def (decls : decl list) i (app : expr) : graph * Index.t * Env.t =
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
               ; source_vars = vars
               ; pre = []
               ; update = { (update_id app.env) with register = app }
               ; tag = []
               ; post = []
               ; target = i_1
               ; target_env = app.env
               ; target_vars = vars
               ; loop_back = false
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
                 let syscaller = Some f in
                 let attacks =
                   let possible_attacks = List.concat_map (fun d ->
                       match d.desc with
                       | AllowAttack { process_typs; attacks } ->
                           if List.mem proc.typ process_typs then attacks
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
                     (* XXX Attacker is restricted by the syscaller?  Yes in Totamarin. So do we here. *)
                     (* base_env must be extended! *)
                     let g', j, env_j = graph_cmd ~vars:(args @ vars) ~proc ~syscaller find_def decls ik cmd in
                     List.concat [
                       g;
                       [ { id= Ident.local ((Ident.to_string attack_id) ^ "_attack_in")
                         ; source = i
                         ; source_env = app.env
                         ; source_vars = vars
                         ; pre = []
                         ; update = { (update_unit app.env)
                                      with items= List.combine args (List.map (fun e -> New e) es) }
                         ; tag = []
                         ; post = []
                         ; target = ik
                         ; target_env = cmd.env
                         ; target_vars = args @ vars
                         ; loop_back = false
                         } ];
                       g';
                       [ { id= Ident.local ((Ident.to_string attack_id) ^ "_attack_out")
                         ; source = j
                         ; source_env = env_j
                         ; source_vars = args @ vars
                         ; pre = []
                         ; update = { (update_id env_j) with items = List.map (fun id -> id, Drop) args }
                         ; tag = []
                         ; post = []
                         ; target = i_1
                         ; target_env = app.env
                         ; target_vars = vars
                         ; loop_back = false
                         } ]
                     ])
                   [] attacks
             | Function _ -> []
             | _ -> assert false
           in

           let args, cmd = find_def f in
           (* i => i0 => ... => j => i_1 *)
           let i0 = Index.push i 0 in
           let g, j, env_j =
             let syscaller =
               match desc with
               | ExtSyscall _ -> Some f
               | _ -> syscaller
             in
             graph_cmd ~vars:(args @ vars) ~proc ~syscaller find_def decls i0 cmd
           in
           List.concat [
             [ { id= Ident.local (Ident.to_string f ^ "_app_in")
               ; source = i
               ; source_env = app.env
               ; source_vars = vars
               ; pre = []
               ; update = { (update_unit app.env) with
                            items = List.combine args (List.map (fun e -> New e) es) }
               ; tag = []
               ; post = []
               ; target = i0
               ; target_env = cmd.env
               ; target_vars = args @ vars
               ; loop_back = false
               } ];
             g;
             [ { id= Ident.local (Ident.to_string f ^ "_app_out")
               ; source = j
               ; source_env = env_j
               ; source_vars = args @ vars
               ; pre = []
               ; update = { (update_id env_j) with items = List.map (fun id -> id, Drop) args }
               ; tag = []
               ; post = []
               ; target = i_1
               ; target_env = app.env
               ; target_vars = vars
               ; loop_back = false
               } ];
             g_attacks
           ], i_1, app.env
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
  (proc : Subst.instantiated_proc)
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
                        fact (Access { proc_id= proc.id; param= proc.param; channel= path; syscall= Some syscall })) syscalls
                  else
                    []
              | Allow { process_typ; target_typs; syscalls= None } ->
                  if process_typ = proc.typ && List.mem fty target_typs then
                    [ fact (Access { proc_id= proc.id; param= proc.param; channel= path; syscall= None }) ]
                  else
                    []
              | _ -> []) decls
        in
        f :: fs) proc.files
  in
  if files = [] && proc.vars = [] then
    [], i
  else
    let i_1 = Index.add i 1 in
    [{ id= Ident.local "init_process"
     ; source = i
     ; source_env = env
     ; source_vars = []
     ; pre = []
     ; update = { (update_unit env) with items = List.map (fun (id,e) -> id, New e) proc.vars }
     ; tag = []
     ; post = files
     ; target = i_1
     ; target_env = proc.main.env
     ; target_vars = List.map fst proc.vars
     ; loop_back = false
     }],
    i_1

type model =
  { id : Subst.proc_id
  ; param : Subst.param_id option
  ; edges : edge list
  }

let model_process ~loc env decls syscalls (proc : Subst.instantiated_proc) =
  let funcs = List.map (fun (f, args, cmd) -> f, (args, cmd)) proc.Subst.funcs in
  let find_def n = List.assoc n (syscalls @ funcs) in
  let g, i = graph_files_and_vars ~loc env decls proc Index.zero in
  let g', _j, _env =
    graph_cmd ~vars:(List.map fst proc.vars) ~proc ~syscaller:None find_def decls i proc.main in
  let g = g @ g' in
  ignore (check_edges g);
  Format.eprintf "%t: %d edges@." (Ident.print (proc.id :> Ident.t)) (List.length g);
  List.iter (fun (e : edge) ->
      Format.eprintf "  %t@." (Ident.print e.id)
    ) g;
  { id= proc.id; param= proc.param; edges= g }

let instantiate_proc_groups (decls : decl list) (sys : decl) =
  match sys.desc with
  | System (proc_groups, _lemmas) ->
      List.map (Subst.instantiate_proc_group decls) proc_groups
  | _ -> assert false

type modeled_proc_group_desc =
  | Unbounded of model
  | Bounded of Subst.param_id * model list

let model_proc_groups (decls : decl list) (sys : decl) (proc_groups : Subst.instantiated_proc_group list)
  : (Subst.proc_group_id * modeled_proc_group_desc) list =
  let syscalls =
    List.filter_map (fun decl ->
        match decl.desc with
        | Syscall { id; args; cmd } -> Some (id, (args, cmd))
        | _ -> None) decls
  in
  List.rev @@ List.fold_left (fun rev_ps ({ id=proc_group_id; desc= p } : Subst.instantiated_proc_group) ->
      let p =
        match p with
        | Unbounded proc ->
            let m = model_process ~loc:sys.loc sys.env decls syscalls proc in
            proc_group_id, Unbounded m
        | Bounded (param, procs) ->
            let ms = List.map (model_process ~loc:sys.loc sys.env decls syscalls) procs in
            proc_group_id, Bounded (param, ms)
      in
      (p :: rev_ps)) [] proc_groups

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

let get_constants (decls : decl list) : (Typed.ident * Typed.init_desc) list =
  List.filter_map (fun (d : decl) ->
      match d.desc with
      | Init { id; desc } -> Some (id, desc)
      | _ -> None) decls

let get_access_controls (decls : decl list) (proc : Subst.instantiated_proc_group)
  : Subst.proc_group_id * (Subst.proc_id * (Typed.chan_arg * Typed.ident option) list) list =
  let aux (proc : Subst.instantiated_proc) =
    proc.id,
    List.concat @@ List.filter_map (fun decl ->
        match decl.desc with
        | Allow { process_typ; target_typs; syscalls } when proc.typ = process_typ ->
            let chan_args =
              List.filter (fun chan_arg ->
                  List.mem chan_arg.typ target_typs) proc.args
            in
            let syscalls =
              match syscalls with
              | None -> [None]
              | Some ss -> List.map Option.some ss
            in
            Some (List.concat_map (fun chan_arg ->
                List.map (fun syscall -> (chan_arg, syscall)) syscalls) chan_args)
        | _ -> None) decls
  in
  proc.id,
  match proc.desc with
  | Unbounded pproc -> [aux pproc]
  | Bounded (_param, pprocs) -> List.map aux pprocs

type t =
  { signature : signature
  ; proc_groups : (Subst.proc_group_id * modeled_proc_group_desc) list
  ; access_controls : (Subst.proc_group_id * (Subst.proc_id * (chan_arg * ident option) list) list) list
  ; constants : (ident * init_desc) list
  ; lemmas : (Ident.t * lemma) list
  }

let t_of_decls (decls : decl list) =
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
  let proc_groups : Subst.instantiated_proc_group list= instantiate_proc_groups decls sys in
  let modeled_proc_groups = model_proc_groups decls sys proc_groups in
  let constants = get_constants decls in
  let lemmas = lemmas_system sys in
  let access_controls = List.map (get_access_controls decls) proc_groups in
  { signature; proc_groups= modeled_proc_groups; constants; lemmas; access_controls }

(* Explained Rabbit2.0.pdf, C. Graph Compression *)
let _compressable edges e1 e2 =
  (* Consecutive *)
  (e1.target = e2.source)
  &&
  (* The tags *)
  (match e1.tag, e2.tag with
   | [], [] -> true
   | _, [] -> e2.pre = []
   | [], _ -> List.for_all (fun f -> not @@ is_global_fact f) e1.post
   | _, _ -> false)
  &&
  (* The topology around e1.target (= e2.source) *)
  ( let ins = List.filter (fun e -> e.target = e1.target) edges in
    let outs = List.filter (fun e -> e.source = e1.target) edges in
    match ins, outs with
    | [_], _
    | _, [_] -> true
    | _ -> false )
  &&
  (* The preconditions of e2 *)
  List.for_all is_global_fact e2.pre
  (* e1 must not be loop_back *)
  && not e1.loop_back

(*
let compress_update enforces update1 update2 =
  let rec eval e =
    match e.desc with
    | Boolean _ | String _ | Integer _ | Float _ | Unit -> e
    | Ident { id=_; param= None; desc= Rho } -> update1.register
    | Ident { id=_; param= None; desc= Var Param } ->
        (* Not mutable *)
        e
    | Ident { id; param= None; desc= Var _ } -> (* mutable *)
        (match List.assoc_opt id update1.items with
         | None -> e
         | Some Drop -> assert false (* Dropped by update1 but used in update2 *)
         | Some (New e | Update e) -> e)
    | Ident { id=_; param= _; desc= _ } -> e
    | Apply (f, es) -> { e with desc= Apply (f, List.map eval es) }
    | Tuple es -> { e with desc= Tuple (List.map eval es) }
  in
  let register = eval update2.register in
  let items =
    List.map (fun (id, udesc) ->
        id,
        match udesc with
        | Drop -> Drop
        | New e -> New (eval e)
        | Update e -> Update (eval e)) update2.items
  in
  { rho= update1.rho; register; items }

let compress (e1 : edge) (e2 : edge) =
  let id = Ident.local (fst e1.id ^ "_" ^ fst e2.id) in
  (* fix structure (C. Graph Compression: special case) *)
  let e1_post, enforces, e2_pre =
    let e2_pre_structure_bindings =
      List.filter_map (fun (f : fact) ->
          match f.desc with
          | Structure { name; proc_id; address; args } ->
              let (let+) a f =
                match a with
                | None -> None
                | Some v -> f v
              in
              let rec mapM f = function
                | [] -> Some []
                | x::xs ->
                    let* x = f x in
                    let* xs = mapM f xs in
                    Some (x :: xs)
              in
              let get_var (e : expr) =
                match e.desc with
                | Ident { id; _ } -> Some id
                | _ -> None
              in
              let* address = get_var address in
              let* args = mapM get_var args in
              Some ((name, proc_id), (f, address, args))
          | _ -> None) e2.pre
    in
    let e1_post, enforces, e2_pre_removals =
      List.fold_left (fun (e1_post, enforces, e2_pre_removals) (f : fact) ->
          match f.desc with
          | Structure { name; proc_id; address; args } ->
              (match List.assoc_opt (name, proc_id) e2_pre_structure_bindings with
              | None -> f :: e1_post, enforces, e2_pre_removals
              | Some (f2, address', args') ->
                  e1_post, (address', address) :: List.combine args' args, f2 :: e2_pre_removals)
          | _ -> f :: e1_post, enforces, e2_pre_removals)
        ([], [], []) e1.post
    in
    let e2_pre = List.filter (fun f -> not @@ List.mem f e2_pre_removals) e2.pre in
    e1_post, enforces, e2_pre
  in
  let update = compress_upadte enforces e1.update e2.update in
  { id
  ; source = e1.source
  ; source_env = e1.source_env
  ; source_vars = e1.source_vars
  ; pre = e1.pre @ e2_pre
  ; update
  ; tag = e1.tag @ e2.tag
  ; post = e1_post @ e2.post
  ; target = e2.target
  ; target_env = e2.target_env
  ; target_vars = e2.target_vars
  ; loop_back = e2.loop_back
  }
*)
