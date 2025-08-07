(* The semantics *)
open Typed

(** Conversion errors *)
type error =
  | NoSystem
  | MultipleSystems
  | LocalFactNotAllowed

(** Print error description. *)
let print_error err ppf =
  match err with
  | NoSystem -> Format.fprintf ppf "No system to compile"
  | MultipleSystems -> Format.fprintf ppf "Only 1 system can exist"
  | LocalFactNotAllowed -> Format.fprintf ppf "Local fact is not allowed in this context"

exception Error of error Location.located

(** [error ~loc err] raises the given runtime error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let debug = ref true

let unit = { env= Env.empty (); loc= Location.nowhere; desc= Unit }

let evar id =
    { env = { vars= [id, Var]; facts = ref [] }
    ; loc = Location.nowhere
    ; desc = Ident { id; desc = Var; param = None }
    }
;;

let rho id =
  { env = { vars= [id, Env.Rho]; facts = ref [] }
  ; loc = Location.nowhere
  ; desc = Ident { id; desc = Rho; param = None }
  }
;;

module Index : sig
  type t = private (int * int) list

  val compare : t -> t -> int

  val compare_lexico : t -> t -> int
  (** Lexicographic ordering.  Slower than [compare] *)

  val zero : t

  val add : t -> int -> t

  val push : t -> int -> t

  val to_string : t -> string

  val to_string' : t -> string

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end = struct
  type t = (int * int) list

  let compare = compare

  let compare_lexico i1 i2 =
    let rec aux i1 i2 =
      match i1, i2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | ii1 :: i1, ii2 :: i2 ->
          match compare ii1 ii2 with
          | 0 -> aux i1 i2
          | n -> n
    in
    aux (List.rev i1) (List.rev i2)

  let zero = [ 0, 0 ]

  let add i k =
    match i with
    | [] -> assert false
    | (n, j) :: i' -> (n, j + k) :: i'
  ;;

  let push i n = (n, 0) :: i

  let to_string i =
    String.concat "_" @@ List.rev_map (fun (a, b) -> Printf.sprintf "%d.%d" a b) i
  ;;

  let to_string' i =
    String.concat "_" @@ List.rev_map (fun (a, b) -> Printf.sprintf "%d_%d" a b) i
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
  | Plain of
      { pid : Subst.proc_id * Subst.param_id option
      ; name : name
      ; args : expr list
      }
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { pid : Subst.proc_id * Subst.param_id option
      ; path : expr
      ; contents : expr
      }
  | Global of string * expr list

  (* New additions at Sem level *)

  | Fresh of ident
  | Structure of
      { pid : Subst.proc_id * Subst.param_id option
      ; name : name
      ; address : expr
      ; args : expr list
      }
  | Loop of
      { pid : Subst.proc_id * Subst.param_id option
      ; mode : loop_mode
      ; index : Index.t
      }
  | Access of
      { pid : Subst.proc_id * Subst.param_id option
      ; channel: expr (* XXX it is also used for file path *)
      ; syscall: ident option
      }

let is_nonlocal_fact f =
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
  | Plain { pid=_; name; args } -> Printf.sprintf "%s(%s)" name (String.concat ", " @@ List.map string_of_expr args)
  | Eq (e1, e2) -> Printf.sprintf "%s = %s" (string_of_expr e1) (string_of_expr e2)
  | Neq (e1, e2) -> Printf.sprintf "%s != %s" (string_of_expr e1) (string_of_expr e2)
  | File { pid=_; path; contents } ->
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
  | Structure { pid=_; name; address; args } ->
      Printf.sprintf "Structure(%s, %s, %s)"
        name
        (string_of_expr address) (String.concat "," (List.map string_of_expr args))
  | Loop { pid=_; mode; index } ->
      let mode = Typed.string_of_loop_mode mode in
      Printf.sprintf
        "Loop%s(%s)"
        mode
        (Index.to_string index)
  | Access { pid=_; channel; syscall } ->
      let syscall =
        match syscall with
        | None -> "."
        | Some syscall -> Ident.to_string syscall
      in
      Printf.sprintf
        "Access(%s, %s)"
        (string_of_expr channel)
        syscall

let fact_of_typed pido (f : Typed.fact) : fact =
  let get_pid () =
    match pido with
    | Some pid -> pid
    | None -> error ~loc:f.loc LocalFactNotAllowed
  in
  let desc : fact' =
    match f.desc with
    | Channel { channel; name; args} -> Channel { channel; name; args }
    | Plain (name, es) -> Plain { pid= get_pid (); name; args= es }
    | Eq (e1, e2) -> Eq (e1, e2)
    | Neq (e1, e2) -> Neq (e1, e2)
    | File { path; contents } -> File { pid= get_pid (); path; contents }
    | Global (name, es) -> Global (name, es)
  in
  { f with desc }

module Update = struct
  type desc =
    | New of expr
    | Update of expr
    | Drop

  type t =
    { rho : Ident.t
    ; register : expr
    ; items : (Ident.t * desc) list
    }

  let to_string u =
    String.concat "; " @@
    Printf.sprintf "%s <- %s" (Ident.to_string u.rho) (string_of_expr u.register)
    :: List.filter_map (function
        | id, New { desc= Ident { id= id'; _ }; _ } when id = id' ->
            (* new id <- id ==>  new id *)
            Some (Printf.sprintf "new %s"
                    (Ident.to_string id))
        | id, New e ->
            Some (Printf.sprintf "new %s = %s"
                    (Ident.to_string id)
                    (string_of_expr e))
        | _ -> None) u.items
    @ List.filter_map (function
        | id, Update e ->
            Some (Printf.sprintf "%s <- %s"
                    (Ident.to_string id)
                    (string_of_expr e))
        | _ -> None) u.items
    @ List.filter_map (function
        | id, Drop ->
            Some (Printf.sprintf "drop %s"
                    (Ident.to_string id))
        | _ -> None) u.items

  (* U is an update.
     V(x) is the value of x.

     U maps V to V',  V' = U(V) as follows:

     - If x is not in U,                V'(x) = V(x)
     - If U(x) = Drop,                  V'(x) = None
     - If U(x) = New(e) or Update(e)    V'(x) = update_expr(V, e)
  *)
  let rec update_expr (u : t) (e : expr) =
    match e.desc with
    | Boolean _ | String _ | Integer _ | Float _ | Unit -> e
    | Ident { id=_; param= None; desc= Rho } ->
        (* [id] and [u.rho] are usually different, but we do not care *)
        u.register
    | Ident { id; param= None; desc= Var} ->
        (match List.assoc_opt id u.items with
         | None -> evar id (* no binding *)
         | Some Drop -> assert false (* dropped *)
         | Some (New e | Update e) -> e)
    | Ident { id=_; param= None; desc= Param } ->
        (* Not mutable *)
        e
    | Ident { id=_; param= _; desc= _ } -> e
    | Apply (f, es) -> { e with desc= Apply (f, List.map (update_expr u) es) }
    | Tuple es -> { e with desc= Tuple (List.map (update_expr u) es) }

  let update_fact u (f : fact) : fact =
    let s = update_expr u in
    let desc =
      match f.desc with
      | Channel { channel; name; args } ->
          Channel { channel= s channel; name; args= List.map s args }
      | Plain { pid; name; args } -> Plain { pid; name; args= List.map s args }
      | Eq (e1, e2) -> Eq (s e1, s e2)
      | Neq (e1, e2) -> Neq (s e1, s e2)
      | File { pid; path; contents } -> File { pid; path= s path; contents= s contents }
      | Global (n, es) -> Global (n, List.map s es)
      | Structure { pid; name; address; args } ->
          Structure { pid; name; address= s address; args= List.map s args }
      | Fresh _-> f.desc
      | Loop _ -> f.desc
      | Access { pid; channel; syscall } ->
          Access { pid; channel= s channel; syscall }
    in
    { f with desc }

  let compress (u1 : t) (u2 : t) =
    let register = update_expr u1 u2.register in
    let items =
      List.filter_map (fun (x, desc) ->
          match desc with
          | Drop ->
              (match List.assoc_opt x u1.items with
               | Some Drop -> assert false
               | Some (New _) -> (* New + Drop = None *) None
               | None | Some (Update _) -> Some (x, Drop))
          | New e ->
              Some (x, New (update_expr u1 e ))
          | Update e ->
              let e = update_expr u1 e in
              (match List.assoc_opt x u1.items with
               | Some Drop -> assert false
               | Some (New _) -> (* New + Update = New *) Some (x, New e)
               | None | Some (Update _) -> Some (x, Update e))) u2.items
      @
      (* variables not mapped by u2 are kept as they are*)
      List.filter (fun (x, _) -> not (List.mem_assoc x u2.items)) u1.items
    in
    { u1 with register; items }

  let override_enforces enforces u =
    match enforces with
    | [] -> u
    | _ ->
        let items =
          List.map (fun (v, desc) ->
              v,
              match desc, List.assoc_opt v enforces with
              | New { desc= Ident {id= v'; _}; _}, Some e when v = v' -> New e
              | _ -> desc) u.items
        in
        { u with items }

  let update_unit () =
    { rho = Ident.local "rho"
    ; register = unit
    ; items = []
    }

  let update_id () =
    let id = Ident.local "rho" in
    { rho = id
    ; register = rho id
    ; items= [] }
end

type edge_id = Ident.t

let edge_id = Fun.id

type edge =
  { id : edge_id
  ; source : Index.t
  ; source_env : Env.t
  ; source_vars : Ident.t list
  ; pre : fact list
  ; update : Update.t
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  ; target_vars : Ident.t list
  ; loop_back : bool
  ; attack : bool
  }

let print_list sep f =
  Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf sep) f

let print_edge_summary ppf (e : edge) =
  let open Format in
  let f = fprintf in
  let pp_facts ppf = print_list ",@ " (fun ppf fact -> f ppf "%s" (string_of_fact fact)) ppf in
  f ppf "@[<v2>%s:@ @[<v>[ @[<v>%a@] ] @[%a@]@ --[ @[<v>%a@] ]->@ [ @[<v>%a@] ] %s@]@] / %s"
    (Index.to_string e.source)
    pp_facts e.pre
    (print_list ", " (fun ppf id -> f ppf "%s" (Ident.to_string id))) e.source_vars
    pp_facts e.tag
    pp_facts e.post
    (Index.to_string e.target)
    (Update.to_string e.update)

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
    @ Typed.vars_of_expr e.update.register
    @ List.map fst e.update.items
    @ List.concat_map (function
        | _, (Update.New e | Update e) -> Typed.vars_of_expr e
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

let channel_and_file_access ~proc:(proc : Subst.proc) ~syscaller (f : Typed.fact) =
  let pid = proc.id, proc.param in
  match f.desc with
  | Channel { channel; _ } ->
      Some { f with desc= Access { pid; channel; syscall= syscaller } }
  | File { path; contents= _ } ->
      Some { f with desc= Access { pid; channel= path; syscall= syscaller } }
  | _ -> None

(* <\Gamma |- c>i *)
let rec graph_cmd ~vars ~proc:(proc : Subst.proc) ~syscaller find_def decls i (c : cmd) : graph * Index.t * Env.t =
  (* For each edge, we have at most 1 transition variable.
     Therefore, no worry of name crash of transition variables *)
  let env = c.env in
  let fact env desc : fact = { env; desc; loc = Location.nowhere } in
  let pid = proc.id, proc.param in
  let fact_of_typed = fact_of_typed (Some pid) in
  match c.desc with
  | Skip ->
      (* i =skip=> i+1 *)
      let i_1 = Index.add i 1 in
      ( [ { id = Ident.local "skip"
          ; source = i (* transition_from *)
          ; source_env = env
          ; source_vars = vars
          ; pre = [] (* transition_pre *)
          ; update = Update.update_unit () (* transition_state_transition *)
          ; tag = [] (* transition_label *)
          ; post = [] (* transition_post *)
          ; target = i_1 (* transition_to *)
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          ; attack = false
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
      let pre = List.filter_map (channel_and_file_access ~proc ~syscaller) fs in
      ( [ { id = Ident.local "put"
          ; source = i
          ; source_env = env
          ; source_vars = vars
          ; pre
          ; update = Update.update_unit ()
          ; tag = []
          ; post = List.map fact_of_typed fs
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          ; attack = false
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
                  (let update = Update.update_unit () in
                   { update with items = [ x, New (rho update.rho) ] })
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = c.env
              ; target_vars = x :: vars
              ; loop_back = false
              ; attack = false
              } ];
            g';
            [ { id = Ident.local ("let_exit_" ^ fst x)
              ; source = k
              ; source_env = env_k
              ; source_vars = x :: vars
              ; pre = []
              ; update = { (Update.update_id ()) with items = [ x, Drop ] }
              ; tag = []
              ; post = []
              ; target = k_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              ; attack = false
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
              ; update = { (Update.update_unit ()) with items = [ x, New e ] }
              ; tag = []
              ; post = []
              ; target = i_1
              ; target_env = c.env
              ; target_vars = x :: vars
              ; loop_back = false
              ; attack = false
              } ];
            g;
            [ { id = Ident.local ("let_exit_" ^ fst x)
              ; source = j
              ; source_env = env_j
              ; source_vars = x :: vars
              ; pre = []
              ; update = { (Update.update_id ()) with items = [ x, Drop ] }
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              ; attack = false
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
                  (let update = Update.update_unit () in
                   { update with items = [ x, Update (rho update.rho) ] })
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              ; attack = false
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
              ; update = Update.update_unit ()
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              ; attack = false
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
          ; update = { (Update.update_unit ()) with items = [ x, Update e ] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          ; attack = false
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
          ; update = Update.update_unit ()
          ; tag = List.map fact_of_typed facts
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          ; attack = false
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
          ; update = { (Update.update_id ()) with register = e }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          ; attack = false
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
              ; update = { (Update.update_unit ()) with items = [x, New (evar x)] }
              ; tag = []
              ; post =
                  (match eopt with
                   | None -> []
                   | Some (s, es) ->
                       [ fact c.env
                         @@ Structure
                           { pid; name = s; address = evar x; args = es }
                       ])
              ; target = i_1
              ; target_env = c.env
              ; target_vars = x :: vars
              ; loop_back = false
              ; attack = false
              } ];
            g;
            [ { id = Ident.local "new_out"
              ; source = j
              ; source_env = env_j
              ; source_vars = x :: vars
              ; pre = []
              ; update = { (Update.update_id ()) with items= [x, Drop] }
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              ; attack = false
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
          @@ Structure { pid; name = s; address = e; args = List.map evar xs }
        ]
      in
      ( List.concat [
            [ { id = Ident.local "get_intro"
              ; source = i
              ; source_env = env
              ; source_vars = vars
              ; pre = pre_and_post
              ; update = { (Update.update_unit ())
                           with items = List.map (fun x -> x, Update.New (evar x)) xs }
              ; tag = []
              ; post = pre_and_post
              ; target = i_1
              ; target_env = c.env
              ; target_vars = xs @ vars
              ; loop_back = false
              ; attack = false
              } ];
            g;
            [ { id = Ident.local "get_out"
              ; source = j
              ; source_env = env_j
              ; source_vars = xs @ vars
              ; pre = []
              ; update = { (Update.update_id ()) with items = List.map (fun x -> x, Update.Drop) xs }
              ; tag = []
              ; post = []
              ; target = j_1
              ; target_env = env
              ; target_vars = vars
              ; loop_back = false
              ; attack = false
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
          ; pre = [ fact env @@ Structure { pid; name = s; address = e; args = xs } ]
          ; update = Update.update_unit ()
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          ; target_vars = vars
          ; loop_back = false
          ; attack = false
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
                ( List.concat [
                      [ { id= Ident.local "case_in"
                        ; source = i
                        ; source_env = env
                        ; source_vars = vars
                        ; pre =
                            List.map fact_of_typed case.facts
                            @ List.filter_map (channel_and_file_access ~proc ~syscaller) case.facts
                        ; update = { (Update.update_unit ())
                                     with items = List.map (fun x -> x, Update.New (evar x)) case.fresh }
                        ; tag = []
                        ; post = []
                        ; target = ij
                        ; target_env = case.cmd.env
                        ; target_vars = case.fresh @ vars
                        ; loop_back = false
                        ; attack = false
                        } ];
                      gj;
                      [ { id= Ident.local "case_out"
                        ; source = bj
                        ; source_env = env_bj
                        ; source_vars = case.fresh @ vars
                        ; pre = []
                        ; update = { (Update.update_id ()) with items = List.map (fun id -> id, Update.Drop) case.fresh }
                        ; tag = []
                        ; post = []
                        ; target = i_1
                        ; target_env = env
                        ; target_vars = vars
                        ; loop_back = false
                        ; attack = false
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
         ; update = Update.update_unit ()
         ; tag = [ fact env @@ Loop { pid; mode = In; index = i } ]
         ; post = []
         ; target = i_1
         ; target_env = env
         ; target_vars = vars
         ; loop_back = false
         ; attack = false
         }
         :: List.concat
              (List.mapi
                 (fun j (case : case) ->
                    let i_1j = Index.push i_1 j in
                    let gj, bj (* bold j *), env_bj = graph_cmd ~vars:(case.fresh @ vars) ~proc ~syscaller find_def decls i_1j case.cmd in
                    List.concat [
                      [ { id= Ident.local "case_in"
                        ; source = i_1
                        ; source_env = env
                        ; source_vars = vars
                        ; pre =
                            List.map fact_of_typed case.facts
                            @ List.filter_map (channel_and_file_access ~proc ~syscaller) case.facts
                        ; update = { (Update.update_unit ())
                                     with items = List.map (fun x -> x, Update.New (evar x)) case.fresh }
                        ; tag = []
                        ; post = []
                        ; target = i_1j
                        ; target_env = case.cmd.env
                        ; target_vars = case.fresh @ vars
                        ; loop_back = false
                        ; attack = false
                        } ];
                      gj;
                      [ { id= Ident.local "case_out"
                        ; source = bj
                        ; source_env = env_bj
                        ; source_vars = case.fresh @ vars
                        ; pre = []
                        ; update = { (Update.update_unit ()) with items = List.map (fun id -> id, Update.Drop) case.fresh }
                        ; tag =
                            [ fact case.cmd.env
                              @@ Loop { pid; mode = Back; index = i }
                            ]
                        ; post = []
                        ; target = i_1
                        ; target_env = env
                        ; target_vars = vars
                        ; loop_back = true (* To increment the transition counter *)
                        ; attack = false
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
                          @ List.filter_map (channel_and_file_access ~proc ~syscaller) case.facts
                      ; update = { (Update.update_unit ())
                                   with items = List.map (fun x -> x, Update.New (evar x)) case.fresh }
                      ; tag = []
                      ; post = []
                      ; target = i_1jn
                      ; target_env = case.cmd.env
                      ; target_vars = case.fresh @ vars
                      ; loop_back = false
                      ; attack = false
                      } ];
                    gj;
                    [ { id= Ident.local "until_out"
                      ; source = bj
                      ; source_env = env_bj
                      ; source_vars = case.fresh @ vars
                      ; pre = []
                      ; update = { (Update.update_id ())
                                   with items = List.map (fun id -> id, Update.Drop) case.fresh }
                      ; tag =
                          [ fact case.cmd.env
                            @@ Loop { pid; mode = Out; index = i }
                          ]
                      ; post = []
                      ; target = i_2
                      ; target_env = env
                      ; target_vars = vars
                      ; loop_back = false
                      ; attack = false
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
               ; update = { (Update.update_id ()) with register = app }
               ; tag = []
               ; post = []
               ; target = i_1
               ; target_env = app.env
               ; target_vars = vars
               ; loop_back = false
               ; attack = false
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
                         ; update = { (Update.update_unit ())
                                      with items= List.combine args (List.map (fun e -> Update.New e) es) }
                         ; tag = []
                         ; post = []
                         ; target = ik
                         ; target_env = cmd.env
                         ; target_vars = args @ vars
                         ; loop_back = false
                         ; attack = true
                         } ];
                       g';
                       [ { id= Ident.local ((Ident.to_string attack_id) ^ "_attack_out")
                         ; source = j
                         ; source_env = env_j
                         ; source_vars = args @ vars
                         ; pre = []
                         ; update = { (Update.update_id ())
                                      with items = List.map (fun id -> id, Update.Drop) args }
                         ; tag = []
                         ; post = []
                         ; target = i_1
                         ; target_env = app.env
                         ; target_vars = vars
                         ; loop_back = false
                         ; attack = false
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
               ; update = { (Update.update_unit ())
                            with items = List.combine args (List.map (fun e -> Update.New e) es) }
               ; tag = []
               ; post = []
               ; target = i0
               ; target_env = cmd.env
               ; target_vars = args @ vars
               ; loop_back = false
               ; attack = false
               } ];
             g;
             [ { id= Ident.local (Ident.to_string f ^ "_app_out")
               ; source = j
               ; source_env = env_j
               ; source_vars = args @ vars
               ; pre = []
               ; update = { (Update.update_id ())
                            with items = List.map (fun id -> id, Update.Drop) args }
               ; tag = []
               ; post = []
               ; target = i_1
               ; target_env = app.env
               ; target_vars = vars
               ; loop_back = false
               ; attack = false
               } ];
             g_attacks
           ], i_1, app.env
       | None | Some _ -> assert false)
  | _ -> assert false
;;

let check_edges es =
  let vs = Index.Map.empty in
  List.fold_left (fun vs (e : edge) ->
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
  (proc : Subst.proc)
  (i : Index.t) =
  let fact fact' : fact = { env; desc=fact'; loc } in
  let pid = proc.id, proc.param in
  let files : fact list =
    List.concat_map (fun (path, fty, contents) ->
        let f = fact @@ File { pid; path; contents } in
        let fs : fact list =
          List.concat_map (fun (decl : Typed.decl) ->
              match decl.desc with
              | Allow { process_typ; target_typs; syscalls= Some syscalls } ->
                  if process_typ = proc.typ && List.mem fty target_typs then
                    List.map (fun syscall ->
                        fact (Access { pid; channel= path; syscall= Some syscall })) syscalls
                  else
                    []
              | Allow { process_typ; target_typs; syscalls= None } ->
                  if process_typ = proc.typ && List.mem fty target_typs then
                    [ fact (Access { pid; channel= path; syscall= None }) ]
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
     ; update = { (Update.update_unit ())
                  with items = List.map (fun (id,e) -> id, Update.New e) proc.vars }
     ; tag = []
     ; post = files
     ; target = i_1
     ; target_env = proc.main.env
     ; target_vars = List.map fst proc.vars
     ; loop_back = false
     ; attack = false
     }],
    i_1

type proc =
  { id : Subst.proc_id
  ; param : Subst.param_id option
  ; edges : edge list
  }

let model_process ~loc env decls syscalls (proc : Subst.proc) =
  let funcs = List.map (fun (f, args, cmd) -> f, (args, cmd)) proc.Subst.funcs in
  let find_def n = List.assoc n (syscalls @ funcs) in
  let g, i = graph_files_and_vars ~loc env decls proc Index.zero in
  let g', _j, _env =
    graph_cmd ~vars:(List.map fst proc.vars) ~proc ~syscaller:None find_def decls i proc.main in
  let g = g @ g' in
  ignore (check_edges g);
  { id= proc.id; param= proc.param; edges= g }

let instantiate_proc_groups (decls : decl list) (sys : decl) =
  match sys.desc with
  | System (proc_groups, _lemmas) ->
      List.map (Subst.instantiate_proc_group decls) proc_groups
  | _ -> assert false

type proc_group_desc =
  | Unbounded of proc
  | Bounded of Subst.param_id * proc list

type proc_group = Subst.proc_group_id * proc_group_desc

let model_proc_groups (decls : decl list) (sys : decl) (proc_groups : Subst.proc_group list)
  : proc_group list =
  let syscalls =
    List.filter_map (fun (decl : Typed.decl) ->
        match decl.desc with
        | Syscall { id; args; cmd } -> Some (id, (args, cmd))
        | _ -> None) decls
  in
  List.rev @@ List.fold_left (fun rev_ps (proc_group_id, proc_group_desc) ->
      let pg =
        proc_group_id,
        match (proc_group_desc : Subst.proc_group_desc) with
        | Unbounded proc ->
            let proc = model_process ~loc:sys.loc sys.env decls syscalls proc in
            Unbounded proc
        | Bounded (param, procs) ->
            let ms = List.map (model_process ~loc:sys.loc sys.env decls syscalls) procs in
            Bounded (param, ms)
      in
      (pg :: rev_ps)) [] proc_groups

let lemmas_system (sys : decl) =
  match sys.desc with
  | System (_procs, lemmas) -> lemmas
  | _ -> assert false

type signature =
  { functions : (Ident.t * int) list
  ; equations : (Typed.expr * Typed.expr) list
  }

let functions_of_decls (decls : decl list) =
  List.filter_map (fun (d : decl) ->
      match d.desc with
      | Function { id; arity } -> Some (id,arity)
      | _ -> None) decls

let equations_of_decls (decls : decl list) =
  List.filter_map (fun (d : decl) ->
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

let get_access_controls (decls : decl list) (proc_group_id, proc_group_desc : Subst.proc_group)
  : Subst.proc_group_id * (Subst.proc_id * (Typed.chan_arg * Typed.ident option) list) list =
  let aux (proc : Subst.proc) =
    proc.id,
    List.concat @@ List.filter_map (fun (decl : decl) ->
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
  proc_group_id,
  match proc_group_desc with
  | Unbounded pproc -> [aux pproc]
  | Bounded (_param, pprocs) -> List.map aux pprocs

type t =
  { signature : signature
  ; proc_groups : proc_group list
  ; access_controls : (Subst.proc_group_id * (Subst.proc_id * (chan_arg * ident option) list) list) list
  ; constants : (ident * init_desc) list
  ; lemmas : (Ident.t * lemma) list
  }

let compile (decls : decl list) =
  (* for each process:
     - model inits
     - access control
     - model
  *)
  let sys =
    match
      List.filter (fun (d : decl) ->
          match d.desc with
          | System _ -> true
          | _ -> false) decls
    with
    | [sys] -> sys
    | [] -> error ~loc:Location.nowhere NoSystem
    | _ -> error ~loc:Location.nowhere MultipleSystems
  in
  let signature = signature_of_decls decls in
  let proc_groups : Subst.proc_group list= instantiate_proc_groups decls sys in
  let modeled_proc_groups = model_proc_groups decls sys proc_groups in
  let constants = get_constants decls in
  let lemmas = lemmas_system sys in
  let access_controls = List.map (get_access_controls decls) proc_groups in
  { signature; proc_groups= modeled_proc_groups; constants; lemmas; access_controls }

let rec eq_expr e1 e2 =
  match e1.desc, e2.desc with
  | Unit, Unit -> true
  | Boolean b1, Boolean b2 -> b1 = b2
  | Integer i1, Integer i2 -> i1 = i2
  | Float f1, Float f2 -> f1 = f2
  | String s1, String s2 -> s1 = s2
  | Tuple es1, Tuple es2 ->
      (* Untyped therefore lengths can be differ *)
      List.length es1 = List.length es2 && List.for_all2 eq_expr es1 es2
  | Apply (f1, es1), Apply (f2, es2) when f1 = f2 ->
      (* Untyped therefore lengths can be differ *)
      List.length es1 = List.length es2 && List.for_all2 eq_expr es1 es2
  | Ident { id=id1; desc=desc1; param=param1 }, Ident { id=id2; desc=desc2; param=param2 }
    when id1 = id2 && desc1 = desc2 ->
      (match param1, param2 with
       | None, None -> true
       | Some e1, Some e2 -> eq_expr e1 e2
       | _ -> false)
  | _ -> false

(* Explained Rabbit2.0.pdf, C. Graph Compression *)
let compressable edges e1 e2 =
  (* Consecutive *)
  (e1.target = e2.source)
  &&
  let debug =
    match (e1.source :> (int * int) list), (e1.target :> (int * int) list), (e2.target :> (int * int) list) with
     (* index are reversed! *)
    | [(0,4)], [(0,1); (0,4); (0,4)], [(0,2); (0,4); (0,4)] -> true
    | _ -> false
  in

  let tags =
    (* The tags *)
    match e1.tag, e2.tag with
     | [], [] -> true
     | _, [] -> e2.pre = []
     | [], _ -> List.for_all (fun f -> not @@ is_nonlocal_fact f) e1.post
     | _, _ -> false
  in
  if debug then Format.eprintf "tags %b@." tags;
  tags &&

  let topology =
    (* The topology around e1.target (= e2.source) *)
    let ins = List.filter (fun e -> e.target = e1.target) edges in
    let outs = List.filter (fun e -> e.source = e1.target) edges in
    match ins, outs with
    | [_], _
    | _, [_] -> true
    | _ -> false
  in
  if debug then Format.eprintf "topo %b@." topology;
  topology &&

  let preconditions_e2 =
    (* The preconditions of [e2]: τ2 has no nonlocal preconditions *)
    not (List.exists is_nonlocal_fact e2.pre)
  in
  if debug then Format.eprintf "prec %b@." preconditions_e2;
  preconditions_e2 &&

  let not_effectful =
    (* The edges must not be both effectful *)
    let effectful e =
      List.exists (fun f -> match f.desc with Loop _ -> false | _ -> true) e.tag
      || List.exists is_nonlocal_fact e.post
    in
    not (effectful e1 && effectful e2)
  in
  if debug then Format.eprintf "not_eff %b@." not_effectful;
  if debug then (
    Format.eprintf "e1: non while %b@."
      (List.exists (fun f -> match f.desc with Loop _ -> false | _ -> true) e1.tag);
    Format.eprintf "e2: non while %b@."
      (List.exists (fun f -> match f.desc with Loop _ -> false | _ -> true) e2.tag);
    Format.eprintf "e1.post %s : %b@." (String.concat ", " (List.map string_of_fact e1.post)) (List.exists is_nonlocal_fact e1.post);
    Format.eprintf "e2.post %s : %b@." (String.concat ", " (List.map string_of_fact e2.post)) (List.exists is_nonlocal_fact e2.post);
  );
  not_effectful &&

  let file_facts =
    (* Even in this case, we avoid merging if both the precondition of τ2
       and the postcondition of τ1 contain file facts. *)
    let has_file_fact fs =
      List.exists (function { desc= File _; _ } -> true | _ -> false) fs
    in
    not (has_file_fact e1.post && has_file_fact e2.pre)
  in
  if debug then Format.eprintf "file %b@." file_facts;
  file_facts &&

  let structure =
    let e2_pre = List.map (Update.update_fact e1.update) e2.pre in
    List.for_all (fun e2_pre_f ->
        match e2_pre_f.desc with
        | Structure { pid; name; address; args=_ } ->
            List.for_all (fun e1_post_f ->
                match e1_post_f.desc with
                | Structure { pid= pid'; name= name'; address= address'; args=_ }
                    when pid = pid' && name = name' ->
                      if eq_expr address address' then true
                      else
                        (* We cannot tell the structures are contractable,
                           therefore the edges cannot be compressed. *)
                        false
                | _ -> true) e1.post
        | _ -> true) e2_pre
  in
  if debug then Format.eprintf "structure %b@." structure;
  structure

let compress (e1 : edge) (e2 : edge) =
  (* facts in [e2] must be substituted by [e1.update] *)
  (* Here we apply [e1.update] to the [e2]'s facts first for easier Structure squahshing *)
  let e2_pre = List.map (Update.update_fact e1.update) e2.pre in
  let e2_tag = List.map (Update.update_fact e1.update) e2.tag in
  let e2_post = List.map (Update.update_fact e1.update) e2.post in

  let id =
    let s = fst e1.id ^ "_" ^ fst e2.id in
    let s = if String.length s > 16 then String.sub s 0 16 else s in
    Ident.local s
  in

  (* fix structure (C. Graph Compression: special case) *)
  let e1_post, (enforces : (Typed.ident * Typed.expr) list), e2_pre =
    List.fold_left (fun (e1_post, enforces, e2_pre) e2_pre_f ->
        match e2_pre_f.desc with
        | Structure { pid; name; address; args } ->
            let e1_post, enforces' =
              List.partition_map (fun e1_post_f ->
                  match e1_post_f.desc with
                  | Structure { pid= pid';  name= name'; address= address'; args= args' }
                    when pid = pid'
                      && name = name' ->
                      assert (eq_expr address address');
                      assert (List.length args = List.length args');
                      let vars =
                        List.map (fun e ->
                            match e.desc with
                            | Ident { id; desc=_; param= None } -> id
                            | _ -> assert false) args
                      in
                      Right (List.combine vars args')
                  | _ -> Left e1_post_f) e1_post
            in
            (match enforces' with
             | [] -> e1_post, enforces, e2_pre_f :: e2_pre
             | _ -> e1_post, List.concat enforces' @ enforces, e2_pre)
        | _ -> e1_post, enforces, e2_pre_f :: e2_pre) (e1.post, [], []) e2_pre
  in
  let e2_pre = List.rev e2_pre in
  let update = Update.override_enforces enforces (Update.compress e1.update e2.update) in
  { id
  ; source = e1.source
  ; source_env = e1.source_env
  ; source_vars = e1.source_vars
  ; pre = e1.pre @ e2_pre
  ; update
  ; tag = e1.tag @ e2_tag (* @ eqs *)
  ; post = e1_post @ e2_post
  ; target = e2.target
  ; target_env = e2.target_env
  ; target_vars = e2.target_vars
  ; loop_back = e2.loop_back
  ; attack = e1.attack || e2.attack
  }

let compress e1 e2 =
  if !debug then (
    Format.eprintf "@[<v2>Compress@ %a@ %a@]@."
      print_edge_summary e1
      print_edge_summary e2
  );
  let e12 = compress e1 e2 in
  if !debug then (
    Format.eprintf "  @[=> %a@]@.@."
      print_edge_summary e12
  );
  e12

(* Topo-sort the edges (ignoring the cycles of course)
   Not really required but good to check the result by human eyes.
*)
let sort_edges edges =
  let sorted_edges_from n =
    List.sort (fun e1 e2 -> Index.compare_lexico e1.target e2.target)
    @@ List.find_all (fun e -> e.source = n) edges
  in
  let rec sort (es : edge list) visited rev_sorted =
    match es with
    | [] -> List.rev rev_sorted
    | e::es when Ident.Set.mem (e.id :> Ident.t) visited ->
        sort es visited rev_sorted
    | e::es ->
        let visited = Ident.Set.add (e.id :> Ident.t) visited in
        let rev_sorted = e :: rev_sorted in
        let es' = sorted_edges_from e.target in
        sort (es' @ es) visited rev_sorted
  in
  sort (sorted_edges_from Index.zero) Ident.Set.empty []

let rec optimize_edges edges =
  (* Code to visit all the pairs of edges.
     Stupid, but runs enough fast even for the camserver example. *)
  let pairs =
    List.concat_map (fun e1 ->
        List.map (fun e2 -> (e1, e2)) edges) edges
  in
  let rec aux = function
    | [] -> edges
    | (e1, e2) :: _ when compressable edges e1 e2 ->
        let e12 = compress e1 e2 in
        let ins = List.filter (fun e -> e.target = e1.target) edges in
        let outs = List.filter (fun e -> e.source = e1.target) edges in
        let edges =
          match ins, outs with
          | [], _ | _, [] -> assert false
          | [_], [_] ->
              (* remove [e1] and [e2] *)
              e12 :: List.filter (fun (e : edge) -> e.id <> e1.id && e.id <> e2.id) edges
          | [_], _ ->
              (* keep [e1] since the other outs than [e2] may depend on it *)
              e12 :: List.filter (fun (e : edge) -> e.id <> e2.id) edges
          | _, [_] ->
              (* keep [e2] since the other ins than [e1] may depend on it *)
              e12 :: List.filter (fun (e : edge) -> e.id <> e1.id) edges
          | _ -> assert false
        in
        (optimize_edges[@tailcall]) edges
    | _ :: pairs -> aux pairs
  in
  sort_edges @@ aux pairs

let optimize_proc proc = { proc with edges = optimize_edges proc.edges }

let optimize_proc_group_desc = function
  | Unbounded proc -> Unbounded (optimize_proc proc)
  | Bounded (p, ps) -> Bounded (p, List.map optimize_proc ps)

let optimize t =
  { t with
    proc_groups = List.map (fun (id, pg) ->
        id, optimize_proc_group_desc pg) t.proc_groups
  }
