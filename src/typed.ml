type name = Name.t
type ident = Ident.t

type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  ; env : Env.t
  }

type expr = expr' loc_env

and expr' =
  | Ident of
      { id : ident
      ; desc : Env.desc
      ; param : expr option
      }
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string
  | Apply of ident * expr list
  | Tuple of expr list
  | Unit

let rec string_of_expr (e : expr) =
  match e.desc with
  | Ident { id; param= None; _ } -> Ident.to_string id
  | Ident { id; param= Some p; _ } -> Printf.sprintf "%s<%s>" (Ident.to_string id) (string_of_expr p)
  | Apply (f, es) -> Printf.sprintf "%s(%s)" (Ident.to_string f) (String.concat ", " @@ List.map string_of_expr es)
  | Tuple es -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map string_of_expr es
  | String s -> Printf.sprintf "%S" s
  | Integer i -> string_of_int i
  | Float f -> f
  | Boolean b -> string_of_bool b
  | Unit -> "()"

type subst = (ident * expr) list

let rec equal_expr (e1 : expr) (e2 : expr) =
  match e1.desc, e2.desc with
  | Ident { id= id1; desc= desc1; param= param1 }, Ident { id= id2; desc= desc2; param= param2 } ->
      id1 = id2
      && desc1 = desc2
      && (
        match param1, param2 with
        | None, None -> true
        | Some p1, Some p2 -> equal_expr p1 p2
        | _ -> false
      )
  | Boolean b1, Boolean b2 -> b1 = b2
  | String s1, String s2 -> s1 = s2
  | Integer i1, Integer i2 -> i1 = i2
  | Float f1, Float f2 -> f1 = f2
  | Apply (f1, es1), Apply (f2, es2) ->
      f1 = f2
      && List.length es1 = List.length es2
      && List.for_all2 equal_expr es1 es2
  | Tuple es1, Tuple es2 ->
      List.length es1 = List.length es2
      && List.for_all2 equal_expr es1 es2
  | Unit, Unit -> true
  | _ -> false

let rec apply_subst (s : subst) (e : expr) : expr =
  match e.desc with
  | Ident { id; desc= Var _; param= None } ->
      Option.value ~default:e (List.assoc_opt id s)
  | Ident { id; desc; param= Some p } ->
      { e with desc= Ident { id; desc; param= Some (apply_subst s p) } }
  | Ident _ -> e
  | Apply (f, es) -> { e with desc= Apply (f, List.map (apply_subst s) es) }
  | Tuple es -> { e with desc= Tuple (List.map (apply_subst s) es) }
  | Boolean _ | String _ | Integer _ | Float _ | Unit -> e

let rec occurs (id : ident) (e : expr) =
  match e.desc with
  | Ident { id= id'; desc= Var _; param= None } -> id = id'
  | Ident { param= Some p; _ } -> occurs id p
  | Ident _ -> false
  | Apply (_, es) | Tuple es -> List.exists (occurs id) es
  | Boolean _ | String _ | Integer _ | Float _ | Unit -> false

let bind_var (s : subst) (id : ident) typ (e : expr) : subst option =
  let e = apply_subst s e in
  let self = { e with desc= Ident { id; desc= Var typ; param= None } } in
  if equal_expr self e then Some s
  else if occurs id e then None
  else
    let s = List.map (fun (id', e') -> id', apply_subst [id, e] e') s in
    Some ((id, e) :: s)

let unify_expr (e1 : expr) (e2 : expr) : subst option =
  let rec aux (s : subst) = function
    | [] -> Some s
    | (e1, e2) :: rest ->
        let e1 = apply_subst s e1 in
        let e2 = apply_subst s e2 in
        if equal_expr e1 e2 then aux s rest
        else
          match e1.desc, e2.desc with
          | Ident { id; desc= Var typ; param= None }, _ ->
              begin
                match bind_var s id typ e2 with
                | None -> None
                | Some s -> aux s rest
              end
          | _, Ident { id; desc= Var typ; param= None } ->
              begin
                match bind_var s id typ e1 with
                | None -> None
                | Some s -> aux s rest
              end
          | Ident { id= id1; desc= desc1; param= param1 }, Ident { id= id2; desc= desc2; param= param2 }
            when id1 = id2 && desc1 = desc2 ->
              begin
                match param1, param2 with
                | None, None -> aux s rest
                | Some p1, Some p2 -> aux s ((p1, p2) :: rest)
                | _ -> None
              end
          | Boolean b1, Boolean b2 when b1 = b2 -> aux s rest
          | String s1, String s2 when s1 = s2 -> aux s rest
          | Integer i1, Integer i2 when i1 = i2 -> aux s rest
          | Float f1, Float f2 when f1 = f2 -> aux s rest
          | Apply (f1, es1), Apply (f2, es2)
            when f1 = f2 && List.length es1 = List.length es2 ->
              aux s (List.combine es1 es2 @ rest)
          | Tuple es1, Tuple es2
            when List.length es1 = List.length es2 ->
              aux s (List.combine es1 es2 @ rest)
          | Unit, Unit -> aux s rest
          | _ -> None
  in
  aux [] [e1, e2]

let type_of_expr (expr : expr) =
  match expr.desc with
  | Ident { desc; _ } -> Option.get (Env.type_of_desc desc)
  | Apply (id, _) ->
      let desc = Option.get @@ Env.find_opt_by_id expr.env id in
      (Option.get (Env.callable_type_of_desc desc)).result_type
  | Boolean _ | String _ | Integer _ | Float _ | Tuple _ | Unit -> Type.TValue

let vars_of_expr e =
  let rec aux e =
    match e.desc with
    | Ident { id; param= None; desc= Var _ } -> [id]
    | Ident { id; param= Some p; desc= Var _ } -> id :: aux p
    | Ident { id=_; param= Some p; desc= _ } -> aux p
    | Ident _ -> []
    | Apply (_, es) | Tuple es -> List.concat_map aux es
    | String _ | Integer _ | Float _ | Boolean _ | Unit -> []
  in
  List.sort_uniq compare @@ aux e

let rec constants (e : expr) =
  match e.desc with
  | Ident { id= _; desc= Const false; param= None } -> [e]
  | Ident { id= _; desc= Const true; param= Some e' } -> e :: constants e'
  | Ident { id= _; desc= Const _; param= _ } -> assert false
  | Ident _ -> []
  | Boolean _ | String _ | Integer _ | Float _ | Unit -> []
  | Apply (_, es) | Tuple es -> List.concat_map constants es

type loop_mode =
  | In
  | Back
  | Out

let string_of_loop_mode = function
  | In -> "In"
  | Back -> "Back"
  | Out -> "Out"

type fact = fact' loc_env

and fact' =
  | Channel of
      { channel : expr
      ; name : name
      ; args : expr list
      }
  | Plain of name * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      }
  | Global of string * expr list

type cmd = cmd' loc_env

and case =
  { fresh : ident list
  ; facts : fact list
  ; cmd : cmd
  }

and cmd' =
  | Skip
  | Sequence of cmd * cmd
  | Put of fact list
  | Let of ident * expr * cmd
  | Assign of ident option * expr
  | Case of case list
  | While of case list * case list
  | Event of fact list
  | Expr of expr
  | New of ident * (name * expr list) option * cmd
  | Get of ident list * expr * name * cmd
  | Del of expr * name

let rec type_of_cmd (cmd : cmd) =
  match cmd.desc with
  | Expr expr -> type_of_expr expr
  | Sequence (_, cmd2) -> type_of_cmd cmd2
  | Let (_, _, body) | New (_, _, body) | Get (_, _, _, body) -> type_of_cmd body
  | Case ({ cmd; _ } :: _) -> type_of_cmd cmd
  | Case [] | While _ | Skip | Put _ | Assign _ | Event _ | Del _ -> Type.TValue

type chan_param = { channel : ident; param : unit option; typ : ident }

type chan_arg =
  { channel : ident
  ; parameter : expr option option
  ; typ : ident
  }

type proc = proc' Location.located

and proc' =
  { id : ident
  ; parameter : expr option
  ; args : chan_arg list
  }

type proc_group_desc =
  | Unbounded of proc
  | Bounded of ident * proc list

type lemma = lemma' loc_env

and lemma' =
  | Plain of string
  | Reachability of
      { fresh : ident list
      ; facts : fact list
      }
  | Correspondence of
      { fresh : ident list
      ; premise : fact
      ; conclusion : fact
      }

type init_desc =
  | Value of expr
  | Value_with_param of ident * expr
  | Fresh
  | Fresh_with_param

type decl = decl' loc_env

and decl' =
  | Function of
      { id : ident
      ; typ : Type.callable_type
      }
  | Equation of expr * expr
  | Syscall of
      { id : ident
      ; args : ident list
      ; cmd : cmd
      ; attack : bool
      }
  | Attack of
      { id : ident
      ; syscall : ident
      ; args : ident list
      ; cmd : cmd
      }
  | Type of
      { id : ident
      ; typclass : Input.type_class
      }
  | Allow of
      { process_typ : ident
      ; target_typs : ident list
      ; syscalls : ident list option
      }
  | AllowAttack of
      { process_typs : ident list
      ; attacks : ident list
      }
  | Init of (* naming... Const is better? *)
      { id : ident
      ; desc : init_desc
      }
  | Channel of
      { id : ident
      ; param : unit option
      ; typ : ident
      }
  | Process of
      { id : ident
      ; param : ident option
      ; args : chan_param list
      ; typ : ident
      ; files : (expr * ident * expr) list
      ; vars : (ident * expr) list
      ; funcs : (ident * ident list * cmd) list
      ; main : cmd
      }
  | System of proc_group_desc list * (Ident.t * lemma) list
  | Load of string * decl list
