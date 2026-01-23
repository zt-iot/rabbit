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

let vars_of_expr e =
  let rec aux e =
    match e.desc with
    | Ident { id; param= None; desc= Var } -> [id]
    | Ident { id; param= Some p; desc= Var } -> id :: aux p
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
  | Return of expr
  | New of ident * (name * expr list) option * cmd
  | Get of ident list * expr * name * cmd
  | Del of expr * name
  | Assume of fact list * cmd

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
      ; arity : int
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
