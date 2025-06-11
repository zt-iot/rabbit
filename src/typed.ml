type name = Name.ident
type ident = Ident.t

type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  ; env : Env.t
  }

type expr = expr' loc_env

and expr' =
  | Ident of { id : ident; desc : Env.desc; param : expr option }
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string
  | Apply of ident * expr list
  | Tuple of expr list
  | Unit
  | Rho

type fact = fact' loc_env

and fact' =
  | Structure of string * expr list
  | Global of string * expr list
  | Channel of expr * string * expr list
  | Process of expr * string * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of expr * expr
  | Fresh of expr

type cmd = cmd' loc_env

and case = { fresh : ident list; facts : fact list; cmd : cmd }

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

type chan_arg = {
  channel: ident;
  parameter : expr option option;
  typ : ident;
}

type pproc = pproc' Location.located
and pproc' = {
  id : ident;
  parameter : expr option;
  args : chan_arg list
}

type proc =
  | Unbounded of pproc
  | Bounded of (ident * pproc list)

type lemma = lemma' loc_env

and lemma' =
  | Plain of string
  | Reachability of { fresh : ident list; facts : fact list }
  | Correspondence of { fresh : ident list; from : fact; to_ : fact }

type init_desc =
  | Value of expr
  | Value_with_param of ident * expr
  | Fresh
  | Fresh_with_param

type decl = decl' loc_env
and decl' =
  | Function of { id : ident; arity : int  }
  | Equation of expr * expr
  | Syscall of { id : ident; args : ident list; cmd : cmd }
  | Attack of { id : ident; syscall : ident; args : ident list; cmd : cmd }
  | Type of { id : ident; typclass : Input.type_class }
  | Allow of { process_typ : ident; target_typs : ident list; syscalls : ident list option }
  | AllowAttack of { process_typs : ident list; attacks : ident list }
  | Init of { id : ident; desc : init_desc }
  | Channel of { id : ident; param : unit option; typ : ident }
  | Process of { id : ident
                ; param : ident option
                ; args : (bool * ident * ident) list
                ; typ : ident
                ; files : (expr * ident * expr) list
                ; vars : (ident * expr) list
                ; funcs : (ident * (ident list) * cmd) list
                ; main : cmd }
  | System of proc list * (Ident.t * lemma) list
  | Load of string * decl list
