type operator = Name.ident

type variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param

let string_of_variable_desc = function
  | Top i -> Printf.sprintf "Top %d" i
  | Loc i -> Printf.sprintf "Loc %d" i
  | Meta i -> Printf.sprintf "Meta %d" i
  | MetaNew i -> Printf.sprintf "MetaNew %d" i
  | Param -> "Param"

type expr = expr' Location.located
and expr' =
  | Const of Name.ident * expr option
  | ExtConst of Name.ident
  | Variable of string * variable_desc
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string
  | Apply of operator * expr list
  | Tuple of expr list
  | Channel of Name.ident * expr option

type fact = fact' Location.located
and fact' =
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of expr * Name.ident * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | FileFact of expr * expr

type 'cmd case = string list * fact list * 'cmd

type cmd = cmd' Location.located
and cmd' =
  | Skip
  | Sequence of cmd * cmd
  | Put of fact list
  | Let of Name.ident * expr * cmd
  | Assign of (Name.ident * variable_desc) * expr
  | FCall of (Name.ident * variable_desc) option * Name.ident * expr list
  | SCall of (Name.ident * variable_desc) option * Name.ident * expr list
  | Case of cmd case list
  | While of cmd case list * cmd case list
  | Event of fact list
  | Return of expr
  | New of Name.ident * (Name.ident * expr list) option * cmd
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident

type chan_arg = ChanArg of { id : Name.ident; param : expr option option; typ : Name.ident }

type chan_param = Input.chan_param = ChanParam of { id : Name.ident; param : unit option; typ : Name.ident }

type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * expr option * (chan_arg list)

type proc =
| UnboundedProc of pproc
| BoundedProc of (Name.ident * pproc list)

type lemma = lemma' Location.located
and lemma' =
  | PlainLemma of { name : Name.ident; desc : string }
  | ReachabilityLemma of { name : Name.ident; fresh_variables : Name.ident list; facts : fact list }
  | CorrespondenceLemma of { name : Name.ident; fresh_variables : Name.ident list; premise : fact; conclusion : fact }

type init_desc =
  | Fresh
  | Value of expr
  | Value_with_param of expr * Name.ident
  | Fresh_with_param



type decl = decl' Location.located
and decl' =
  | DeclEqThyFunc of Name.ident * int
  | DeclEqThyEquation of expr * expr
  | DeclExtSyscall of Name.ident * Name.ident list * cmd
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd
  | DeclType of Name.ident * Input.rabbit_typ
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  | DeclAttack of Name.ident list * Name.ident list
  | DeclInit of Name.ident * init_desc
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of chan_param
  | DeclProc of { id : Name.ident
                ; param : Name.ident option
                ; args : chan_param list
                ; typ : Name.ident
                ; files : (expr * Name.ident * expr) list
                ; vars : (Name.ident * expr) list
                ; funcs : (Name.ident * (Name.ident list) * cmd) list
                ; main : cmd }
  | DeclSys of proc list * lemma list
  | DeclLoad of string * decl list
