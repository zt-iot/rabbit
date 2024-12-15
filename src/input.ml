type operator = string
type type_class = CProc | CFsys | CChan
type arg_type = TyValue | TyChannel | TyProcess | TyPath

type expr = expr' Location.located
and expr' =
  | Var of Name.ident
  | Boolean of bool
  | String of string  
  (* | Integer of Mpzf.t *)
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of Name.ident * Name.ident * expr list
  | PathFact of Name.ident * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list

type cmd = cmd' Location.located
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  | Wait of fact list * cmd
  | Put of fact list
  | Let of Name.ident * expr * cmd 
  | Assign of Name.ident option * expr
  | Case of cmd * cmd 
  | While of cmd * cmd
  | Event of fact list
  | Return of expr

type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident option

type prop = prop' Location.located
and prop' =
  | PlainString of string
  | Reachability of fact list
  | Correspondence of fact * fact

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  | DeclExtEq of expr * expr
  | DeclExtSyscall of Name.ident * (arg_type * Name.ident) list * cmd
  | DeclExtAttack of Name.ident * (arg_type * Name.ident) * (fact list * fact list) 
  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident list * Name.ident list
  | DeclAttack of Name.ident list * Name.ident list
  | DeclInit of Name.ident * expr option
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of Name.ident * Name.ident
  | DeclProc of Name.ident * (Name.ident * Name.ident) list * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * cmd) list * cmd
  | DeclSys of proc list * lemma list 
  | DeclLoad of string

