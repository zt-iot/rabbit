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

  | Param of Name.ident * expr

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of expr * Name.ident * expr list
  | ResFact of int * expr list (* 0: eq 1: neq 3 : FILE*)
  (* | InjFact of  *)

type cmd = cmd' Location.located
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  (* | Wait of fact list * cmd *)
  | Put of fact list
  | Let of Name.ident * expr * cmd 
  | Assign of Name.ident option * expr
  | Case of (fact list * cmd) list
  | While of (fact list * cmd) list * (fact list * cmd) list
  | Event of fact list
  | Return of expr

  | New of Name.ident * Name.ident * expr list * cmd 
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident

type chan_arg =
  | ChanArgPlain of Name.ident
  | ChanArgParam of Name.ident
  | ChanArgParamInst of Name.ident * expr



type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * (chan_arg list)
  | ParamProc of Name.ident * expr * (chan_arg list)

type proc = 
| UnboundedProc of pproc 
| BoundedProc of (Name.ident * pproc list)


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
  | DeclExtAttack of Name.ident * Name.ident * (arg_type * Name.ident) list * cmd
  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  | DeclAttack of Name.ident list * Name.ident list
  | DeclInit of Name.ident * expr option
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of Name.ident * Name.ident
  | DeclProc of Name.ident * (bool * Name.ident * Name.ident) list * Name.ident * 
                ((expr * Name.ident * expr) list) * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * cmd) list * cmd
  | DeclParamProc of Name.ident * Name.ident * (bool * Name.ident * Name.ident) list * Name.ident * 
                ((expr * Name.ident * expr) list) * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * cmd) list * cmd
  | DeclSys of proc list * lemma list 
  | DeclLoad of string

  | DeclParamInit of Name.ident * (Name.ident * expr) option
  | DeclParamChan of Name.ident * Name.ident
