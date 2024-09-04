type operator = string
type type_class = CProc | CFsys | CChan
type attack_class = CEaves |  CTamper | CDrop 
type arg_type = TyValue | TyChannel

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

type atomic_stmt = atomic_stmt' Location.located
and atomic_stmt' = 
  | Skip
  | Let of Name.ident * expr
  | LetUnderscore of expr
  (* | Call of Name.ident * Name.ident * expr list *)
  | If of expr * stmt list * stmt list
  | For of Name.ident * int * int * stmt list

and event = event' Location.located
and event' = 
  | Event of Name.ident * (expr list)

and stmt = stmt' Location.located
and stmt' = 
  | OpStmt of atomic_stmt
  | EventStmt of atomic_stmt * event list

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | LocalFact of Name.ident * Name.ident * expr list

type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident

type prop = prop' Location.located
and prop' =
  | PlainString of string

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  | DeclExtEq of expr * expr
  | DeclExtSyscall of Name.ident * (arg_type * Name.ident) list * (fact list * fact list) list * expr option
  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident list * Name.ident list
  | DeclAttack of Name.ident * (attack_class list)
  | DeclInit of Name.ident * expr
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of Name.ident * Name.ident
  | DeclProc of Name.ident * (Name.ident list) * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * stmt list * Name.ident) list * 
                stmt list
  | DeclSys of proc list * lemma list 

