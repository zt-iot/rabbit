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

type atomic_stmt = atomic_stmt' Location.located
and atomic_stmt' = 
  | Skip
  | Let of Name.ident * expr * bool
  | LetUnderscore of expr
  (* | Call of Name.ident * Name.ident * expr list *)
  | If of expr * expr * stmt list * stmt list
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
  | ChannelFact of Name.ident * Name.ident * expr list
  | PathFact of Name.ident * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list

type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident option

type prop = prop' Location.located
and prop' =
  | PlainString of string
  | Reachability of event list
  | Correspondence of event * event

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

type complex_rule = complex_rule' Location.located
and complex_rule' = 
  | CRule of (fact list * fact list) 
  | CRuleStmt of (fact list * stmt list * fact list) 
  | CRulePar of complex_rule * complex_rule
  | CRuleRep of complex_rule 
  | CRuleSeq of complex_rule * complex_rule 

type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  | DeclExtEq of expr * expr
  | DeclExtSyscall of Name.ident * (arg_type * Name.ident) list * (Name.ident * expr) list * complex_rule * expr option
  | DeclExtAttack of Name.ident * (arg_type * Name.ident) * (fact list * fact list) 
  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident list * Name.ident list
  | DeclAttack of Name.ident list * Name.ident list
  | DeclInit of Name.ident * expr option
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of Name.ident * Name.ident
  | DeclProc of Name.ident * (Name.ident list) * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * stmt list * Name.ident) list * 
                stmt list
  | DeclSys of proc list * lemma list 
  | DeclLoad of string

