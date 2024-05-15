type operator = string
type type_class = CProc | CFsys | CChan
type access_class = CRead |  CWrite | CSend | CRecv 
type attack_class = CEaves |  CTamper | CDrop 
type chan_class = CDatagram | CStream

type decl = decl' Location.located
and decl' =
  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident * (access_class list)
  | DeclAttack of Name.ident * (attack_class list)
  | DeclInit of Name.ident * expr
  | DeclFsys of Name.ident * (fpath list)
  | DeclChan of Name.ident * chan_class * Name.ident
  | DeclProc of Name.ident * (Name.ident list) * Name.ident * ((Name.ident * expr) list) * (Name.ident * (Name.ident list) * comp) * comp 

type fpath = fpath' Location.located
and fpath' = 
  | Fpath of (Name.ident * expr * Name.ident)

type sys = sys' Location.located
and sys' = 
  | Sys of proc list * assert list

type assert = assert' Location.located
and assert' =
  | Assert of Name.ident * prop 

type prop = prop' Location.located
and prop' =
  | True

type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident

type expr = expr' Location.located
and expr' =
  | Var of Name.ident
  | Boolean of bool
  | Integer of Mpzf.t
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list

type op = op' Location.located
and op' = 
  | Skip
  | Let of Name.ident * expr
  | Call of Name.ident * expr list
  | If of expr * op list * op list
  | For of Name.ident * nat * nat * op list

type event = event' Location.located
and event' = 
  | Name.ident * ((Name.ident * bool) list)

type stmt = stmt' Location.located
and stmt' = 
  | OpStmt of op
  | EventStmt of op * event * event list

