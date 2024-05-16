type operator = string
type type_class = CProc | CFsys | CChan
type access_class = CRead |  CWrite | CSend | CRecv 
type attack_class = CEaves |  CTamper | CDrop 
type chan_class = CDatagram | CStream

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

type op = op' Location.located
and op' = 
  | Skip
  | Let of Name.ident * expr
  | Call of Name.ident * Name.ident * expr list
  | If of expr * stmt list * stmt list
  | For of Name.ident * int * int * stmt list

and event = event' Location.located
and event' = 
  | Event of Name.ident * ((Name.ident * bool) list)

and stmt = stmt' Location.located
and stmt' = 
  | OpStmt of op
  | EventStmt of op * event list

type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident

type fpath = fpath' Location.located
and fpath' = 
  | Fpath of (Name.ident * expr * Name.ident)

type prop = prop' Location.located
and prop' =
  | True

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

type sys = sys' Location.located
and sys' = 
  | Sys of proc list * lemma list

type datatype = datatype' Location.located
and datatype' = 
  | DInt
  | DString
  | DBool

type decl = decl' Location.located
and decl' =
  | DeclPrimFun of Name.ident * (datatype list) * datatype
  | DeclPrimEq of expr * expr
  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident * (access_class list)
  | DeclAttack of Name.ident * (attack_class list)
  | DeclInit of Name.ident * expr
  | DeclFsys of Name.ident * (fpath list)
  | DeclChan of Name.ident * chan_class * Name.ident
  | DeclProc of Name.ident * (Name.ident list) * Name.ident * 
                ((Name.ident * expr) list) * 
                (Name.ident * (Name.ident list) * stmt list * Name.ident) list* 
                stmt list
