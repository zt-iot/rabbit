type indexed_var = Name.ident * int * int
type operator = string 
let index_var s (i, j) = (s, i, j)
let indexed_underscore = ("",-1,-1)

type expr = expr' Location.located
and expr' =
  | Const of Name.ident
  | ExtConst of Name.ident
  | Variable of indexed_var
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list
  | Channel of string * Input.access_class list * Input.chan_class list 
  | FrVariable of string

type instruction = 
  | IRead | IWrite | IInvoke | IRecv | ISend | IOpen | IClose | ICloseConn | IConnect | IAccept


type atomic_stmt = atomic_stmt' Location.located
and atomic_stmt' = 
  | Skip
  | Let of indexed_var * expr
  | Call of indexed_var * Name.ident * expr list
  | Instruction of indexed_var * instruction * expr list
  | If of expr * stmt list * stmt list
  | For of indexed_var * int * int * stmt list

and event = event' Location.located
and event' = 
  | Event of Name.ident * (expr list)

and stmt = stmt' Location.located
and stmt' = 
  | OpStmt of atomic_stmt
  | EventStmt of atomic_stmt * event list


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

let string_of_type_class c = 
   match c with 
   | Input.CProc -> "Proc"
   | Input.CFsys -> "Fsys" 
   | Input.CChan -> "Chan"

let string_of_chan_class c = 
   match c with 
   | Input.CDatagram -> "datagram"
   | Input.CStream -> "stream"

let string_of_access_class a = 
   match a with
   | Input.CRead -> "read"
   | Input.CWrite -> "write"
   | Input.CSend -> "send"
   | Input.CRecv -> "recv"

let string_of_attack_class a = 
   match a with
   | Input.CEaves -> "Eaves" 
   | Input.CTamper -> "Tamper"
   | Input.CDrop  -> "Drop"
