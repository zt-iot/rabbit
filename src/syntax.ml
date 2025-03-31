type indexed_var = Name.ident * int * int * int
type operator = string 
let index_var s (i, j, k) = (s, i, j, k)
let indexed_underscore = ("",-1,-1, -1)

type expr = expr' Location.located
and expr' =
  | Const of Name.ident
  | ExtConst of Name.ident
  | TopVariable of string * int
  | LocVariable of string * int
  | MetaVariable of string * int
  | MetaNewVariable of string * int
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list
  | Channel of string * Name.ident (* second field records necessary permissions.. *) 
  | Path of string  (* only needed for syscall defintiions *) 
  | Process of string (* only needed for syscall defintiions *)
  (* | Run of string * expr list (* only needed for syscall defintiions *) *)
  (* | FrVariable of string *)
  | ParamChan of string * expr 
  | ParamConst of string * expr

  | Param of string

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | PathFact of expr * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list
  | ResFact of int * expr list



(* meta vars, local vars, top-level variables *)
(* type local_typing_context = Name.ident list * Name.ident list * Name.ident list *)

type cmd = cmd' Location.located
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  | Put of fact list
  | Let of Name.ident * expr * cmd
  | Assign of (Name.ident * (int * bool)) * expr (* (k, true) : k'th in top-level (k, false): k'th in local *)
  | FCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  | SCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  | Case of (string list * fact list * cmd) list
  | While of (string list * fact list * cmd) list * (string list * fact list * cmd) list
  | Event of fact list
  | Return of expr

  | New of Name.ident * Name.ident * expr list * cmd 
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident



type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident

type fpath = fpath' Location.located
and fpath' = 
  | Fpath of (Name.ident * expr * Name.ident)

type lemma = lemma' Location.located
and lemma' = 
  | PlainLemma of Name.ident * Name.ident  
  | ReachabilityLemma of Name.ident * Name.ident list * fact list
  | CorrespondenceLemma of Name.ident * Name.ident list * fact * fact 

