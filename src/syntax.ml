type indexed_var = Name.ident * int * int * int
type operator = string 
let index_var s (i, j, k) = (s, i, j, k)
let indexed_underscore = ("",-1,-1, -1)

type expr = expr' Location.located
and expr' =
  | Const of Name.ident
  | ExtConst of Name.ident
  | Variable of string
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

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of Name.ident * Name.ident * expr list
  | PathFact of Name.ident * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list



(* meta vars, local vars, top-level variables *)
type local_typing_context = (Name.ident list) list * Name.ident list list

type cmd = local_typing_context * cmd' Location.located
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  | Wait of fact list * cmd
  | Put of fact list
  | Let of Name.ident * expr 
  | Assign of Name.ident * expr
  | FCall of Name.ident option * Name.ident * expr list
  | SCall of Name.ident option * Name.ident * expr list
  | Case of fact list * cmd * fact list * cmd 
  | While of fact list * fact list * cmd
  | Event of fact list


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

