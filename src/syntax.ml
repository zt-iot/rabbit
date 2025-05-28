type operator = string

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
  | Path of string  (* only needed for syscall defintions *)
  | Process of string (* only needed for syscall defintiions *)
  | ParamChan of string * expr
  | ParamConst of string * expr
  | Param of string

type fact = fact' Location.located
and fact' =
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list
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
  | Assign of (Name.ident * (int * bool)) * expr (* (k, true) : k'th in top-level (k, false): k'th in local *)
  | FCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  | SCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  | Case of cmd case list
  | While of cmd case list * cmd case list
  | Event of fact list
  | Return of expr
  | New of Name.ident * (Name.ident * expr list) option * cmd
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident

(* last one is type` *)
type chan_arg =
  | ChanArgPlain of string * string
  | ChanArgParam of string * string
  | ChanArgParamInst of string * expr * string

type lemma = lemma' Location.located
and lemma' =
  | PlainLemma of Name.ident * Name.ident
  | ReachabilityLemma of Name.ident * Name.ident list * Name.ident list * Name.ident list * fact list
  | CorrespondenceLemma of Name.ident * Name.ident list * fact * fact
