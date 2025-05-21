type indexed_var = Name.ident * int * int * int
type operator = string

val index_var : Name.ident -> int * int * int -> indexed_var
val indexed_underscore : indexed_var

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
  | Float of string
  | Apply of operator * expr list
  | Tuple of expr list
  | Channel of string * Name.ident
  | Path of string
  | Process of string
  | ParamChan of string * expr
  | ParamConst of string * expr
  | Param of string

type fact = fact' Location.located

and fact' =
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list
  | ResFact of int * expr list

type 'cmd case = string list * fact list * 'cmd

type cmd = cmd' Location.located

and cmd' =
  | Skip
  (** doing nothing *)
  | Sequence of cmd * cmd
  (** sequencing, c1; c2 *)
  | Put of fact list
  (** output, put[f1,..,fn] *)
  | Let of Name.ident * expr * cmd
  (** let binding, let x = e in c *)
  | Assign of (Name.ident * (int * bool)) * expr
  (** assignment, x := e *)
  | FCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  (** function call, x := f(e1,..,en) *)
  | SCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  (** syscall call, x := s(e1,..,en) *)
  | Case of cmd case list
  (** guarded cases, case [a1s] => c1 | .. | [ans] => cn end *)
  | While of cmd case list * cmd case list
  (** guarded loop,
      repeat [a1s] => c1 | .. | [ans] => cn
      until [a'1s] => c'1 | .. | [a'ms] => c'm
      end
  *)
  | Event of fact list
  (** tag, event[T] *)
  | Return of expr
  (** return *)
  | New of Name.ident * Name.ident * expr list * cmd
  (** allocation, new x := S(e1,..en) in c *)
  | Get of Name.ident list * expr * Name.ident * cmd
  (** fetch, let x1,..,xn := e.S in c *)
  | Del of expr * Name.ident
  (** deletion , delete e.S *)

type chan_arg =
  | ChanArgPlain of string * string
  | ChanArgParam of string * string
  | ChanArgParamInst of string * expr * string

(** Lemma *)
type lemma = lemma' Location.located
and lemma' =
  | PlainLemma of Name.ident * Name.ident
  | ReachabilityLemma of
      Name.ident * Name.ident list * Name.ident list * Name.ident list * fact list
  | CorrespondenceLemma of Name.ident * Name.ident list * fact * fact
