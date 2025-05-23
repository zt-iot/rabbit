type operator = string

(* XXX unused
type indexed_var = Name.ident * int * int * int
val index_var : Name.ident -> int * int * int -> indexed_var
val indexed_underscore : indexed_var
*)

type expr = expr' Location.located

and expr' =
  | Const of Name.ident
  | ExtConst of Name.ident
  | TopVariable of string * int
  | LocVariable of string * int
  | MetaVariable of string * int
  | MetaNewVariable of string * int
  | Boolean of bool
  (** boolean, [true]/[false] *)
  | String of string
  (** string, ["hello"] *)
  | Integer of int
  (** integer, [42] *)
  | Float of string (* store the string so we can correctly round later *)
  (** float, [4.12] *)
  | Apply of operator * expr list
  (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list
  (** tuple, [(e1,..,en)] *)
  | Channel of string * Name.ident (* second field records necessary permissions.. *)
  | Path of string  (* only needed for syscall defintions *)
  | Process of string (* only needed for syscall defintiions *)
  (* | Run of string * expr list (* only needed for syscall defintiions *) *)
  (* | FrVariable of string *)
  | ParamChan of string * expr
  (** id<e> *)
  | ParamConst of string * expr
  (** id<e> *)
  | Param of string

type fact = fact' Location.located

and fact' =
  | Fact of Name.ident * expr list
  (** [n(e1,..,en)] *)
  | GlobalFact of Name.ident * expr list
  (** [:: n(e1,..,en) ]*)
  | ChannelFact of expr * Name.ident * expr list
  (** [e :: n(e1,..,en)] *)
  | ProcessFact of Name.ident * Name.ident * expr list
  (** [e % n(e1,..,en)] *)
  | EqFact of expr * expr (** e1 = e2 *)
  | NeqFact of expr * expr (** e1 != e2 *)
  | FileFact of expr * expr (** S.e *)

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
