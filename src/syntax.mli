type operator = string

type expr = expr' Location.located

and expr' =
  | Const of Name.ident (** const by [const n = e] or [const fresh n] *)
  | ExtConst of Name.ident (** ext function by [function f:0] *)
  | TopVariable of string * int (** variables by [var ...] in process definition *)
  | LocVariable of string * int (** local variables by function arguments, etc. *)
  | MetaVariable of string * int (** variables introduced by [new] and [let x1,...,xn := e.S in ...] *)
  | MetaNewVariable of string * int (** pattern variables in cases and free variables in lemmas *)
  | Boolean of bool (** boolean, [true]/[false] *)
  | String of string (** string, ["hello"] *)
  | Integer of int (** integer, [42] *)
  | Float of string (** float, [4.12]. Store the string so we can correctly round later *)
  | Apply of operator * expr list (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list (** tuple, [(e1,..,en)] *)
  | Channel of Name.ident * Name.ident (** channel name and type *)
  (* | Path of string (* only needed for syscall defintions *) *)
  | Process of string (* only needed for syscall defintiions *)
  | ParamChan of string * expr (** id<e> *)
  | ParamConst of string * expr (** id<e> *)
  | Param of string

type fact = fact' Location.located

and fact' =
  | Fact of Name.ident * expr list (** [n(e1,..,en)] *)
  | GlobalFact of Name.ident * expr list (** [:: n(e1,..,en) ]*)
  | ChannelFact of expr * Name.ident * expr list (** [e :: n(e1,..,en)] *)
  | ProcessFact of Name.ident * Name.ident * expr list (** [e % n(e1,..,en)] *)
  | EqFact of expr * expr (** e1 = e2 *)
  | NeqFact of expr * expr (** e1 != e2 *)
  | FileFact of expr * expr (** S.e *)

type 'cmd case = string list * fact list * 'cmd

type cmd = cmd' Location.located

and cmd' =
  | Skip (** doing nothing *)
  | Sequence of cmd * cmd (** sequencing, c1; c2 *)
  | Put of fact list (** output, put[f1,..,fn] *)
  | Let of Name.ident * expr * cmd (** let binding, let x = e in c *)
  | Assign of (Name.ident * (int * bool)) * expr (** assignment, x := e *)
  | FCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  (** function call, x := f(e1,..,en) *)
  | SCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  (** syscall call, x := s(e1,..,en) *)
  | Case of cmd case list (** guarded cases, case [a1s] => c1 | .. | [ans] => cn end *)
  | While of cmd case list * cmd case list
  (** guarded loop,
      repeat [a1s] => c1 | .. | [ans] => cn
      until [a'1s] => c'1 | .. | [a'ms] => c'm
      end
  *)
  | Event of fact list (** tag, event[T] *)
  | Return of expr (** return *)
  | New of Name.ident * (Name.ident * expr list) option * cmd
  (** allocation, new x := S(e1,..en) in c *)
  | Get of Name.ident list * expr * Name.ident * cmd
  (** fetch, let x1,..,xn := e.S in c *)
  | Del of expr * Name.ident (** deletion , delete e.S *)

type chan_arg =
  | ChanArgPlain of string * string
  | ChanArgParam of string * string
  | ChanArgParamInst of string * expr * string

type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * expr option * (chan_arg list)

type proc =
| UnboundedProc of pproc
| BoundedProc of (Name.ident * pproc list)

(** Lemma *)
type lemma = lemma' Location.located
and lemma' =
  | PlainLemma of Name.ident * string
  | ReachabilityLemma of
      Name.ident * Name.ident list * Name.ident list * Name.ident list * fact list
  | CorrespondenceLemma of Name.ident * Name.ident list * fact * fact

type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  (** external function, [function id : arity] *)
  | DeclExtEq of expr * expr
  (** external equation, [equation e1 = e2] *)
  | DeclExtSyscall of Name.ident * Name.ident list * cmd
  (** system call, [syscall f(a1,..,an) { c }]
                   [passive attack f(ty1 a1,..,tyn an) { c }]
      XXX what is passive attack for?  It is not distinguishable from syscall in Input.
  *)
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd
  (** [attack f on name (a1,..,an) { c }] *)
  | DeclType of Name.ident * Input.type_class
  (** type declaration, [type t : filesys/process/channel] *)
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  (** [allow s t1 .. tn [f1, .., fm]]
      [allow s t1 .. tn [.]]  for all the syscalls

      XXX the list [ti] is either empty or singleton.  Should use option type?
  *)
  | DeclAttack of Name.ident list * Name.ident list
  (** [allow attack t1 .. tn [f1, .., fm]] *)
  | DeclInit of Name.ident * expr option
  (** [const n = e]
      [const fresh n]
  *)
  | DeclParamInit of Name.ident * (Name.ident * expr) option
  (** - [const n<p> = e]
      - [const fresh n<>] *)
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  (** // [filesys n = [f1, .., fm]] XXX unused *)
  | DeclChan of Name.ident * unit option * Name.ident
  (** [channel n : ty] or [channel n<> : ty *)
  | DeclProc of { id : Name.ident
                ; param : Name.ident option
                ; args : (bool * Name.ident * Name.ident) list
                ; typ : Name.ident
                ; files : (expr * Name.ident * expr) list
                ; vars : (Name.ident * expr) list
                ; funcs : (Name.ident * (Name.ident list) * cmd) list
                ; main : cmd }
  (** [process id<p>(x1 : ty1, .., xn : tyn) : ty { file ... var ... function ... main ... }] *)
  | DeclSys of proc list * lemma list
  (** [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
  | DeclLoad of string * decl list
  (** [load "fn"] *)
