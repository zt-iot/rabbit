type operator = Name.ident

type variable_class =
  | Top (** variables by [var ...] in process definition *)
  | Loc (** local variables by function arguments, etc. *)
  | Meta (** variables introduced by [new] and [let x1,...,xn := e.S in ...] *)
  | MetaNew (** pattern variables in cases and free variables in lemmas *)

type expr = expr' Location.located

and expr' =
  | Const of Name.ident * expr option
  (** - const [n] by [const n = e] or [const fresh n]
      - const [n<e>] by [const name<param> = e] or [const fresh name<>] *)
  | ExtConst of Name.ident (** ext function by [function f:0] *)
  | Variable of string * (variable_class * int (* index *))
  | Boolean of bool (** boolean, XXX no constant available for now *)
  | String of string (** string, ["hello"] *)
  | Integer of int (** integer, [42] *)
  | Float of string (** float, [4.12]. Store the string so we can correctly round later *)
  | Apply of operator * expr list (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list (** tuple, [(e1,..,en)] *)
  | Channel of Name.ident * expr option (** [id] or [id<e>] *)
  | Param of Name.ident (** parameter variable *)

type fact = fact' Location.located

and fact' =
  | Fact of Name.ident * expr list (** [n(e1,..,en)] *)
  | GlobalFact of Name.ident * expr list (** [:: n(e1,..,en) ]*)
  | ChannelFact of expr * Name.ident * expr list (** [e :: n(e1,..,en)] *)
  | ProcessFact of Name.ident * Name.ident * expr list (** [e % n(e1,..,en)] *)
  | EqFact of expr * expr (** [e1 = e2] *)
  | NeqFact of expr * expr (** [e1 != e2] *)
  | FileFact of expr * expr (** [S.e] *)

type 'cmd case = Name.ident list * fact list * 'cmd
(** case: [fresh_vars * facts * cmd] *)

type cmd = cmd' Location.located

and cmd' =
  | Skip (** doing nothing *)
  | Sequence of cmd * cmd (** sequencing, c1; c2 *)
  | Put of fact list (** output, [put[f1,..,fn]] *)
  | Let of Name.ident * expr * cmd (** let binding, [var x = e in c] *)
  | Assign of (Name.ident * (int * bool)) * expr
  (** assignment, [x := e]. [x] is [(name, (idx, top_or_local))] *)
  | FCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  (** function call, [x := f(e1,..,en)]. [x] is [(name, (idx, top_or_local))] *)
  | SCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  (** syscall call, [x := s(e1,..,en)]. [x] is [(name, (idex, top_or_local))] *)
  | Case of cmd case list (** guarded cases, [case [a1s] => c1 | .. | [ans] => cn end] *)
  | While of cmd case list * cmd case list
  (** guarded loop,
      [repeat [a1s] => c1 | .. | [ans] => cn
       until [a'1s] => c'1 | .. | [a'ms] => c'm
       end]
  *)
  | Event of fact list (** tag, [event[T]] *)
  | Return of expr (** return *)
  | New of Name.ident * (Name.ident * expr list) option * cmd
  (** allocation, [new x := S(e1,..en) in c] *)
  | Get of Name.ident list * expr * Name.ident * cmd
  (** fetch, [let x1,..,xn := e.S in c] *)
  | Del of expr * Name.ident (** deletion , [delete e.S] *)

type chan_arg = ChanArg of { id : Name.ident; param : expr option option; typ : Name.ident }
  (** - [param= None]: [id]
      - [param= Some None]: [id<>]
      - [param= Some (Some e)]: [id<e>]
  *)

type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * expr option * (chan_arg list) (** [pid<e>(chargs,..,chargs)] *)


type proc =
  | UnboundedProc of pproc (** [proc] *)
  | BoundedProc of (Name.ident * pproc list) (** [!name.(pproc1|..|pprocn)] *)

(** Lemma *)
type lemma = lemma' Location.located
and lemma' =
  | PlainLemma of Name.ident * string
  (** [name : exists-trace "xxx"]
      [name : all-traces "xxx"]
  *)
  | ReachabilityLemma of
      Name.ident * Name.ident list (* fresh variables *) * fact list
  (** [name : reachable f1,..,fn] *)
  | CorrespondenceLemma of Name.ident * Name.ident list (* fresh variables *) * fact * fact
  (** [name : corresponds fa ~> fb] *)

type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  (** external function, [function id : arity] *)
  | DeclExtEq of expr * expr
  (** external equation, [equation e1 = e2] *)
  | DeclExtSyscall of Name.ident * Name.ident list * cmd
  (** system call, [syscall name(args) { c }]
                   [passive attack name(args) { c }]
      XXX what is passive attack for?  It is not distinguishable from syscall in Input.
  *)
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd
  (** [attack name on syscall (args) { c }] *)
  | DeclType of Name.ident * Input.type_class
  (** type declaration, [type t : filesys/process/channel] *)
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  (** [allow proc_ty target_ty1 .. target_tyn [syscall1, .., syscallm]]
      [allow proc_ty target_ty1 .. targe_t_tyn [.]]  for all the syscalls

      XXX the list [target_tyi] is either empty or singleton.  Should use option type?
  *)
  | DeclAttack of Name.ident list * Name.ident list
  (** [allow attack proc_ty1 .. proc_tyn [attack1, .., attackn]] *)
  | DeclInit of Name.ident * expr option
  (** [const n = e]
      [const fresh n]
  *)
  | DeclParamInit of Name.ident * (Name.ident * expr) option
  (** - [const name<param> = e]
      - [const fresh name<>] *)
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  (** [filesys n = [f1, .., fm]] XXX unused *)
  | DeclChan of Name.ident * unit option * Name.ident
  (** [channel name : chan_ty] or [channel name<> : chan_ty] *)
  | DeclProc of { id : Name.ident
                ; param : Name.ident option
                ; args : (bool * Name.ident * Name.ident) list
                ; typ : Name.ident
                ; files : (expr * Name.ident * expr) list
                ; vars : (Name.ident * expr) list
                ; funcs : (Name.ident * (Name.ident list) * cmd) list
                ; main : cmd }
  (** [process id<param>(ch1 : chty1, .., chn : chtyn) : proc_ty { file ... var ... function ... main ... }] *)
  | DeclSys of proc list * lemma list
  (** [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
  | DeclLoad of string * decl list
  (** [load "fn"] *)
