type operator = string

type type_class =
  | CProc (** [process] *)
  | CFsys (** [filesys] *)
  | CChan (** [channel] *)

type expr = expr' Location.located

and expr' =
  | Var of Name.ident (** variable, [x] *)
  | Wildcard (** anonymous value, [_] *)
  | Boolean of bool (** boolean. Currently no boolean constants available  *)
  | String of string (** string, ["hello"] *)
  (* | Integer of Mpzf.t *)
  | Integer of int (** integer, [42] *)
  | Float of string (* store the string so we can correctly round later *)
  (** float, [4.12] *)
  | Apply of operator * expr list (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list (** tuple, [(e1,..,en)] *)
  | Param of Name.ident * expr (** parameter, [f<e>] *)

type fact = fact' Location.located

and fact' =
  | Fact of Name.ident * expr list (** [n(e1,..,en)] *)
  | GlobalFact of Name.ident * expr list (** [:: n(e1,..,en) ]*)
  | ChannelFact of expr * Name.ident * expr list (** [e :: n(e1,..,en)] *)
  | ProcessFact of expr * Name.ident * expr list (** [e % n(e1,..,en)] *)
  | EqFact of expr * expr (** [e1 = e2] *)
  | NeqFact of expr * expr (** [e1 != e2] *)
  | FileFact of expr * expr (** [S.e] *)

type 'cmd case = fact list * 'cmd

type cmd = cmd' Location.located

and cmd' =
  | Skip (** skip *)
  | Sequence of cmd * cmd (** sequencing, [c1; c2] *)
  (* | Wait of fact list * cmd *)
  | Put of fact list (** output, [put[f1,..,fn]] *)
  | Let of Name.ident * expr * cmd (** let binding, [var x = e in c] *)
  | Assign of Name.ident option * expr (** assignment, [x := e] or [_ := e] *)
  | Case of cmd case list
  (** guarded cases, [case [x,..] => c1 | .. | [z,..] => cn end] *)
  | While of cmd case list * cmd case list
  (** guarded loop,
     [repeat [x,..] => c1 | .. | [z,..] => cn
      until [x',..] => c1 | .. | [z',..] => cn'
      end] *)
  | Event of fact list (** tag, [event[T]] *)
  | Return of expr (** return *)
  | New of Name.ident * (Name.ident * expr list) option * cmd
  (** allocation, [new x := S(e1,..,en) in c] *)
  | Get of Name.ident list * expr * Name.ident * cmd
  (** fetch, [let x1,...,xn := e.S in c] *)
  | Del of expr * Name.ident (** deletion, [delete e.S] *)

(** Channel argument *)
type chan_arg =
  | ChanArgPlain of Name.ident (** [id] *)
  | ChanArgParam of Name.ident (** [id<>] *)
  | ChanArgParamInst of Name.ident * expr (** [id<e>] *)

type chan_param = ChanParam of { id : Name.ident; param : unit option; typ : Name.ident }
(** [chan_name : chan_ty] or [chan_name<> : chan_ty] *)

type pproc = pproc' Location.located

and pproc' =
  | Proc of Name.ident * chan_arg list (** [pid(chargs,..,chargs)] *)
  | ParamProc of Name.ident * expr * chan_arg list (** [pid<e>(chargs,..,chargs)] *)

type proc =
  | UnboundedProc of pproc (** [proc] *)
  | BoundedProc of (Name.ident * pproc list) (** [!name.(pproc1|..|pprocn)] *)

type prop = prop' Location.located

and prop' =
  | PlainString of string (** [exists-trace "xxx"]
      [all-traces "xxx"]
  *)
  | Reachability of fact list (** [reachable f1,..,fn] *)
  | Correspondence of fact * fact (** [corresponds fa ~> fb] *)

type lemma = lemma' Location.located
and lemma' = Lemma of Name.ident * prop (** lemma [Name : prop] *)

type init_desc =
  | Fresh
  | Value of expr
  | Value_with_param of expr * Name.ident
  | Fresh_with_param

type decl = decl' Location.located

and decl' =
  | DeclExtFun of Name.ident * int (** external function, [function id : arity] *)
  | DeclExtEq of expr * expr (** external equation, [equation e1 = e2] *)
  | DeclExtSyscall of Name.ident * Name.ident list * cmd * bool
  (** system call, [syscall f(ty1 a1,..,tyn an) { c }]
                   [passive attack f(ty1 a1,..,tyn an) { c }]
  *)
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd
  (** [attack f on name (ty1 a1,..,tyn an) { c }] *)
  | DeclType of Name.ident * type_class
  (** type declaration, [type t : filesys/process/channel] *)
  | DeclAccess of Name.ident * Name.ident list * Name.ident list option
  (** [allow s t1 .. tn [f1, .., fm]]
      [allow s t1 .. tn [.]]  for the direct accesses via [put] and [case], [repeat]

      XXX the list [ti] is either empty or singleton.  Should use option type?
  *)
  | DeclAttack of Name.ident list * Name.ident list
  (** [allow attack t1 .. tn [f1, .., fm]] *)
  | DeclInit of Name.ident * init_desc
  (** [const n = e]
      [const fresh n]
      [const n<p> = e]
      [const fresh n<>] *)
  | DeclChan of chan_param (** [channel n : ty] or [channel n<> : ty] *)
  | DeclProc of
      { id : Name.ident
      ; param : Name.ident option
      ; args : chan_param list
      ; typ : Name.ident
      ; files : (expr * Name.ident * expr) list
      ; vars : (Name.ident * expr) list
      ; funcs : (Name.ident * Name.ident list * cmd) list
      ; main : cmd
      }
  (** [ process id<p>(x1 : ty1, .., xn : tyn) : ty {
          file id : ty = e ...
          var ...
          function ...
          main ...
        }
      ] *)
  | DeclSys of proc list * lemma list
  (** [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
  | DeclLoad of string (** [load "fn"] *)

val vars_of_expr : expr -> Name.Set.t
val vars_of_fact : fact -> Name.Set.t
val vars_of_facts : fact list -> Name.Set.t
