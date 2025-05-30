type operator = string

type type_class =
  | CProc (** [process] *)
  | CFsys (** [filesys] *)
  | CChan (** [channel] *)

type expr = expr' Location.located
and expr' =
  | Var of Name.ident
  (** variable, [x] *)
  | Boolean of bool
  (** boolean, [true]/[false] *)
  | String of string
  (** string, ["hello"] *)
  (* | Integer of Mpzf.t *)
  | Integer of int
  (** integer, [42] *)
  | Float of string (* store the string so we can correctly round later *)
  (** float, [4.12] *)
  | Apply of operator * expr list
  (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list
  (** tuple, [(e1,..,en)] *)
  | Param of Name.ident * expr
  (** parameter, [f<e>] *)

let vars_of_expr e =
  let module NS = Name.Set in
  let rec aux s (e : expr) =
    match e.data with
    | Var id -> NS.add id s
    | Boolean _ | String _ | Integer _ | Float _ -> s
    | Apply (_, es) | Tuple es -> List.fold_left aux s es
    | Param (id, e) -> NS.add id (aux s e)
  in
  aux NS.empty e

type fact = fact' Location.located
and fact' =
  | Fact of Name.ident * expr list
  (** [n(e1,..,en)] *)
  | GlobalFact of Name.ident * expr list
  (** [:: n(e1,..,en) ]*)
  | ChannelFact of expr * Name.ident * expr list
  (** [e :: n(e1,..,en)] *)
  | ProcessFact of expr * Name.ident * expr list
  (** [e % n(e1,..,en)] *)
  | EqFact of expr * expr (** e1 = e2 *)
  | NeqFact of expr * expr (** e1 != e2 *)
  | FileFact of expr * expr (** S.e *)

let vars_of_fact (fact : fact) =
  let module NS = Name.Set in
  match fact.data with
  | Fact (_, es) -> List.fold_left (fun s e -> NS.union s (vars_of_expr e)) NS.empty es
  | GlobalFact (_, es) -> List.fold_left (fun s e -> NS.union s (vars_of_expr e)) NS.empty es
  | ChannelFact (e, _, es)
  | ProcessFact (e, _, es)  -> List.fold_left (fun s e -> NS.union s (vars_of_expr e)) NS.empty (e::es)
  | EqFact (e1, e2) | NeqFact (e1, e2) | FileFact (e1, e2) ->
      NS.union (vars_of_expr e1) (vars_of_expr e2)

let vars_of_facts facts =
  List.fold_left (fun s fact ->
      Name.Set.union s (vars_of_fact fact)) Name.Set.empty facts

type 'cmd case = (fact list * 'cmd)

type cmd = cmd' Location.located
and cmd' =
  | Skip
  (** skip *)
  | Sequence of cmd * cmd
  (** sequencing, [c1; c2] *)
  (* | Wait of fact list * cmd *)
  | Put of fact list
  (** output, [put[f1,..,fn]] *)
  | Let of Name.ident * expr * cmd
  (** let binding, [let x = e in c] *)
  | Assign of Name.ident option * expr
  (** assignment, [x := e] or [_ := e] *)
  | Case of cmd case list
  (** guarded cases, [case [x,..] => c1 | .. | [z,..] => cn end] *)
  | While of cmd case list * cmd case list
  (** guarded loop,
     [repeat [x,..] => c1 | .. | [z,..] => cn
      until [x',..] => c1 | .. | [z',..] => cn'
      end] *)
  | Event of fact list
  (** tag, [event[T]] *)
  | Return of expr
  (** return *)
  | New of Name.ident * (Name.ident * expr list) option * cmd
  (** allocation, [new x := S(e1,..,en) in c] *)
  | Get of Name.ident list * expr * Name.ident * cmd
  (** fetch, [let x1,...,xn := e.S in c] *)
  | Del of expr * Name.ident
  (** deletion, [delete e.S] *)

(** Channel argument *)
type chan_arg =
  | ChanArgPlain of Name.ident (** [id] *)
  | ChanArgParam of Name.ident (** [id<>] *)
  | ChanArgParamInst of Name.ident * expr (** [id<e>] *)

type pproc = pproc' Location.located
and pproc' =
  | Proc of Name.ident * (chan_arg list) (** [pid(chargs,..,chargs)] *)
  | ParamProc of Name.ident * expr * (chan_arg list) (** [pid<e>(chargs,..,chargs)] *)

type proc =
| UnboundedProc of pproc (** [proc] *)
| BoundedProc of (Name.ident * pproc list) (** [!name.(pproc1|..|pprocn)] *)


type prop = prop' Location.located
and prop' =
  | PlainString of string
  (** [exists-trace "xxx"]
      [all-traces "xxx"]
  *)
  | Reachability of fact list
  (** [reachable f1,..,fn] *)
  | Correspondence of fact * fact
  (** [corresponds fa ~> fb] *)

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop
  (** lemma [Name : prop] *)


type decl = decl' Location.located
and decl' =
  | DeclExtFun of Name.ident * int
  (** external function, [function id : arity] *)
  | DeclExtEq of expr * expr
  (** external equation, [equation e1 = e2] *)
  | DeclExtSyscall of Name.ident * Name.ident list * cmd
  (** system call, [syscall f(ty1 a1,..,tyn an) { c }]
                   [passive attack f(ty1 a1,..,tyn an) { c }]
      XXX what is passive attack for?  It is not distinguishable from syscall in Input.
  *)
  | DeclExtAttack of Name.ident * Name.ident * Name.ident list * cmd
  (** [attack f on name (ty1 a1,..,tyn an) { c }] *)
  | DeclType of Name.ident * type_class
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
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  (** // [filesys n = [f1, .., fm]] XXX unused *)
  | DeclChan of Name.ident * Name.ident
  (** [channel n : ty] *)
  | DeclProc of { id : Name.ident
                ; args : (bool * Name.ident * Name.ident) list
                ; typ : Name.ident
                ; files : (expr * Name.ident * expr) list
                ; vars : (Name.ident * expr) list
                ; funcs : (Name.ident * (Name.ident list) * cmd) list
                ; main : cmd }
  (** [ process id(x1 : ty1, .., xn : tyn) : ty {
          file id : ty = e ...
          var ...
          function ...
          main ...
        }
      ] *)
  | DeclParamProc of { id : Name.ident
                     ; param : Name.ident
                     ; args : (bool * Name.ident * Name.ident) list
                     ; typ : Name.ident
                     ; files : (expr * Name.ident * expr) list
                     ; vars : (Name.ident * expr) list
                     ; funcs : (Name.ident * (Name.ident list) * cmd) list
                     ; main : cmd }
  (** [process id<p>(x1 : ty1, .., xn : tyn) : ty { file ... var ... function ... main ... }] *)
  | DeclSys of proc list * lemma list
  (** [system proc1|..|procn requires [lemma X : ...; ..; lemma Y : ...]] *)
  | DeclLoad of string
  (** [load "fn"] *)
  | DeclParamInit of Name.ident * (Name.ident * expr) option
  (** - [const n<p> = e]
      - [const fresh n<>] *)
  | DeclParamChan of Name.ident * Name.ident
  (** [channel n<> : ty] *)
