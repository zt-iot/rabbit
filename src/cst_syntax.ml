
type name = Name.t [@@deriving show]
type ident = Ident.t [@@deriving show]


type 'desc loc_env =
  { desc : 'desc
  ; loc : Location.t
  ; env : Cst_env.t
  }


let pp_loc_env pp_desc fmt { desc; loc = _; env } =
  Format.fprintf fmt "{ desc = %a; env = %a }"
    pp_desc desc
    Cst_env.pp env


type expr = expr' loc_env [@@deriving show]

and expr' =
  | Ident of
      { id : ident
      ; desc : Cst_env.desc
      ; param : expr option
       (** [param= Some _] iff [desc= Const true _] *)
      }
  (** [id] or [id<e>].
      [id<e>] is only possible either for [id] of [Channel {param=true}] or [Const {param=true}] *)
  | Boolean of bool (** boolean, [true]/[false] *)
  | String of string (** string, ["hello"] *)
  | Integer of int (** integer, [42] *)
  | Float of string (** float, [4.12]. Store the string so we can correctly round later *)
  | Apply of ident * expr list (** application, [f(e1,..,en)]   /  [e1 op e2] *)
  | Tuple of expr list (** tuple, [(e1,..,en)] *)
  | Unit
[@@deriving show]



type fact = fact' loc_env [@@deriving show]

and fact' =
  | Channel of
      { channel : expr
      ; name : name
      ; args : expr list
      } (** Channel fact [ch :: name(args)] *)
  | Out of expr (** Attacker fact: Out *)
  | In of expr (** Attacker fact: In *)
  | Plain of name * expr list
  | Eq of expr * expr
  | Neq of expr * expr
  | File of
      { path : expr
      ; contents : expr
      } (** File fact [path.contents] *)
  | Global of string * expr list
[@@deriving show]

type cmd = cmd' loc_env [@@deriving show]

and case =
  { fresh : ident list
  ; facts : fact list
  ; cmd : cmd
  } [@@deriving show]

and cmd' =
  | Skip (** doing nothing *)
  | Sequence of cmd * cmd (** sequencing, c1; c2 *)
  | Put of fact list (** output, put[f1,..,fn] *)
  | Let of ident * expr * cmd (** let binding, let x = e in c *)
  | Assign of ident option * expr (** assignment, x := e *)
  | Case of case list (** guarded cases, case [a1s] => c1 | .. | [ans] => cn end *)
  | While of case list * case list
  (** guarded loop,
      repeat [a1s] => c1 | .. | [ans] => cn
      until [a'1s] => c'1 | .. | [a'ms] => c'm
      end
  *)
  | Event of fact list (** tag, event[T] *)
  | Return of expr (** return *)
  | New of ident * (name * expr list) option * cmd
  (** allocation, new x := S(e1,..en) in c *)
  | Get of ident list * expr * name * cmd (** fetch, let x1,..,xn := e.S in c *)
  | Del of expr * name (** deletion , delete e.S *)
[@@deriving show]



type chan_param = { channel : ident; param : unit option; typ : ident } [@@deriving show]



type chan_arg =
  { channel : ident
  ; parameter : expr option option
  (** - [None]: Simple channel [id],
      - [Some None]: Channel with a parameter [id<>],
      - [Some (Some e)]: Instantiated channel with a parameter [id<e>]
  *)
  ; typ : ident
  } [@@deriving show]

type pproc = pproc' Location.located [@@deriving show]

(** id<parameter>(args) *)
and pproc' =
  { id : ident
  ; parameter : expr option
  ; args : chan_arg list
  } [@@deriving show]

type proc =
  | Unbounded of pproc (** [proc] *)
  | Bounded of ident * pproc list (** [!name.(pproc1|..|pprocn)] *)
[@@deriving show]




type init_desc =
  | Value of expr (** [const n = e] *)
  | Value_with_param of ident * expr (** [const n<p> = e] *)
  | Fresh (** [const fresh n] *)
  | Fresh_with_param (** [const fresh n<>] *)
[@@deriving show]



type decl = decl' loc_env [@@deriving show]

and decl' =
  | EqThyFunc of
      { id : ident
      ; arity : int
      } (** external function, [function id : arity] *)
  | Equation of expr * expr (** external equation, [equation e1 = e2] *)
  | Syscall of
      { id : ident
      ; args : ident list
      ; cmd : cmd
      }
  (** system call, [syscall f(a1,..,an) { c }]
                   [passive attack f(ty1 a1,..,tyn an) { c }]
      XXX what is passive attack for?  It is not distinguishable from syscall in Input.
  *)
  | Attack of
      { id : ident
      ; syscall : ident
      ; args : ident list
      ; cmd : cmd
      } (** [attack id on syscall (a1,..,an) { c }] *)
  | Process of
      { id : ident
      ; param : ident option
      ; args : chan_param list
      ; typ : ident
      ; files : (expr * ident * expr) list
      ; vars : (ident * expr) list
      ; funcs : (ident * ident list * cmd) list
      ; main : cmd
      }
  (** [process id<p>(x1 : ty1, .., xn : tyn) : ty { file ... var ... function ... main ... }] *)
  | System of proc list
  (** [system proc1|..|procn *)
[@@deriving show]


