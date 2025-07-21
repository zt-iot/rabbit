
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


(* Cst_syntax.expr = Typed.expr but with an embedded Cst_env.t *)
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


(* Cst_syntax.fact = Typed.fact but with an embedded Cst_env.t *)
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

(* Cst_synax.cmd = Typed.cmd but with an embedded Cst_env.t 
Additionally, the `New` constructor needs a Cst_env.core_security_type
*)
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
  | New of ident * Cst_env.core_security_type option * (name * expr list) option * cmd
  (** allocation, new x := S(e1,..en) in c *)
  | Get of ident list * expr * name * cmd (** fetch, let x1,..,xn := e.S in c *)
  | Del of expr * name (** deletion , delete e.S *)
[@@deriving show]





type chan_param = Typed.chan_param [@@deriving show]
type proc = Typed.proc [@@deriving show]


type init_desc =
  | Value of expr (** [const n = e] *)
  | Value_with_param of ident * expr (** [const n<p> = e] *)
  | Fresh (** [const fresh n] *)
  | Fresh_with_param (** [const fresh n<>] *)
[@@deriving show]



(* The point of a Cst_syntax.decl is only to register `Cst_syntax.cmd` code *)
(* as we cannot register that information in the environment *)
type decl = decl' loc_env [@@deriving show]
and decl' =
  | Syscall of
      { id : ident
      ; args : ident list
      ; cmd : cmd
      }
  (** system call, [syscall f(a1,..,an) { c }]
                   [passive attack f(ty1 a1,..,tyn an) { c }]
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
      ; vars : (ident * expr) list (* typing information is not necessary, because we can infer the type from the expression *)
      ; funcs : (ident * ident list * cmd) list (* typing information is recorded in the environment instead *)
      ; main : cmd
      }
  (** [process id<p>(x1 : ty1, .., xn : tyn) : ty { file ... var ... function ... main ... }] *)
  | System of string list
  (** [system proc1|..|procn *)
[@@deriving show]



