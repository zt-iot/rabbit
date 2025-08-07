(** The semantics *)

include Sig.ERROR

module Index : sig
  (** Transition graph node index, it is reversed! *)
  type t = private (int * int) list

  val compare : t -> t -> int

  val zero : t

  (** [add i n] for $i + n$ *)
  val add : t -> int -> t

  (** [push i n] for $i_n$ *)
  val push : t -> int -> t

  val to_string : t -> string

  val to_string' : t -> string
  (** Same as [to_string] but uses '_' instead of '.' *)

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

(** [Typed.fact] + some internal facts *)
type fact = fact' Typed.loc_env

and fact' =
  | Channel of
      { channel : Typed.expr
      ; name : Name.t
      ; args : Typed.expr list
      } (** Channel fact [ch :: name(args)] *)
  | Plain of
      { pid : Subst.proc_id * Subst.param_id option
      ; name : Name.t
      ; args : Typed.expr list
      } (** [n(e1,..,en)] *)
  | Eq of Typed.expr * Typed.expr (** [e1 = e2] *)
  | Neq of Typed.expr * Typed.expr (** [e1 != e2] *)
  | File of
      { pid : Subst.proc_id * Subst.param_id option
      ; path : Typed.expr
      ; contents : Typed.expr
      } (** File fact [path.contents] *)
  | Global of Name.t * Typed.expr list (** [:: n(e1,..,en)] *)

  (* New additions at Sem level *)

  | Fresh of Ident.t (** Fresh variable *)
  | Structure of
      { pid : Subst.proc_id * Subst.param_id option
      ; name : Name.t
      ; address : Typed.expr
      ; args : Typed.expr list
      } (** Structure fact [name(process, address, args)] *)
  | Loop of
      { pid : Subst.proc_id * Subst.param_id option
      ; mode : Typed.loop_mode
      ; index : Index.t
      }
  | Access of
      { pid : Subst.proc_id * Subst.param_id option
      ; channel: Typed.expr (** channel or file *)
      ; syscall: Ident.t option (** System call allowed the access.
                                    [None] allows the access out of syscalls.   *)
      }

val string_of_fact : fact -> string

val fact_of_typed : (Subst.proc_id * Subst.param_id option) option -> Typed.fact -> fact
(** Canonically maps [Typed.fact] to [fact] *)

module Update : sig
  type desc =
    | New of Typed.expr
    | Update of Typed.expr
    | Drop

  (** State update

      For simplicity, we do not track unmodified variables.
  *)
  type t =
    { rho : Ident.t
    (** $\rho$ variable used in this update *)

    ; register : Typed.expr
    (** The register value a.k.a the return value *)

    ; items : (Ident.t * desc) list
    (** Value updates, if a variable is not listed here, it is not changed *)
    }

  val to_string : t -> string
end

type edge_id = private Ident.t

val edge_id : Ident.t -> edge_id

(**
                      update  tag
                          ↓   ↓
                          f, [T]
   [A]^i_{\Gamma_i} -----------------> [B]^j_{\Gamma_j}
    ↑  ↑      ↑                         ↑  ↑      ↑
   pre |      |                      post  |      |
     source source_vars                 target target_vars
            (source_env)                       (target_env)

   Note that [source_env] and [target_env] are the environments used to name-check (Typer)
   and they can be different from $\Gamma_i$ when in system call codes,
   i.e. the process local variables in [source/target_vars] are not bound in [source/target_env]
   at system call cmds.

   Now [source_env] and [target_env] are only used for debugging purposes.
   They can be safely dropped from this type.
*)
type edge =
  { id : edge_id
  ; source : Index.t (** source node index *)
  ; source_env : Env.t (** environment of the source node *)
  ; source_vars : Ident.t list (** mutable variables of the source node *)
  ; pre : fact list (** preconditions *)
  ; update : Update.t (** state update *)
  ; tag : fact list (** tags *)
  ; post : fact list (** postconditions *)
  ; target : Index.t (** target node index *)
  ; target_env : Env.t (** environment of the target node *)
  ; target_vars : Ident.t list (** mutable variables of the target node *)
  ; loop_back : bool (** Loops back. Triggers an increment of transition counter if [true] *)
  ; attack : bool (** Attack route. [true] if the edge to start an attack *)
  }

type signature =
  { functions : (Ident.t * int) list
  ; equations : (Typed.expr * Typed.expr) list
  }

(** Process, [id<parameter>(args)] *)
type proc =
  { id : Subst.proc_id
  ; param : Subst.param_id option
  ; edges : edge list }

(** Unnamed process group *)
type proc_group_desc =
  | Unbounded of proc
  | Bounded of Subst.param_id * proc list

(** Named process group *)
type proc_group = Subst.proc_group_id * proc_group_desc

type t =
  { signature : signature
  ; proc_groups : proc_group list
  ; access_controls :
      (Subst.proc_group_id
       * (Subst.proc_id
          * (Typed.chan_arg * Ident.t option (* system call or "anywhere" *)) list) list) list
  ; constants : (Ident.t * Typed.init_desc) list
  ; lemmas : (Ident.t * Typed.lemma) list
  }

val compile : Typed.decl list -> t
(** [compile decls] compiles [decls] to semantics [t].

    If the function fails to compile [decls], it raises an exception
    [Error _].
*)

val optimize : t -> t
(** Performs graph compression. *)
