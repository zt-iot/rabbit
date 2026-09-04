type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global

val string_of_named_fact_desc : named_fact_desc -> string

(** Kinds of bound identifiers together with inferred value types where needed. *)
type desc =
  | Var of Type.type_ (** mutable variable *)
  | Param (** parameter *)
  | ExtFun of Type.callable_type (** external function *)
  | ExtConst (** external function with arity = 0, ex.  [function true 0] *)
  | ExtSyscall of Type.callable_type (** external system call *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Ident.t (* channel type *)
  | Attack
  | Type of Input.type_class
  | Function of Type.callable_type (** function with definition *)
  | Process
  | Rho (** $\rho$, only used in [Sem] and later stages *)

val kind_of_desc : desc -> string

val callable_type_of_desc : desc -> Type.callable_type option
val type_of_desc : desc -> Type.type_ option

val print_desc : desc -> Format.formatter -> unit

include Error.S

(** Name checking environment *)
type t

val bindings : t -> (Ident.t * desc) list

val empty : unit -> t

val singleton : Ident.t -> desc -> t

val mem : t -> Name.ident -> bool

val find_opt : t -> Name.ident -> (Ident.t * desc) option

val find_opt_by_id : t -> Ident.t -> desc option

val add : t -> Ident.t -> desc -> t

val update_fact : t -> Name.ident -> named_fact_desc * Type.type_ list option -> unit
(** If the binding already exists, it is overridden *)

val find_fact_opt : t -> Name.ident -> (named_fact_desc * Type.type_ list option) option

val find : loc:Location.t -> t -> Name.ident -> Ident.t * desc
val find_desc : loc:Location.t -> t -> Name.ident -> desc -> Ident.t

(** Fails if the name is bound in the environment *)
val add_global : loc:Location.t -> t -> Name.ident -> desc -> t * Ident.t

val add_fact : loc:Location.t -> t -> Name.ident -> named_fact_desc * Type.type_ list option -> unit
