type named_fact_desc =
  | Channel
  | Structure of Input.field_type list
  | Plain
  | Global

type type_ =
  | TValue
  | TChannel
  | TParameter
  | TVar of type_var ref

and type_var =
  | Unbound of int
  | Link of type_

type callable_type =
  { argument_types : type_ list
  ; result_type : type_
  }

exception Cannot_unify of type_ * type_

val fresh_type : unit -> type_
val type_variable_mark : unit -> int
val repr : type_ -> type_
val unify : type_ -> type_ -> unit
val default_type : type_ -> type_
val default_types_since : int -> unit
val discard_types_since : int -> unit
val type_of_field_type : Input.field_type -> type_
val print_type : type_ -> Format.formatter -> unit

val string_of_named_fact_desc : named_fact_desc -> string

(** Kinds of bound identifiers together with inferred value types where needed. *)
type desc =
  | Var of type_ (** mutable variable *)
  | Param (** parameter *)
  | ExtFun of callable_type (** external function *)
  | ExtConst (** external function with arity = 0, ex.  [function true 0] *)
  | ExtSyscall of callable_type (** external system call *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Ident.t (* channel type *)
  | Attack
  | Type of Input.type_class
  | Function of callable_type (** function with definition *)
  | Process
  | Rho (** $\rho$, only used in [Sem] and later stages *)

val callable_type_of_desc : desc -> callable_type option
val type_of_desc : desc -> type_ option

val print_desc : desc -> Format.formatter -> unit

(** Name checking environment *)
type t =
  { vars : (Ident.t * desc) list
  ; facts : (Name.ident * (named_fact_desc * type_ list option)) list ref
  (** Fact names with descriptions and argument types. Types can be unknown
      if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c].

      The fact environment is a global singleton and shared,
      therefore implemented as a reference.
  *)
  }

val empty : unit -> t

val mem : t -> Name.ident -> bool

val find_opt : t -> Name.ident -> (Ident.t * desc) option

val find_opt_by_id : t -> Ident.t -> desc option

val add : t -> Ident.t -> desc -> t

val update_fact : t -> Name.ident -> named_fact_desc * type_ list option -> unit
(** If the binding already exists, it is overridden *)

val find_fact_opt : t -> Name.ident -> (named_fact_desc * type_ list option) option
