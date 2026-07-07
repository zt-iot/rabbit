type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global

val string_of_named_fact_desc : named_fact_desc -> string

(** Kinds of variables, or very weak types *)
type desc =
  | Var (** mutable variable *)
  | Param (** parameter *)
  | ExtFun of int (** external function with arity *)
  | ExtConst (** external function with arity = 0, ex.  [function true 0] *)
  | ExtSyscall of int (** external system call with arity *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Ident.t (* channel type *)
  | Attack
  | Type of Input.type_class
  | Function of int (** function with definition and arity *)
  | Process
  | Rho (** $\rho$, only used in [Sem] and later stages *)

val print_desc : desc -> Format.formatter -> unit

(** Name checking environment *)
type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option * bool)) list ref;
  (** Fact names with descriptions, arities and whether it is persistent.
      Arities can be unknown if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c].

      The fact environment is a global singleton and shared,
      therefore implemented as a reference.
  *)
  tags : (Name.ident * (named_fact_desc * int option)) list ref;
  (** Tags are similar to facts, but differ in that they never distinguish whether they are persistent or not  *)
}

val empty : unit -> t

val mem : t -> Name.ident -> bool

val find_opt : t -> Name.ident -> (Ident.t * desc) option

val find_opt_by_id : t -> Ident.t -> desc option

val add : t -> Ident.t -> desc -> t

val update_fact : t -> Name.ident -> named_fact_desc * int option * bool -> unit
(** If the binding already exists, it is overridden *)

val update_tag : t -> Name.ident -> named_fact_desc * int option -> unit

val find_fact_opt : t -> Name.ident -> (named_fact_desc * int option * bool) option

val find_tag_opt : t -> Name.ident -> (named_fact_desc * int option) option
