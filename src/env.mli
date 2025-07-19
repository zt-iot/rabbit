type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global

val string_of_named_fact_desc : named_fact_desc -> string

type desc =
  | Var (** mutable variable *)
  | Param (** parameter *)
  | ExtFun of int (** external function with arity *)
  | ExtConst (** external function with arity = 0, ex.  function true 0 *)
  | ExtSyscall of int (** external system call with arity *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Ident.t (* channel type *)
  | Attack
  | Type of Input.type_class
  | Function of int (** function with definition and arity *)
  | Process
  | Rho (** $\rho$, only used in [Sem] and later stages *)

val print_desc : desc -> Format.formatter -> unit

type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option)) list ref
  (** Fact names with descriptions and arities. Arities can be unknown
      if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c].

      The fact environment is a global singleton and shared, therefore a reference.
  *)
}

val empty : unit -> t

val mem : t -> Name.ident -> bool

val find_opt : t -> Name.ident -> (Ident.t * desc) option

val find_opt_by_id : t -> Ident.t -> desc option

val add : t -> Ident.t -> desc -> t

val update_fact : t -> Name.ident -> named_fact_desc * int option -> unit
(** If the binding already exists, it is overridden *)

val find_fact_opt : t -> Name.ident -> (named_fact_desc * int option) option

val merge : t -> t -> t
