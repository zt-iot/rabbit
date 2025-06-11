type var_desc = Syntax.variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param

type named_fact_desc =
  | NoName
  | Global
  | Channel
  | Process

val string_of_named_fact_desc : named_fact_desc -> string

type desc =
  | Var of var_desc
  | ExtFun of int (** external function with arity *)
  | ExtConst (** external function with arity = 0, ex.  function true 0 *)
  | ExtSyscall of int (** external system call with arity *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Ident.t (* channel type *)
  | Attack
  | Type of Input.type_class
  | Function of int (** function with definition and arity *)
  | Process

val print_desc : desc -> Format.formatter -> unit

type t

val empty : unit -> t

val mem : t -> Name.ident -> bool

val find_opt : t -> Name.ident -> (Ident.t * desc) option

val find_opt_by_id : t -> Ident.t -> desc option

val add : t -> Ident.t -> desc -> t

val add_fact : t -> Name.ident -> named_fact_desc * int -> unit

val find_fact_opt : t -> Name.ident -> (named_fact_desc * int) option
