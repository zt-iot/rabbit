type var_desc = Syntax.variable_desc =
  | Top of int
  | Loc of int
  | Meta of int
  | MetaNew of int
  | Param

type named_fact_desc =
  | Channel
  | Structure
  | Plain
  | Global

val string_of_named_fact_desc : named_fact_desc -> string





(* represents type terms within square brackets '[` and `]` *)
type ty_param = 
  | TyParamSimple of Name.ident * ty_param list
  | TyParamSecurity of Name.ident
  | TyParamProduct of ty_param * ty_param


(* an instantiated_ty is used to type expression terms in Rabbit *)
type instantiated_ty = 
  | TySecurity of Name.ident
  | TySimple of Name.ident * ty_param list
  | TyProduct of instantiated_ty * instantiated_ty
  | TyChan of ty_param list
  

type f_param_ty_param = 
  | FParamTyParamSecurity of Name.ident
  | FParamTyParamSimple of Name.ident * f_param_ty_param list
  | FParamTyParamProduct of f_param_ty_param * f_param_ty_param
  | FParamTyParamPoly of Name.ident


type function_param = 
  | FParamSecurity of Name.ident
  | FParamSimple of Name.ident * f_param_ty_param list
  | FParamProduct of function_param * function_param
  | FParamPoly of Name.ident
  | FParamChannel of f_param_ty_param list
  

type desc =

  | SimpleTypeDef of Name.ident list (* simple type declaration *)
  | Var of var_desc
  | ExtFun of int (** external function with arity *)
  | ExtConst (** external function with arity = 0, ex.  function true 0 *)
  | ExtSyscall of int (** external system call with arity *)
  | Const of bool (* with param or not *)
  | Channel of bool (* with param or not *) * Ident.t (* channel type *)
  | Attack

  (* all these four constructors represents the <y> in `type <x> : <y>` *)
  | ProcTypeDef
  | FilesysTypeDef

  | ChanTypeDef of ty_param list
  | SecurityTypeDef of Name.ident * ty_param list
  

  | Function of int (** function with definition and arity *)
  | Process (* a process template, not to be confused with a process type (ProcessTypeDef) *)

val print_desc : desc -> Format.formatter -> unit

type t = {
  vars : (Ident.t * desc) list;
  facts : (Name.ident * (named_fact_desc * int option)) list ref
  (** Fact names with descriptions and arities. Arities can be unknown
      if [delete e.S] first appear than [new x := S(args) in c]
      and [let xi := e.S in c]
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
