

open Sets

exception TypeException of string

type core_type = 
  | TChan of core_type list
  | TSimple of Name.ident * core_type list
  | TProd of core_type * core_type

type secrecy_lvl = 
  | Public 
  | SNode of proc_ty_set 

type integrity_lvl = 
  | Untrusted
  | INode of proc_ty_set

type core_security_type = core_type * (secrecy_lvl * integrity_lvl)

type function_param_type = 
  | CParamCore of core_security_type
  | CParamPoly of Name.ident

val typeof_cmd : Cst_syntax.cmd -> unit

val typecheck_decl : Cst_syntax.decl -> unit

val typecheck_sys :
  Cst_syntax.decl list -> Cst_syntax.decl -> unit