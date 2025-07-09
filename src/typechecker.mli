


exception TypeException of string


val typeof_expr : Cst_syntax.expr -> Cst_env.core_security_type

val typeof_cmd : Cst_syntax.cmd -> Cst_env.core_security_type

val typecheck_decl : Cst_syntax.decl -> unit

val typecheck_sys :
  Cst_syntax.decl list -> Cst_syntax.decl -> unit