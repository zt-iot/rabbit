



val typeof_expr : Cst_syntax.expr -> Cst_env.t -> Cst_env.core_security_type



val typeof_cmd : Cst_syntax.cmd -> Cst_env.t -> Cst_env.core_security_type 


(* TODO fill in typing signature once it is clear which type this function should return *)

val typecheck_decl : Cst_syntax.decl -> Cst_env.t -> unit

(* Supplying an environment is not necessary: 
the global environment is 
simply the environment from the Cst_syntax.decl.System declaration
*)
val typecheck_sys : Cst_syntax.decl list -> Cst_syntax.decl -> unit