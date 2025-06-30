



val typecheck_expr : Typed.expr -> Env.t 

val typecheck_cmd : Typed.cmd -> Env.t -> unit

(* TODO fill in typing signature once it is clear which type this function should return *)
val typecheck_decl : Typed.decl -> Env.t -> unit