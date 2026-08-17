open Rabbit_proverif_pv_parse
open Pitptree

include module type of Proverif_compiler_env

val compile_expr_to_term : GEnv.t -> T.expr -> term_e
val compile_expr_to_gterm : GEnv.t -> T.expr -> gterm_e
val compile_expr_to_pterm : GEnv.t -> PEnv.t -> T.expr -> pterm_e
val compile_process_body : GEnv.t -> PEnv.t -> T.cmd -> tprocess_e
