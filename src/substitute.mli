include Sig.ERROR

(** Substitute channels inside expr *)
val expr_chan_sub : Syntax.expr -> string -> Syntax.expr -> Syntax.expr

(** Substitute channels inside cmd *)
val cmd_chan_sub : Syntax.cmd -> string -> Syntax.expr -> Syntax.cmd

(** Substitute param_chan in side expr *)
val expr_param_chan_sub : Syntax.expr -> string -> string -> Syntax.expr

(** Substitute param_chan in side cmd *)
val cmd_param_chan_sub : Syntax.cmd -> string -> string -> Syntax.cmd

(** Replace parameter in an expression by the expression [expr_param expr_with_param expr] *)
val expr_param : Syntax.expr -> Syntax.expr -> Syntax.expr

(** Replace parameter in cmd by the expression *)
val cmd_param : Syntax.cmd -> Syntax.expr -> Syntax.cmd
