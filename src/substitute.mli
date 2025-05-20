type substitute_error =
    AccessError of string
  | PremissionError of string
  | UnintendedError of string

include Sig.ERROR with type error := substitute_error

val expr_chan_sub :
  Syntax.expr ->
  string ->
  Syntax.expr ->
  Syntax.expr

val fact_chan_sub :
  Syntax.fact ->
  string ->
  Syntax.expr ->
  Syntax.fact

val facts_chan_sub :
  Syntax.fact list ->
  string ->
  Syntax.expr ->
  Syntax.fact list

val cmd_chan_sub :
  Syntax.cmd ->
  string ->
  Syntax.expr -> Syntax.cmd

val expr_param_chan_sub :
  Syntax.expr ->
  string -> string -> Syntax.expr

val fact_param_chan_sub :
  Syntax.fact ->
  string -> string -> Syntax.fact

val facts_param_chan_sub :
  Syntax.fact list ->
  string ->
  string -> Syntax.fact list

val cmd_param_chan_sub :
  Syntax.cmd ->
  string -> string -> Syntax.cmd

val expr_param :
  Syntax.expr ->
  Syntax.expr -> Syntax.expr

val fact_param :
  Syntax.fact ->
  Syntax.expr ->
  Syntax.fact

val facts_param :
  Syntax.fact list ->
  Syntax.expr ->
  Syntax.fact list

val cmd_param :
  Syntax.cmd ->
  Syntax.expr -> Syntax.cmd
