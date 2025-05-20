type substitute_error =
    AccessError of string
  | PremissionError of string
  | UnintendedError of string

exception Error of substitute_error Location.located

val error : loc:Location.t -> substitute_error -> 'error

val print_error : substitute_error -> Format.formatter -> unit

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
