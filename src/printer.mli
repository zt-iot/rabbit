(* XXX not used for now *)
val print_type_class : Input.type_class -> string
val pprint_iv : string * int * int * int -> Format.formatter -> unit
val pprint_expr :
  Syntax.expr' Location.located -> 'a -> 'b
val pprint_event :
  Syntax.cmd' Location.located ->
  Format.formatter -> unit
val pprint_stmt : 'a Location.located -> Format.formatter -> unit
val pprint_atomic_stmt :
  Syntax.cmd' Location.located -> 'a -> 'b
val pprint_stmts :
  'a Location.located list -> Format.formatter -> unit
val pprint_context : Context.context -> Format.formatter -> unit
val pprint_definition :
  Context.definition -> Format.formatter -> unit
val pprint_access_policy :
  Context.access_policy -> Format.formatter -> unit
val pprint_system :
  ((string * Syntax.expr' Location.located) list *
   (string * string list * 'a Location.located list *
    (string * int * int * int))
     list * 'b Location.located list * string)
    list -> Format.formatter -> unit
