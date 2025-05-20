(* XXX not used for now *)
val print_type_class : Input.type_class -> string
val pprint_iv : (string * int * int * int) Sig.printer
val pprint_expr : Syntax.expr -> 'a -> 'b (* xxx *)
val pprint_event : Syntax.cmd Sig.printer
val pprint_stmt : 'a Location.located Sig.printer (* xxx *)
val pprint_atomic_stmt : Syntax.cmd Sig.printer
val pprint_stmts : 'a Location.located list Sig.printer (* xxx *)
val pprint_context : Context.context Sig.printer
val pprint_definition : Context.definition Sig.printer
val pprint_access_policy : Context.access_policy Sig.printer
val pprint_system :
  ((string * Syntax.expr' Location.located) list *
   (string * string list * 'a Location.located list *
    (string * int * int * int))
     list * 'b Location.located list * string) list Sig.printer
