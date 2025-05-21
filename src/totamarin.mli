(** Translate Rabbit system to Tamarin format

    [translate_sys context (used_idents, used_string)]
*)
val translate_sys : Context.system -> string list * string list -> Tamarin.tamarin
