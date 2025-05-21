(** Translate Rabbit system to Tamarin format *)
val translate_sys : Context.system -> string list * string list -> Tamarin.tamarin
