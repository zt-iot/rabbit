type t = string * int

val global : string -> t

val local : string -> t

val name : t -> string

val print : t -> Format.formatter -> unit
