type t = string * int

val global : string -> t
(** Make a global variable.  Note: no check of name collisions *)

val local : string -> t

val is_global : t -> bool

val name : t -> string

val print : t -> Format.formatter -> unit

val to_string : t -> string
(** ["name__idx"] *)

val prefix : string -> t -> t

module Set : Set.S with type elt = t
