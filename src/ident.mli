type t = string * int
(** Name with stamp to avoid name crashes *)

val global : string -> t
(** Make a global variable with stamp 0.
    Note: no check of name collisions *)

val local : string -> t
(** Create a new ident with a fresh stamp *)

val is_global : t -> bool

val print : t -> Format.formatter -> unit

val to_string : t -> string
(** ["name__idx"] *)

val prefix : string -> t -> t
(** [prefix pre id] returns a new identifier by prefixing [pre]
    to the name of [id]. The result has the same stamp as [id]. *)

module Set : Set.S with type elt = t
