type t = string * int [@@deriving show]

val global : string -> t

val local : string -> t

val string_part : t -> string

val name : t -> string

val print : t -> Format.formatter -> unit

val to_string : t -> string
(** ["name__idx"] *)
