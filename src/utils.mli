val run : string -> int * string list
(** Sub-shell calls *)

val runf : ('a, unit, string, int * string list) format4 -> 'a
(** Sub-shell calls with format interface *)
