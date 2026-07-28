open Rabbit_proverif_pv_parse

type program = Pv_parser.program

val pp_program : Format.formatter -> program -> unit
val to_string : program -> string
val to_string_with_parens : bool -> program -> string
val to_string_safe : program -> string * (unit, unit) result
