open Rabbit_proverif_pv_parse

module Error : sig
  type error =
    | Unsupported of string
    | Invalid_input of string
    | Internal_error of string

  exception Error of error Location.located

  val print_error : error -> Format.formatter -> unit
end

val compile_program : Typed.decl list -> Pv_parser.program
