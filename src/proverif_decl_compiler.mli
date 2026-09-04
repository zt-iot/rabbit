open Rabbit_proverif_pv_parse

module Error : sig
  type error =
    | Unsupported of string
    | Invalid_input of string
    | Internal_error of string

  include Error.S with type error := error
end

val compile_program : Typed.decl list -> Pv_parser.program
