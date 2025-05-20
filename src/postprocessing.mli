type postprocessing_error

exception Error of postprocessing_error

val print_error : postprocessing_error -> Format.formatter -> unit

val optimize : Totamarin.model -> Totamarin.model
