type extent

val dummy_ext : extent
val merge_ext : extent -> extent -> extent
val extent : Lexing.lexbuf -> extent
val parse_extent : unit -> extent
val set_start : Lexing.lexbuf -> extent -> unit
val input_error : string -> extent -> 'a
val input_warning : string -> extent -> unit
val user_error : string -> 'a
val internal_error : string -> 'a
val add_point_if_necessary : string -> string
val get_extent : bool -> extent -> string option
val get_extent_string : bool -> extent -> string
val get_mess_from : bool -> string -> string -> extent -> string
val display_input_error : string -> extent -> 'a

exception InputError of string * extent

val interactive_mode : bool ref
val get_warning_list : unit -> (string * extent) list
    
(*String parsing*)
val clear_buffer : unit -> unit
val get_string : unit -> string * extent
val set_start_pos : Lexing.lexbuf -> unit
val set_end_pos : Lexing.lexbuf -> unit
val add_char : char -> unit
val char_backslash : char -> char
