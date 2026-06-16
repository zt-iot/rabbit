type program = Pitptree.tdecl list * Pitptree.tprocess_e * Pitptree.tprocess_e option

val parse_lexbuf : filename:string -> Lexing.lexbuf -> program
val parse_channel : filename:string -> in_channel -> program
val parse_file : string -> program
val parse_string : ?filename:string -> string -> program
