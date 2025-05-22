val read_file : ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) -> string -> 'a * (string list * string list)
