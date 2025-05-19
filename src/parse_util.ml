let parse_typ_from_string (s : string) : Ast.typ =
  let lexbuf = Lexing.from_string s in
  Parser.plain_decl Lexer.tokenize lexbuf