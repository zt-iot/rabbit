type program = Pitptree.tdecl list * Pitptree.tprocess_e * Pitptree.tprocess_e option

let parse_lexbuf ~filename (lexbuf : Lexing.lexbuf) =
  Param.reset ();
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  Pitparser.all Pitlexer.token lexbuf

let parse_channel ~filename ic =
  parse_lexbuf ~filename (Lexing.from_channel ic)

let parse_file filename =
  let ic = open_in_bin filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> parse_channel ~filename ic)

let parse_string ?(filename = "<string>") source =
  parse_lexbuf ~filename (Lexing.from_string source)
