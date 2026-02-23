open Parser

let reserved =
  [ "graph", GRAPH
  ; "digraph", DIGRAPH
  ; "strict", STRICT
  ; "node", NODE
  ; "edge", EDGE
  ; "subgraph", SUBGRAPH
  ]
;;

let digit = [%sedlex.regexp? '0' .. '9']

(* for graph parser *)
let name =
  [%sedlex.regexp?
    ( ('_' | alphabetic), Star ('_' | alphabetic | digit)
    | Opt '-', ('.', Plus digit | Plus digit, Opt ('.', Star digit)) )]
;;

let newline = [%sedlex.regexp? '\n' | '\r' | "\n\r" | "\r\n"]
let hspace = [%sedlex.regexp? ' ' | '\t' | '\r']
let comment_line = [%sedlex.regexp? "//", Star (Compl '\n'), '\n']
let start_longcomment = [%sedlex.regexp? "/*"]
let end_longcomment = [%sedlex.regexp? "*/"]
let c_line = [%sedlex.regexp? "\n#", Star (Compl '\n'), '\n']

(* for record node parser *)
let structural_char_rc =
  [%sedlex.regexp? '{' | '}' | '|' | '<' | '>' | '(' | ')' | ',' | '[' | ']' | ':']
;;

let hspace_rc = [%sedlex.regexp? ' ' | '\t' | '\r' | '\n']
let port_inner = [%sedlex.regexp? Star (alphabetic | digit | '_')]
let timestamp = [%sedlex.regexp? Star (alphabetic | digit | '_' | '.')]

(* for substitution parser *)
let structural_char_st = [%sedlex.regexp? '<' | '>' | '=']
let text_escaped_char = [%sedlex.regexp? '\\', any]
let hspace_st = [%sedlex.regexp? ' ' | '\t' | '\r' | '\n']
let tag_content = [%sedlex.regexp? Star (Compl '>')]

let text_content =
  [%sedlex.regexp? Plus (Compl (hspace_st | structural_char_st) | text_escaped_char)]
;;

let loc_of lex = Location.make lex.Ulexbuf.pos_start lex.Ulexbuf.pos_end

let rec token_gr ({ Ulexbuf.end_of_input; _ } as lexbuf) =
  if end_of_input then EOF else token_gr_aux lexbuf

and token_gr_aux ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | comment_line ->
      f ();
      Ulexbuf.new_line lexbuf;
      token_gr_aux lexbuf
  | c_line ->
      f ();
      Ulexbuf.new_line lexbuf;
      Ulexbuf.new_line lexbuf;
      token_gr_aux lexbuf
  | "--" | "->" ->
      f ();
      EDGEOP
  | '{' ->
      f ();
      LBRA
  | '}' ->
      f ();
      RBRA
  | ',' ->
      f ();
      COMMA
  | '[' ->
      f ();
      LSBRA
  | ']' ->
      f ();
      RSBRA
  | ':' ->
      f ();
      COLON
  | ';' ->
      f ();
      SEMICOLON
  | '=' ->
      f ();
      EQ
  | '+' ->
      f ();
      PLUS
  | start_longcomment ->
      f ();
      comments_gr 0 lexbuf
  | '"' ->
      f ();
      double_quote_gr "" lexbuf
  | name ->
      f ();
      let n = Ulexbuf.lexeme lexbuf in
      (try List.assoc n reserved with
       | Not_found ->
           Ulexbuf.record_ident n lexbuf;
           ID n)
  | '<' ->
      f ();
      html_gr 0 "<" lexbuf
  | Plus hspace ->
      f ();
      token_gr_aux lexbuf
  | newline ->
      f ();
      Ulexbuf.new_line lexbuf;
      token_gr_aux lexbuf
  | eof ->
      f ();
      EOF
  | any ->
      f ();
      let w = Ulexbuf.lexeme lexbuf in
      let loc = loc_of lexbuf in
      Ulexbuf.error ~loc (Ulexbuf.Unexpected w)
  | _ -> assert false

and comments_gr level ({ Ulexbuf.stream; _ } as lexbuf) =
  match%sedlex stream with
  | end_longcomment ->
      if level = 0
      then (
        Ulexbuf.update_pos lexbuf;
        token_gr lexbuf)
      else comments_gr (level - 1) lexbuf
  | start_longcomment -> comments_gr (level + 1) lexbuf
  | newline ->
      Ulexbuf.new_line lexbuf;
      comments_gr level lexbuf
  | eof -> Ulexbuf.error ~loc:(loc_of lexbuf) Ulexbuf.UnclosedComment
  | any -> comments_gr level lexbuf
  | _ -> assert false

and double_quote_gr cur ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | "\\\"" ->
      f ();
      double_quote_gr (cur ^ "\\\"") lexbuf
  | newline ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      Ulexbuf.new_line lexbuf;
      double_quote_gr (cur ^ s) lexbuf
  | '"' ->
      f ();
      ID_DQUOTE cur
  | eof -> Ulexbuf.error ~loc:(loc_of lexbuf) Ulexbuf.UnclosedQuote
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      double_quote_gr (cur ^ s) lexbuf
  | _ -> assert false

and html_gr level cur ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | '>' ->
      f ();
      if level = 0 then ID_HTML (cur ^ ">") else html_gr (level - 1) (cur ^ ">") lexbuf
  | '<' ->
      f ();
      html_gr (level + 1) (cur ^ "<") lexbuf
  | newline ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      Ulexbuf.new_line lexbuf;
      html_gr level (cur ^ s) lexbuf
  | eof -> Ulexbuf.error ~loc:(loc_of lexbuf) Ulexbuf.UnclosedHTML
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      html_gr level (cur ^ s) lexbuf
  | _ -> assert false
;;

let rec token_rc ({ Ulexbuf.end_of_input; _ } as lexbuf) =
  if end_of_input then EOF else token_rc_aux lexbuf

and token_rc_aux ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | '{' ->
      f ();
      LBRA
  | '}' ->
      f ();
      RBRA
  | '|' ->
      f ();
      PIPE
  | '(' ->
      f ();
      LPAR
  | ')' ->
      f ();
      RPAR
  | ',' ->
      f ();
      COMMA
  | '[' ->
      f ();
      LSBRA
  | ']' ->
      f ();
      RSBRA
  | ':' ->
      f ();
      COLON
  | "\\<" | "&lt;" ->
      f ();
      LT
  | "\\>" | "&gt;" ->
      f ();
      GT
  | "'" ->
      f ();
      squote_rc "" lexbuf
  | '"' ->
      f ();
      dquote_rc "" lexbuf
  | "&nbsp;" | "\\l" ->
      f ();
      token_rc_aux lexbuf
  | Plus hspace_rc ->
      f ();
      token_rc_aux lexbuf
  | eof ->
      f ();
      EOF
  | '<', port_inner, '>' ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      let id = String.sub s 1 (String.length s - 2) in
      PORT_ID id
  | '#', timestamp ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      let ts = String.sub s 1 (String.length s - 1) in
      TIMESTAMP ts
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      lex_text_continuation s lexbuf
  | _ ->
      let w = Ulexbuf.lexeme lexbuf in
      let codes =
        String.fold_left (fun acc c -> acc ^ string_of_int (Char.code c) ^ " ") "" w
      in
      failwith (Printf.sprintf "Lexer error: unexpected char '%s' (codes: %s)" w codes)

(* combine strings splitted by "&nbsp;" and "\\l" *)
and lex_text_continuation cur ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | "&nbsp;" | "\\l" | Plus hspace_rc ->
      f ();
      lex_text_continuation cur lexbuf
  | eof | structural_char_rc | "\\<" | "\\>" | "&lt;" | "&gt;" ->
      Sedlexing.rollback stream;
      TEXT cur
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      lex_text_continuation (cur ^ s) lexbuf
  | _ -> assert false

and squote_rc cur ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | "\\\'" ->
      f ();
      squote_rc (cur ^ "\\\'") lexbuf
  | "&nbsp" | "\\l" | Plus hspace_rc ->
      f ();
      squote_rc cur lexbuf
  | "'" ->
      f ();
      TEXT cur
  | eof -> Ulexbuf.error ~loc:(loc_of lexbuf) Ulexbuf.UnclosedQuote
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      squote_rc (cur ^ s) lexbuf
  | _ -> assert false

and dquote_rc cur ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | "\\\"" ->
      f ();
      dquote_rc (cur ^ "\\\"") lexbuf
  | "&nbsp;" | "\\l" | Plus hspace_rc ->
      f ();
      dquote_rc cur lexbuf
  | '"' ->
      f ();
      TEXT cur
  | eof -> Ulexbuf.error ~loc:(loc_of lexbuf) Ulexbuf.UnclosedQuote
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      dquote_rc (cur ^ s) lexbuf
  | _ -> assert false
;;

let rec token_st ({ Ulexbuf.end_of_input; _ } as lexbuf) =
  if end_of_input then EOF else token_st_aux lexbuf

and token_st_aux ({ Ulexbuf.stream; _ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | Plus hspace_st ->
      f ();
      token_st_aux lexbuf
  | eof ->
      f ();
      EOF
  | '<', "TABLE", tag_content, '>' ->
      f ();
      TABLE_L
  | '<', "/TABLE", '>' ->
      f ();
      TABLE_R
  | '<', "TR", tag_content, '>' ->
      f ();
      TR_L
  | '<', "/TR", '>' ->
      f ();
      TR_R
  | '<', "TD", tag_content, '>' ->
      f ();
      TD_L
  | '<', "/TD", '>' ->
      f ();
      TD_R
  | '<', "FONT", tag_content, '>' ->
      f ();
      FONT_L
  | '<', "/FONT", '>' ->
      f ();
      FONT_R
  | '=' ->
      f ();
      EQ
  | text_content ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      TEXT s
  | any ->
      f ();
      let s = Ulexbuf.lexeme lexbuf in
      TEXT s
  | _ -> assert false
;;

let run
      (lexer : Ulexbuf.t -> 'a)
      (parser : (Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'b)
      (lexbuf : Ulexbuf.t)
  : 'b
  =
  let lexer () =
    let token = lexer lexbuf in
    token, lexbuf.Ulexbuf.pos_start, lexbuf.Ulexbuf.pos_end
  in
  let parser = MenhirLib.Convert.Simplified.traditional2revised parser in
  try parser lexer with
  | Parser.Error ->
      let w = Ulexbuf.lexeme lexbuf in
      let loc = loc_of lexbuf in
      Ulexbuf.error ~loc (Ulexbuf.Unexpected w)
  | Sedlexing.MalFormed ->
      let loc = loc_of lexbuf in
      Ulexbuf.error ~loc Ulexbuf.MalformedUTF8
;;

let read_file lexer parse fn =
  let fh = open_in fn in
  let lex = Ulexbuf.from_channel ~fn fh in
  let terms = run lexer parse lex in
  close_in fh;
  terms
;;

let read_string lexer parse s =
  let lex = Ulexbuf.from_string s in
  run lexer parse lex
;;
