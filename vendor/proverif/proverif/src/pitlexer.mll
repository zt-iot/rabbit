{
open Parsing_helper
open Pitparser

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

let comment_depth = ref 0
let comment_extent_list = ref []

(* Typed front-end *)

let keyword_table =
  create_hashtable 11
[ "type", TYPE;
  "set", SET;
  "forall", FORALL;
  "fail", FAIL;
  "or", ORTEXT;
  "const", CONST;
  "letfun", LETFUN;
  "channel", CHANNEL;
  "def", DEFINE;
  "expand", EXPAND;
  "yield", YIELD;
  "proba", PROBA;
  "letproba", LETPROBA;
  "proof", PROOF;
  "implementation", IMPLEMENTATION;
  "foreach", FOREACH;
  "do", DO;
  "secret", SECRET;
  "public_vars", PUBLICVARS;
(* Tables of keys *)
  "table", TABLE;
  "insert", INSERT;
  "get", GET;
(* Common keywords *)
  "param", PARAM;
  "new", NEW;
  "out", OUT;
  "in", IN;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "fun", FUN;
  "equation", EQUATION;
  "reduc", REDUCTION;
  "pred", PREDICATE;
  "process", PROCESS;
  "let", LET;
  "query", QUERY;
  "putbegin", PUTBEGIN;
  "noninterf", NONINTERF;
  "event", EVENT;
  "not", NOT;
  "elimtrue", ELIMTRUE;
  "free", FREE;
  "clauses", CLAUSES;
  "suchthat", SUCHTHAT;
  "nounif", NOUNIF;
  "select", SELECT;
  "noselect", NOUNIF;
  "phase", PHASE;
  "sync", BARRIER;
  "among", AMONG;
  "weaksecret", WEAKSECRET;
  "equivalence", EQUIVALENCE;
  "otherwise", OTHERWISE;
  "choice", CHOICE;
  "diff", CHOICE;
  "lemma", LEMMA;
  "axiom", AXIOM;
  "restriction", RESTRICTION;
  "for", FOR]

}

rule token = parse
  "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; token lexbuf }
| [ ' ' '\009' '\012' ] +
     { token lexbuf }
| [ 'a'-'z' 'A'-'Z' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { let s = Lexing.lexeme lexbuf in
	 try
	   Hashtbl.find keyword_table s
         with
           Not_found ->
             IDENT (s, extent lexbuf)
     }
| [ '~' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { if !Param.allow_tilde then
         let s = Lexing.lexeme lexbuf in
         IDENT (s, extent lexbuf)
       else
         input_error "~ not allowed." (extent lexbuf)
     }
| '@' { AT }
| '\"'
    {
      clear_buffer ();
      set_start_pos lexbuf;
      string lexbuf;
      STRING (get_string ()) }
| ([ '0'-'9' ]) +
    {
      try
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	input_error "Incorrect integer" (extent lexbuf)
    }
| [ '0'-'9' ]+ ((('.' [ '0'-'9' ]*)? ['e' 'E'] ['+' '-']? [ '0'-'9' ]+) |  '.' [ '0'-'9' ]+)
     { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
| ([ '0'-'9' ])+ "-proj-" [ 'a'-'z' 'A'-'Z' '0'-'9' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' '-' ] )*)
    {
      PROJECTION(Lexing.lexeme lexbuf, extent lexbuf)
    }
| "(*"
    {
      comment_depth := 1;
      comment_extent_list := (extent lexbuf) :: !comment_extent_list;
      comment lexbuf;
      token lexbuf
    }
| "optim-if" { OPTIMIF }
| "is-cst" { ISCST }
| '#' { COUNT }
| ',' { COMMA }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '{' { LBRACE }
| '}' { RBRACE }
| '|' { BAR }
| "||" { OR }
| "&&" { WEDGE }
| ';' { SEMI }
| '!' { REPL }
| '=' { EQUAL }
| '/' { SLASH }
| '.' { DOT }
| '*' { STAR }
| ':' { COLON }
| '+' { PLUS }
| '-' { MINUS }
| '^' { POWER }
| "->" { RED }
| "<=" { LEQ }
| "<->" { EQUIV }
| "<=>" { EQUIVEQ }
| "<>" { DIFF }
| "==>" { BEFORE }
| "<" { LESS }
| ">=" { GEQ }
| ">" { GREATER }
| "<-" { LEFTARROW }
| "<-R" { RANDOM }
| "inj-event" { INJEVENT }
| '_' { UNDERSCORE (extent lexbuf) }
| eof { EOF }
| _ { input_error "Illegal character" (extent lexbuf) }

and comment = parse
| "(*" {
    incr comment_depth;
    comment_extent_list := (extent lexbuf) :: !comment_extent_list;
    comment lexbuf }
| "*)"
    {
      decr comment_depth;
      comment_extent_list := List.tl !comment_extent_list;
      if !comment_depth = 0 then () else comment lexbuf
    }
| "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; comment lexbuf }
| eof { input_error "Unterminated comment" (List.hd !comment_extent_list) }
| _ { comment lexbuf }

and string = parse
| '\"' { set_end_pos lexbuf }
| '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r']
      {
        add_char (char_backslash (Lexing.lexeme_char lexbuf 1));
        string lexbuf
      }
| '\\' _
      { input_error "Illegal escape" (extent lexbuf) }
| "\010" | "\013"
     { Lexing.new_line lexbuf;
       add_char (Lexing.lexeme_char lexbuf 0);
       string lexbuf }
| "\013\010"
     { Lexing.new_line lexbuf;
       add_char (Lexing.lexeme_char lexbuf 0);
       add_char (Lexing.lexeme_char lexbuf 1);
       string lexbuf  }
| eof
      { input_error "Unterminated string" (extent lexbuf) }
| _
      {
        add_char (Lexing.lexeme_char lexbuf 0);
        string lexbuf
      }

and swap_token = parse
  "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; swap_token lexbuf }
| [ ' ' '\009' '\012' ] +
     { swap_token lexbuf }
| [ '@' 'a'-'z' 'A'-'Z' ] (( [ '@' 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { let s = Lexing.lexeme lexbuf in
        TAG (s, extent lexbuf)
     }
| "(*" {
         comment lexbuf;
         swap_token lexbuf
       }
| ';' { SEMI }
| "->" { RED }
| eof { EOF }
| _ { input_error "Illegal character" (extent lexbuf) }
