{
open Parsing_helper
open Piparser

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

(* Untyped front-end *)

let keyword_table =
  create_hashtable 11
[ "data", DATA;
  "param", PARAM;
  "private", PRIVATE;
(* Common keywords *)
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
  "phase", PHASE;
  "sync", BARRIER;
  "among", AMONG;
  "weaksecret", WEAKSECRET;
  "choice", CHOICE;
  "diff", CHOICE;
  "otherwise", OTHERWISE;
  "can", CANTEXT;
  "fail", FAIL;
  "where", WHERE]

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
| '\"' (( [ ' ' '!' '#'-'[' ']'-'~' '\192'-'\214' '\216'-'\246' '\248'-'\255' ] )*) '\"'
    { let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2), extent lexbuf)
    } 
| ([ '0'-'9' ]) +
    { 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	input_error "Incorrect integer" (extent lexbuf)
    }
| "(*" {
         comment lexbuf;
         token lexbuf
       }
| ',' { COMMA }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '|' { BAR }
| ';' { SEMI }
| '!' { REPL }
| '=' { EQUAL }
| '/' { SLASH }
| '.' { DOT }
| '*' { STAR }
| ':' { COLON }
| '&' { WEDGE }
| "->" { RED } 
| "<->" { EQUIV } 
| "<=>" { EQUIVEQ } 
| "<>" { DIFF }
| "==>" { BEFORE }
| eof { EOF }	
| _ { input_error "Illegal character" (extent lexbuf) }

and comment = parse
| "*)" { }
| "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; comment lexbuf }
| eof { }
| _ { comment lexbuf }
