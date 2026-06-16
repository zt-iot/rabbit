{
open Parsing_helper
open Pitptree
open Fileprint

let comment_depth = ref 0
let comment_extent_list = ref []

let kinds = Hashtbl.create 7

let rec get_top_symbol_reduc = function
  | EETerm (PFunApp(("=",_), [(PFunApp((f,ext),_),_);_]),_) -> (f,ext)
  | EETerm (PFunApp(("=",_), [(_, ext1);_]),_) ->
      input_error ("In \"reduc\", all rewrite rules should begin with function application") ext1
  | EETerm (_,ext1) ->
      input_error ("In \"reduc\", all rewrite rules should be an equality between two terms") ext1
  | EELet (_,_,eq) -> get_top_symbol_reduc eq

let init_kinds d =
  Hashtbl.iter (fun keyw _ -> Hashtbl.add kinds keyw "\\kwl") Pitlexer.keyword_table;
  Hashtbl.add kinds "channel" "\\kwt";
  Hashtbl.add kinds "bitstring" "\\kwt";
  Hashtbl.add kinds "bool" "\\kwt";
  Hashtbl.add kinds "true" "\\kwc";
  Hashtbl.add kinds "false" "\\kwc";
  List.iter (function
      TTypeDecl(t,_) -> Hashtbl.add kinds t "\\kwt"
    | TFunDecl((f,_),_,_,_) -> Hashtbl.add kinds f "\\kwf"
    | TReducFail((f,_),_,_,_,_) -> Hashtbl.add kinds f "\\kwf"
    | TReduc(((_,t)::_),_) ->
        let (f,_) = get_top_symbol_reduc t in
        Hashtbl.add kinds f "\\kwf"
    | TPredDecl((p,_),_,_) -> Hashtbl.add kinds p "\\kwp"
    | TFree((c,_),_,_) -> Hashtbl.add kinds c "\\kwc"
    | TConstDecl((c,_),_,_) -> Hashtbl.add kinds c "\\kwc"
    | TTableDecl((t,_),_) -> Hashtbl.add kinds t "\\kwt"
    | TEventDecl((e,_),_) -> Hashtbl.add kinds e "\\kwe"
    | TLetFun((f,_),_,_) -> Hashtbl.add kinds f "\\kwf"
    | _ -> ()) d

let parse filename =
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let ptree =
      try
        Pitparser.all Pitlexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s)

}

rule token = parse
  "\010" | "\013" | "\013\010"
    { print_string " $\\\\\n$";
      Lexing.new_line lexbuf; token lexbuf }
| ' '
     { print_string "\\ "; token lexbuf }
| '\009'
     { print_string "\\qquad\\qquad "; token lexbuf }
| [ '\012' ] +
     { token lexbuf }
| [ 'a'-'z' 'A'-'Z' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     {
       let s = Lexing.lexeme lexbuf in
       begin
	 try
           let k = Hashtbl.find kinds s  in
	   print_string (k ^ "{");
	   print_sanitize s;
	   print_string "}"
	 with Not_found ->
	   print_string "\\var{";
	   print_sanitize s;
	   print_string "}"
       end;
       token lexbuf
     }
| '@' { print_string "\\string@"; token lexbuf  }
| '\"'
    { print_string "\\textit{\"";
      string lexbuf }
| ([ '0'-'9' ]) + | '(' | ')' | '[' | ']' | ';' | '!' | '/' | '.' | '*'
     { print_string (Lexing.lexeme lexbuf); token lexbuf }
| "(*" {
      comment_depth := 1;
      comment_extent_list := (extent lexbuf) :: !comment_extent_list;
         print_string "\\textit{(*";
         comment lexbuf
       }
| ',' (' ' *) { print_string ", "; token lexbuf }
| '{' { print_string "\\{"; token lexbuf }
| '}' { print_string "\\}"; token lexbuf }
| (' ' *) '|' (' ' *) { print_string "\\mid"; token lexbuf }
| (' ' *) "||" (' ' *) { print_string (if !nice_tex then "\\vee" else "\\mid\\mid"); token lexbuf }
| (' ' *) "&&" (' ' *) { print_string (if !nice_tex then "\\wedge" else "\\ \\&\\&\\ "); token lexbuf }
| (' ' *) '=' (' ' *) { print_string " = "; token lexbuf }
| ':' { print_string "{:}"; token lexbuf }
| (' ' *) "+" (' ' *) { print_string " + "; token lexbuf }
| (' ' *) "-" (' ' *) { print_string " - "; token lexbuf }
| (' ' *) "->" (' ' *) { print_string (if !nice_tex then "\\rightarrow " else "\\ {-}{>}\\ "); token lexbuf }
| (' ' *) "<=" (' ' *) { print_string (if !nice_tex then "\\leq " else "\\ {<}{=}\\ "); token lexbuf }
| (' ' *) "<->" (' ' *) { print_string (if !nice_tex then "\\leftrightarrow " else "\\ {<}{-}{>}\\ "); token lexbuf }
| (' ' *) "<=>" (' ' *) { print_string (if !nice_tex then "\\Leftrightarrow " else "\\ {<}{=}{>}\\ "); token lexbuf }
| (' ' *) "<>" (' ' *) { print_string (if !nice_tex then "\\neq " else "\\ {<}{>}\\ "); token lexbuf }
| (' ' *) "==>" (' ' *) { print_string (if !nice_tex then "\\Longrightarrow " else "\\ {=}{=}{>}\\ "); token lexbuf }
| (' ' *) "<" (' ' *) { print_string " < "; token lexbuf }
| (' ' *) ">=" (' ' *) { print_string (if !nice_tex then "\\geq " else "\\ {>}{=}\\ "); token lexbuf }
| (' ' *) ">" (' ' *) { print_string " > "; token lexbuf }
| (' ' *) "<-" (' ' *) { print_string (if !nice_tex then "\\leftarrow " else "\\ {<}{-}\\ "); token lexbuf }
| (' ' *) "<-R" (' ' *) { print_string (if !nice_tex then "\\getR " else "\\ {<}{-}{R}\\ "); token lexbuf }
| "inj-event" { print_string "\\kwl{inj\\textbf{-}event}"; token lexbuf }
| eof {  print_string "$\n\\end{tabbing}\n" }
| _ { internal_error ((get_extent_string true (extent lexbuf)) ^ "Illegal character (should have been detected in previous pass)") }

and comment = parse
| "(*" {
    print_string "(*";
    incr comment_depth;
    comment_extent_list := (extent lexbuf) :: !comment_extent_list;
    comment lexbuf }
| "*)"
    {
      print_string "*)";
      decr comment_depth;
      comment_extent_list := List.tl !comment_extent_list;
      if !comment_depth = 0 then
      begin
        print_string "}"; 
        token lexbuf
      end
      else comment lexbuf
    }
| "\010" | "\013" | "\013\010"
     { print_string "}$\\\\\n$\\textit{"; 
       Lexing.new_line lexbuf; comment lexbuf }
| eof { internal_error ((get_extent_string true (List.hd !comment_extent_list)) ^ "Unterminated comment") }
| _ { print_sanitize (Lexing.lexeme lexbuf); comment lexbuf }

and string = parse
| "\"" { print_string "\"}";
         token lexbuf }
| "\010" | "\013" | "\013\010"
    { print_string "}$\\\\\n$\\textit{";
      Lexing.new_line lexbuf; string lexbuf }
| eof
    { internal_error ((get_extent_string true (extent lexbuf)) ^ "Unterminated string (should have been detected in previous pass)") }
| _ { print_sanitize (Lexing.lexeme lexbuf); string lexbuf }

{

let convert filename =
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    print_preamble();
    print_string "\\begin{tabbing}\n$";
    token lexbuf;
    close_in ic
  with Sys_error s ->
    user_error ("File error: " ^ s)

let converttotex f =
  let (d,_,_) = parse f in
  init_kinds d;
  convert f

}
