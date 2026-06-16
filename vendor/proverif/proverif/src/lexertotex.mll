{
open Parsing_helper
open Piptree
open Fileprint

type kind =
    Keyword
  | Fun
  | Cst
  | Pred

let kinds = Hashtbl.create 7

let init_kinds d = 
  Hashtbl.iter (fun keyw _ -> Hashtbl.add kinds keyw "\\kwl") Pilexer.keyword_table;
  List.iter (function
      FunDecl((f,_),_,_) -> Hashtbl.add kinds f "\\kwf"
    | DataFunDecl((f,_),_) -> Hashtbl.add kinds f "\\kwf"
    | Reduc((((PFunApp((f,_),_) ,_),_)::_),_) -> Hashtbl.add kinds f "\\kwf"
    | ReducFail((((PFunApp((f,_),_) ,_),_,_)::_),_) -> Hashtbl.add kinds f "\\kwf"
    | PredDecl((p,_),_,_) -> Hashtbl.add kinds p "\\kwp"
    | Free(l,_) -> List.iter (fun (c,_) -> Hashtbl.add kinds c "\\kwc") l
    | _ -> ()) d

let parse filename = 
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let ptree =
      try
        Piparser.all Pilexer.token lexbuf
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
     { print_string "$\\\\\n$"; token lexbuf }
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
           let k = Hashtbl.find kinds s in
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
| ([ '0'-'9' ]) +
     { print_string (Lexing.lexeme lexbuf); token lexbuf }
| "(*" {
         print_string "\\textit{(*";
         comment lexbuf
       }
| ',' (' ' *) { print_string ", "; token lexbuf }
| '(' { print_string "("; token lexbuf }
| ')' { print_string ")"; token lexbuf }
| '[' { print_string "["; token lexbuf }
| ']' { print_string "]"; token lexbuf }
| (' ' *) '|' (' ' *) { print_string "\\mid"; token lexbuf }
| ';' { print_string ";"; token lexbuf }
| '!' { print_string "!"; token lexbuf }
| (' ' *) '=' (' ' *) { print_string " = "; token lexbuf }
| '/' { print_string "/"; token lexbuf }
| '.' { print_string "."; token lexbuf }
| '*' { print_string "*"; token lexbuf }
| ':' { print_string "{:}"; token lexbuf }
| '&' { print_string "\\&"; token lexbuf }
| (' ' *) "->" (' ' *) { print_string (if !nice_tex then "\\rightarrow" else "\\ {-}{>}\\ "); token lexbuf }
| (' ' *) "<->" (' ' *) { print_string (if !nice_tex then "\\leftrightarrow" else "\\ {<}{-}{>}\\ "); token lexbuf }
| (' ' *) "<=>" (' ' *) { print_string (if !nice_tex then "\\Leftrightarrow" else "\\ {<}{=}{>}\\ "); token lexbuf }
| (' ' *) "<>" (' ' *) { print_string (if !nice_tex then "\\neq" else "\\ {<}{>}\\ "); token lexbuf }
| (' ' *) "==>" (' ' *) { print_string (if !nice_tex then "\\Longrightarrow" else "\\ {=}{=}{>}\\ "); token lexbuf }
| eof {  print_string "$\n\\end{tabbing}\n" }	
| _ { internal_error ((get_extent_string true (extent lexbuf)) ^ "Illegal character (should have been detected in previous pass)") }

and comment = parse
| "*)" { print_string "*)}";
         token lexbuf }
| "\010" | "\013" | "\013\010"
     { print_string "}$\\\\\n$\\textit{"; comment lexbuf }
| eof { print_string "}$\n\\end{tabbing}\n" }
| _ { print_sanitize (Lexing.lexeme lexbuf); comment lexbuf }

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
  let d,_ = parse f in
  init_kinds d;
  convert f 

} 
