let nice_tex = ref true

let preamble = "
\\documentclass{article}
\\usepackage[utf8]{inputenc}
\\newcommand{\\kwl}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\kwc}[1]{\\mathsf{#1}}
\\newcommand{\\kwp}[1]{\\mathsf{#1}}
\\newcommand{\\kwt}[1]{\\mathsf{#1}}
\\newcommand{\\kwe}[1]{\\mathsf{#1}}
\\newcommand{\\kwtable}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\getR}{\\stackrel{R}{\\leftarrow}}
\\begin{document}
"

let postamble = "
\\end{document}
"

let printed_preamble = ref false

let outfile = ref ""

let outchannel = ref stdout

let print_string s = 
  output_string (!outchannel) s

let print_sanitize s = 
  for i = 0 to String.length s - 1 do
    match s.[i] with
      '\\' -> print_string "{\\textbackslash}"
    | '&' -> print_string "\\ensuremath{\\&}"
    | '{' -> print_string "\\ensuremath{\\{}"
    | '}' -> print_string "\\ensuremath{\\}}"
    | '_' -> print_string "{\\_}"
    | '^' -> print_string "{\\string^}"
    | '#' -> print_string "\\#"
    | '$' -> print_string "\\$"
    | '%' -> print_string "\\%"
    | '@' -> print_string "{\\string@}"
    | '~' -> print_string "{\\string~}"
    | '>' -> print_string "\\ensuremath{>}"
    | '<' -> print_string "\\ensuremath{<}"
    | ' ' -> print_string "\\ "
    | '\009' -> print_string "\\qquad\\qquad "
    | '\000'..'\031' -> () (* ignore control characters; tab handled above; 
			      line breaks handled in the lexer *)
    | c -> output_char (!outchannel) c
  done

let print_preamble() =
  if not (!printed_preamble) then
    begin
      printed_preamble := true;
      print_string preamble
    end
  
let close () =
  if (!printed_preamble) then
    print_string postamble;
  if (!outfile) != "" then
    close_out (!outchannel)

