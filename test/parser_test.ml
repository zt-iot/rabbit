open Alcotest

open Rabbit_lib



let test_parser() = 
   let cwd = Sys.getcwd() in
   let _ = Printf.printf "Current working dir: %s\n" cwd in
   let fn2 = "../../../examples/camserver_simple_type_decls.txt" in
   let decls2, _ = Lexer.read_file Parser.file fn2 in
   let size2 = List.length decls2 in 
   check int "parser token size" size2 11

(* let test_greet () =
  check string "greet Alice" "Hello, Alice!" (greet "Alice") *)

let suite = ("Parser module", [test_case "double" `Quick test_parser])

(* let fn2 = "examples/camserver_simple_type_decls.txt" in
let decls2, parser_state2 = Lexer.read_file Parser.file fn2 in
let size2 = List.length decls2 in  *)