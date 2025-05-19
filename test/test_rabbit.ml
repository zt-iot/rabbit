open OUnit2
open Parser
open Input

let test_typ_parser _ =
  let parsed = parse_typ_from_string "data bool" in
  assert_equal DeclSimpleTypeSimpleTyp("bool", []) parsed;

let suite =
  "Parser tests" >::: [
    "Parse typ" >:: test_typ_parser
  ]

let () =
  run_test_tt_main suite