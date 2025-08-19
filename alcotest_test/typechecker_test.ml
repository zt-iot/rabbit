(* open Rabbit_lib *)

open Alcotest



let increment x = x + 1

let test_increment () =
  check int "increment 3 -> 4" 4 (increment 3)


let suite = ("Typechecker module", [test_case "double" `Quick test_increment])