open Alcotest

open Rabbit_lib

let rabbit_ty_testable = Alcotest.testable Typechecker.pp_rabbit_ty Typechecker.equal_rabbit_ty


let increment x = x + 1


let test_increment () =
  check int "increment 3 -> 4" 4 (increment 3)

let suite = ("Typechecker module", [
  test_case "test_increment" `Quick test_increment; 
  ])