open Alcotest

open Rabbit_lib


let test_increment () =
  check int "increment 3 -> 4" 4 (Sample.increment 3)


let suite = ("Sample module", [test_case "double" `Quick test_increment])