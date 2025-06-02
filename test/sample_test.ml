open Alcotest

open Rabbit_lib
open Sample

let test_increment () =
  check int "increment 3 -> 4" 4 (increment 3)


let suite = ("A module", [test_case "double" `Quick test_increment])