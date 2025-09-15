open Rabbit_lib
open Rabbit_lib.Sets

open Alcotest



let suite = ("Lattice_util module", [test_case "test_read_access_map_to_secrecy_lattice" `Quick test_read_access_map_to_secrecy_lattice])