open Rabbit_lib

open Rabbit_lib.Sets

open Alcotest

(* let access_lattice_testable = Alcotest.testable Lattice_util.pp_cst_access_policy Lattice_util.equal_cst_access_policy  *)

let access_lattice_testable_no_order = Alcotest.testable Lattice_util.pp_cst_access_policy Lattice_util.equal_cst_access_policy_no_order



let test_read_access_map_to_secrecy_lattice () = 

  let read_access_map = 
  Maps.SecurityTypeMap.empty  
  |> Maps.SecurityTypeMap.add (Ident.global "client_msg") 
    (ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "attacker_ty" |> ProcTySet.add "bob_t")
  |> Maps.SecurityTypeMap.add (Ident.global "client_sig") 
    (ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "attacker_ty" |> ProcTySet.add "bob_t")
  |> Maps.SecurityTypeMap.add (Ident.global "conn_client") 
    (ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t")
  |> Maps.SecurityTypeMap.add (Ident.global "sign_key_alice")
    (ProcTySet.empty |> ProcTySet.add "alice_t")
  |> Maps.SecurityTypeMap.add (Ident.global "udp_t") 
    (ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t") in 
    let expected_secrecy_lattice = 
      ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t"), true)
      :: ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t" |> ProcTySet.add "attacker_ty"), true)
      :: ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t"), true) :: [] in 

    let actual_secrecy_lattice = () in 

  let result = ((Rabbit_lib.To_cst.compute_access_relation read_access_map), Lattice_util.GreaterThanOrEqual) in 
  ()

let suite = ("To_cst module", [test_case "test_read_access_map_to_secrecy_lattice" `Quick test_read_access_map_to_secrecy_lattice])