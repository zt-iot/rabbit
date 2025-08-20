open Rabbit_lib
open Rabbit_lib.Sets

open Alcotest


let increment x = x + 1

let test_increment () =
  check int "increment 3 -> 4" 4 (increment 3)



let test_subtype_1 () = 
  let secrecy_lattice = 
      (((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t"), true)
      :: ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t" |> ProcTySet.add "attacker_ty"), true)
      :: ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t"), true) :: [], Lattice_util.GreaterThanOrEqual) in 


  let integrity_lattice = 
    (((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t"), true)
      :: ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t" |> ProcTySet.add "attacker_ty"), true)
      :: ((ProcTySet.empty |> ProcTySet.add "alice_t", 
        ProcTySet.empty |> ProcTySet.add "alice_t" |> ProcTySet.add "bob_t"), true) :: [], Lattice_util.LessThanOrEqual) in 

  let arg_type = () in 

  let parameter_type = (Cst_syntax.TProd (
      (Cst_syntax.TSimple (Ident.global "message", []), (Lattice_util.Public, Lattice_util.Untrusted)), 
      (Cst_syntax.TSimple (Ident.global "signature", []), (Lattice_util.Public, Lattice_util.Untrusted))
  ), (Lattice_util.Public, Lattice_util.Untrusted)) in
  
  

  ()


let suite = ("Typechecker module", [test_case "test_increment" `Quick test_increment])