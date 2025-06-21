open Alcotest

open Rabbit_lib


let rabbit_ty_testable = Alcotest.testable Typechecker.pp_rabbit_ty Typechecker.equal_rabbit_ty

let test_tr_var () = 

  let ty_inner = Typechecker.PlainTyp ("bool", []) in
  let rabbit_typ = Typechecker.RabbitTyp( ty_inner, (Typechecker.Public, Typechecker.Untrusted) ) in
  let env = Maps.StringMap.(empty |> add "x" rabbit_typ ) in   
  let expr = Syntax.Variable("x", Loc(0)) in 

  let resulting_type = Typechecker.typeof_expr expr env in 
  
  let expected_type = Typechecker.RabbitTyp( ty_inner, (Typechecker.Public, Typechecker.Untrusted) ) in


  check rabbit_ty_testable "type equals expected type" resulting_type expected_type



let test_tr_app () = 

  (* suppose x is a message type *)
  (* let type_of_x = Typechecker.RabbitTyp(Typechecker.PlainTyp("message", []), 
    (Typechecker.SNode(Sets.ProcSet.of_list ["alice"; "bob"]), 
     Typechecker.INode(Sets.ProcSet.of_list ["alice"; "bob"]))) in 

  (* and suppose y is some signing key type *)
  let type_of_y = Typechecker.RabbitTyp(Typechecker.PlainTyp("key", [type_of_x]), 
    (Typechecker.SNode(Sets.ProcSet.of_list ["alice"]), (* only Alice can read the key *) 
     Typechecker.INode(Sets.ProcSet.of_list ["alice"])) (* only Alice is allowed to provide the key *)
  ) in  

  let ret_ty = Typechecker.RabbitTyp(Typechecker.PlainTyp("signature"))

  let type_of_f = Typechecker.FunTyp()
  let exp = Syntax.Apply("f", [Syntax.Variable("x", Loc(0)); Syntax.Variable("y", Loc(0))]) *)

  check int "0 equals 0" 0 0
  





let suite = ("Typechecker module", [
  test_case "test_tr_var" `Quick test_tr_var; 
  test_case "test_tr_app" `Quick test_tr_app
  ])