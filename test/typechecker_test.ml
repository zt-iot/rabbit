open Alcotest

open Rabbit_lib


let rabbit_ty_testable = Alcotest.testable Typechecker.pp_rabbit_ty Typechecker.equal_rabbit_ty

let test_tr_var () = 

  let ty_inner = Typechecker.PlainTyp ("bool", []) in
  let rabbit_typ = Typechecker.RabbitTyp( ty_inner, (Typechecker.Public, Typechecker.Untrusted) ) in

  let env = Maps.StringMap.(empty |> add "x" (Typechecker.ValueRabbitTyp rabbit_typ )) in   


  let expr = Syntax.Variable("x", Loc(0)) in 

  let resulting_type = Typechecker.typeof_expr expr env in 
  
  let expected_type = Typechecker.RabbitTyp( ty_inner, (Typechecker.Public, Typechecker.Untrusted) ) in


  check rabbit_ty_testable "type equals expected type" resulting_type expected_type



let test_tr_app () = 
  
  (* suppose x is a message type *)
  let type_of_x = Typechecker.RabbitTyp(Typechecker.PlainTyp("message", []), 
    (Typechecker.SNode(Sets.ProcSet.of_list ["alice"; "bob"]), 
     Typechecker.INode(Sets.ProcSet.of_list ["alice"; "bob"]))) in 

  (* and suppose y is some signing key type for messages of type `type_of_x *)
  let type_of_y = Typechecker.RabbitTyp(Typechecker.PlainTyp("sigkey", [type_of_x]), 
    (Typechecker.SNode(Sets.ProcSet.of_list ["alice"]), (* only Alice can read the key *) 
     Typechecker.INode(Sets.ProcSet.of_list ["alice"])) (* only Alice is allowed to provide the key *)
  ) in  

  (* and suppose ret_ty is the type that function `sign` returns *)
  let ret_ty = Typechecker.RabbitTyp(Typechecker.PlainTyp("signature", []), 
    (Typechecker.SNode(Sets.ProcSet.of_list ["alice"; "bob"]), 
     Typechecker.INode(Sets.ProcSet.of_list ["alice"]))) in

  (* we can then make a function signature type_of_x -> type_of_y -> ret_ty *)
  let function_sig = Typechecker.FunTyp([type_of_x; type_of_y; ret_ty]) in 

  let env = Maps.StringMap.(empty |> add "x" (Typechecker.ValueRabbitTyp type_of_x) |> add "y" (Typechecker.ValueRabbitTyp type_of_y) |> add "sign" (Typechecker.ValueFunTyp function_sig)) in
  let exp = Syntax.Apply("sign", [Syntax.Variable("x", Loc(0)); Syntax.Variable("y", Loc(0))]) in

  let expected_type = ret_ty in
  let actual_type = Typechecker.typeof_expr exp env in 


  check rabbit_ty_testable "function application" actual_type expected_type
  





let suite = ("Typechecker module", [
  test_case "test_tr_var" `Quick test_tr_var; 
  test_case "test_tr_app" `Quick test_tr_app
  ])