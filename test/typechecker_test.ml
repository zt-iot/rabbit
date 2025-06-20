open Alcotest

open Rabbit_lib


let rabbit_ty_testable = Alcotest.testable Typechecker.pp_rabbit_ty Typechecker.equal_rabbit_ty

let test_typechecker () = 


  let ty_inner = Typechecker.PlainTyp ("bool", []) in
  let rabbit_typ = Typechecker.RabbitTyp( ty_inner, (Typechecker.Public, Typechecker.Untrusted) ) in
  let env = Maps.StringMap.(empty |> add "x" rabbit_typ ) in   
  let expr = Syntax.Variable("x", Loc(0)) in 

  let resulting_type = Typechecker.typeof_expr expr env in 
  
  let expected_type = Typechecker.RabbitTyp( ty_inner, (Typechecker.Public, Typechecker.Untrusted) ) in

  (* check int "0 equals 0" 0 0 *)
  check rabbit_ty_testable "type equals expected type" resulting_type expected_type




let suite = ("Typechecker module", [test_case "test_typechecker" `Quick test_typechecker])