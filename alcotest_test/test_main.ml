
let () =
  Alcotest.run "All tests"
    [
      To_cst_test.suite;
      Typechecker_test.suite;
    ]