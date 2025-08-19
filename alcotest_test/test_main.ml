
let () =
  Alcotest.run "All tests"
    [
      Typechecker_test.suite;
    ]