

let () =
  Alcotest.run "All tests"
    [
      Sample_test.suite;
      Typechecker_test.suite;
    ]