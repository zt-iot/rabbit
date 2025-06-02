

let () =
  Alcotest.run "All tests"
    [
      Sample_test.suite;
    ]