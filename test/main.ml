

let () =
  Alcotest.run "All tests"
    [
      Sample_test.suite;
      Parser_test.suite;
    ]