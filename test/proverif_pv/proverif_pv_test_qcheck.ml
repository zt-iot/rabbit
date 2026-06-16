let () =
  QCheck_base_runner.run_tests_main [Proverif_p_test_qcheck.test] |> ignore
