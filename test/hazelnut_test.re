open Alcotest;

let () =
  run("Hazelnut_tests", [("erase_exp", Test_erase_exp.erase_exp_tests)]);
