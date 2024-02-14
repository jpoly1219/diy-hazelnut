open Alcotest;
open Hazelnut_lib.Hazelnut;
open Test_interfaces;

let test_eetop = () => {
  let ze: zexp = Cursor(Var("x"));
  let given = erase_exp(ze);
  let expected: hexp = Var("x");
  check(hexp_typ, "same hexp", given, expected);
};

let erase_exp_tests = [("test_eetop", `Quick, test_eetop)];
