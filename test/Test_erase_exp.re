open Alcotest;
open Hazelnut_lib.Hazelnut;
open Test_interfaces;

let test_eetop = () => {
  let ze: zexp = Cursor(Var("x"));
  let given: hexp = erase_exp(ze);
  let expected: hexp = Var("x");
  check(hexp_typ, "same hexp", given, expected);
};

let test_eeascl = () => {
  let ze: zexp = LAsc(Cursor(Lam("f", Lit(1))), Arrow(Num, Num));
  let given: hexp = erase_exp(ze);
  let expected: hexp = Asc(Lam("f", Lit(1)), Arrow(Num, Num));
  check(hexp_typ, "same hexp", given, expected);
};

let erase_exp_tests = [
  ("test_eetop", `Quick, test_eetop),
  ("test_etarrl", `Quick, test_eeascl),
];
