open Alcotest;
open Hazelnut_lib.Hazelnut;

let hexp_eq = (he1: hexp, he2: hexp): bool => compare_hexp(he1, he2) == 0;

let hexp_print = (_: hexp): string => "hexp";

let hexp_typ = testable(Fmt.using(hexp_print, Fmt.string), hexp_eq);
