open Alcotest;
open Test_interface;
module Hazelnut = Hazelnut_lib.Hazelnut;

module TypCtx = Map.Make(String);
type typctx = Hazelnut.TypCtx.t(Hazelnut.Htyp.t);

// let syn_action =
//     (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
//     : option((Zexp.t, Htyp.t)) => {

let test_sadel = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lit(1));
  let t: Hazelnut.Htyp.t = Num;
  let a: Hazelnut.Action.t = Del; 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((Cursor(EHole), Hole));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_safin = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(NEHole(Lit(1)));
  let t: Hazelnut.Htyp.t = Hole;
  let a: Hazelnut.Action.t = Finish; 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((Cursor(Lit(1)), Num));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

// Construct rules

let test_sacasc = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lit(1));
  let t: Hazelnut.Htyp.t = Num;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Asc); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((RAsc(Lit(1), Cursor(Num)), Num));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_sacvar = () => {
  let ctx: typctx = TypCtx.singleton("x", Hazelnut.Htyp.Num);
  let ze: Hazelnut.Zexp.t = Cursor(EHole);
  let t: Hazelnut.Htyp.t = Hole;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Var("x")); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((Cursor(Var("x")), Num));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_saclam = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(EHole);
  let t: Hazelnut.Htyp.t = Hole;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Lam("x")); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((RAsc(Lam("x",EHole), LArrow(Cursor(Hole),Hole)), Arrow(Hole,Hole)));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_saclit = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(EHole);
  let t: Hazelnut.Htyp.t = Hole;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Lit(1)); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((Cursor(Lit(1)), Num));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_sacneh = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lit(1));
  let t: Hazelnut.Htyp.t = Num;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.NEHole); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((NEHole(Cursor(Lit(1))), Hole));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_sacap1 = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lam("x",EHole));
  let t: Hazelnut.Htyp.t = Arrow(Hole,Hole);
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Ap); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((RAp(Lam("x",EHole), Cursor(EHole)), Hole));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_sacap2 = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lit(1));
  let t: Hazelnut.Htyp.t = Num;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Ap); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((RAp(NEHole(Lit(1)), Cursor(EHole)), Hole));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_sacplus1 = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lit(1));
  let t: Hazelnut.Htyp.t = Num;
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Plus); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((RPlus(Lit(1), Cursor(EHole)), Num));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let test_sacplus2 = () => {
  let ctx: typctx = TypCtx.empty;
  let ze: Hazelnut.Zexp.t = Cursor(Lam("x",EHole));
  let t: Hazelnut.Htyp.t = Arrow(Hole,Hole);
  let a: Hazelnut.Action.t = Construct(Hazelnut.Shape.Plus); 
  let given: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) = Hazelnut.syn_action(ctx, (ze, t), a);
  let expected: option((Hazelnut.Zexp.t,Hazelnut.Htyp.t)) =
    Some((RPlus(NEHole(Lam("x",EHole)), Cursor(EHole)), Num));
  check(zexp_htyp, "same option(Hazelnut.Zexp.t)", given, expected);
};

let syn_action_tests = [
  ("test_sadel", `Quick, test_sadel),
  ("test_safin", `Quick, test_safin),
  ("test_sacasc", `Quick, test_sacasc),
  ("test_sacvar", `Quick, test_sacvar),
  ("test_saclam", `Quick, test_saclam),
  ("test_saclit", `Quick, test_saclit),
  ("test_sacneh", `Quick, test_sacneh),
  ("test_sacap1", `Quick, test_sacap1),
  ("test_sacap2", `Quick, test_sacap2),
  ("test_sacplus2", `Quick, test_sacplus2),
];
