open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

// helper
let rec erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(ht1) => ht1
  | LArrow(zt1, ht1) => Arrow(erase_typ(zt1), ht1)
  | RArrow(ht1, zt1) => Arrow(ht1, erase_typ(zt1))
  };
};

let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(he1) => he1
  | Lam(str, ze1) => Lam(str, erase_exp(ze1))
  | LAp(ze1, he1) => Ap(erase_exp(ze1), he1)
  | RAp(he1, ze1) => Ap(he1, erase_exp(ze1))
  | LPlus(ze1, he1) => Plus(erase_exp(ze1), he1)
  | RPlus(he1, ze1) => Plus(he1, erase_exp(ze1))
  | LAsc(ze1, ht1) => Asc(erase_exp(ze1), ht1)
  | RAsc(he1, zt1) => Asc(he1, erase_typ(zt1))
  | NEHole(ze1) => NEHole(erase_exp(ze1))
  };
};

// helper
let rec consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1) {
  | Arrow(t1Typ1, t1Typ2) =>
    switch (t2) {
    | Arrow(t2Typ1, t2Typ2) =>
      consistent(t1Typ1, t2Typ1) && consistent(t1Typ2, t2Typ2)
    | Hole => true
    | _ => false
    }
  | Num =>
    switch (t2) {
    | Num => true
    | Hole => true
    | _ => false
    }
  | Hole => true
  };
};

// helper
let matchedArrow = (t: Htyp.t): option(Htyp.t) => {
  switch (t) {
  | Arrow(ht1, ht2) => Some(Arrow(ht1, ht2))
  | Hole => Some(Arrow(Hole, Hole))
  | _ => None
  };
};

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(str) =>
    if (TypCtx.mem(str, ctx)) {
      Some(TypCtx.find(str, ctx));
    } else {
      None;
    }
  | Ap(e1, e2) =>
    let t1 = syn(ctx, e1);
    switch (t1) {
    | Some(typ) =>
      let t1Matched = matchedArrow(typ);
      switch (t1Matched) {
      | Some(Arrow(t2, t)) =>
        if (ana(ctx, e2, t2)) {
          Some(t);
        } else {
          None;
        }
      | _ => None
      };
    | _ => None
    };
  | Lit(_) => Some(Num)
  | Plus(e1, e2) =>
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    }
  | EHole => Some(Hole)
  | NEHole(e1) =>
    if (syn(ctx, e1) != None) {
      Some(Hole);
    } else {
      None;
    }
  | Asc(e1, t) =>
    if (ana(ctx, e1, t)) {
      Some(t);
    } else {
      None;
    }
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Lam(str, e1) =>
    let tMatched = matchedArrow(t);
    switch (tMatched) {
    | Some(Arrow(t1, t2)) =>
      let newCtx = TypCtx.add(str, t1, ctx);
      ana(newCtx, e1, t2);
    | _ => false
    };
  | _ =>
    let t1 = syn(ctx, e);
    switch (t1) {
    | Some(typ) => consistent(t, typ)
    | _ => false
    };
  };
};

// helper for type actions
let rec type_action = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  let type_action_zipper = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
    switch (t) {
    | LArrow(zt1, ht1) =>
      let after = type_action(zt1, a);
      switch (after) {
      | Some(typ) => Some(LArrow(typ, ht1))
      | _ => None
      };
    | RArrow(ht1, zt1) =>
      let after = type_action(zt1, a);
      switch (after) {
      | Some(typ) => Some(RArrow(ht1, typ))
      | _ => None
      };
    | _ => None
    };
  };

  switch (a) {
  | Move(d) =>
    switch (t) {
    | Cursor(Arrow(t1, t2)) =>
      switch (d) {
      | Child(One) => Some(LArrow(Cursor(t1), t2))
      | Child(Two) => Some(RArrow(t1, Cursor(t2)))
      | _ => type_action_zipper(t, a)
      }
    | LArrow(Cursor(t1), t2) =>
      switch (d) {
      | Parent => Some(Cursor(Arrow(t1, t2)))
      | _ => type_action_zipper(t, a)
      }
    | RArrow(t1, Cursor(t2)) =>
      switch (d) {
      | Parent => Some(Cursor(Arrow(t1, t2)))
      | _ => type_action_zipper(t, a)
      }
    | _ => type_action_zipper(t, a)
    }
  | Del =>
    switch (t) {
    | Cursor(_) => Some(Cursor(Hole))
    | _ => type_action_zipper(t, a)
    }
  | Construct(Arrow) =>
    switch (t) {
    | Cursor(zt1) => Some(RArrow(zt1, Cursor(Hole)))
    | _ => type_action_zipper(t, a)
    }
  | Construct(Num) =>
    switch (t) {
    | Cursor(Hole) => Some(Cursor(Num))
    | _ => type_action_zipper(t, a)
    }
  | _ => type_action_zipper(t, a)
  };
};

// helper for expression actions
let exp_action = (e: Zexp.t, a: Action.t): option(Zexp.t) => {
  switch (a) {
  | Move(d) =>
    switch (e) {
    | Cursor(Asc(he1, ht1)) =>
      switch (d) {
      | Child(One) => Some(LAsc(Cursor(he1), ht1))
      | Child(Two) => Some(RAsc(he1, Cursor(ht1)))
      | _ => None
      }
    | LAsc(Cursor(he1), ht1) =>
      switch (d) {
      | Parent => Some(Cursor(Asc(he1, ht1)))
      | _ => None
      }
    | RAsc(he1, Cursor(ht1)) =>
      switch (d) {
      | Parent => Some(Cursor(Asc(he1, ht1)))
      | _ => None
      }
    | Cursor(Lam(str, he1)) =>
      switch (d) {
      | Child(One) => Some(Lam(str, Cursor(he1)))
      | _ => None
      }
    | Lam(str, Cursor(he1)) =>
      switch (d) {
      | Parent => Some(Cursor(Lam(str, he1)))
      | _ => None
      }
    | Cursor(Plus(he1, he2)) =>
      switch (d) {
      | Child(One) => Some(LPlus(Cursor(he1), he2))
      | Child(Two) => Some(RPlus(he1, Cursor(he2)))
      | _ => None
      }
    | LPlus(Cursor(he1), he2) =>
      switch (d) {
      | Parent => Some(Cursor(Plus(he1, he2)))
      | _ => None
      }
    | RPlus(he1, Cursor(he2)) =>
      switch (d) {
      | Parent => Some(Cursor(Plus(he1, he2)))
      | _ => None
      }
    | Cursor(Ap(he1, he2)) =>
      switch (d) {
      | Child(One) => Some(LAp(Cursor(he1), he2))
      | Child(Two) => Some(RAp(he1, Cursor(he2)))
      | _ => None
      }
    | LAp(Cursor(he1), he2) =>
      switch (d) {
      | Parent => Some(Cursor(Ap(he1, he2)))
      | _ => None
      }
    | RAp(he1, Cursor(he2)) =>
      switch (d) {
      | Parent => Some(Cursor(Ap(he1, he2)))
      | _ => None
      }
    | Cursor(NEHole(he1)) =>
      switch (d) {
      | Child(One) => Some(NEHole(Cursor(he1)))
      | _ => None
      }
    | NEHole(Cursor(he1)) =>
      switch (d) {
      | Parent => Some(Cursor(NEHole(he1)))
      | _ => None
      }
    | _ => None
    }
  | _ => None
  };
};

let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  let syn_action_zipper =
      (ctx: typctx, (e: Zexp.t, _: Htyp.t), a: Action.t)
      : option((Zexp.t, Htyp.t)) => {
    switch (e) {
    | LAsc(ze1, ht1) =>
      let ze2 = ana_action(ctx, ze1, a, ht1);
      switch (ze2) {
      | Some(ze) => Some((LAsc(ze, ht1), ht1))
      | _ => None
      };
    | RAsc(he1, zt1) =>
      let zt2 = type_action(zt1, a);
      switch (zt2) {
      | Some(zt) =>
        if (ana(ctx, he1, erase_typ(zt))) {
          Some((RAsc(he1, zt), erase_typ(zt)));
        } else {
          None;
        }
      | _ => None
      };
    | LAp(ze1, he1) =>
      let tSynthesized = syn(ctx, erase_exp(ze1));
      switch (tSynthesized) {
      | Some(ht2) =>
        let somePair = syn_action(ctx, (ze1, ht2), a);
        switch (somePair) {
        | Some((ze2, ht3)) =>
          let tMatched = matchedArrow(ht3);
          switch (tMatched) {
          | Some(Arrow(ht4, ht5)) =>
            if (ana(ctx, he1, ht4)) {
              Some((LAp(ze2, he1), ht5));
            } else {
              None;
            }
          | _ => None
          };
        | _ => None
        };
      | _ => None
      };
    | RAp(he1, ze1) =>
      let tSynthesized = syn(ctx, he1);
      switch (tSynthesized) {
      | Some(ht2) =>
        let tMatched = matchedArrow(ht2);
        switch (tMatched) {
        | Some(Arrow(ht3, ht4)) =>
          let analyzed = ana_action(ctx, ze1, a, ht3);
          switch (analyzed) {
          | Some(ze) => Some((RAp(he1, ze), ht4))
          | _ => None
          };
        | _ => None
        };
      | _ => None
      };
    | LPlus(ze1, he1) =>
      let analyzed = ana_action(ctx, ze1, a, Num);
      switch (analyzed) {
      | Some(ze) => Some((LPlus(ze, he1), Num))
      | _ => None
      };
    | RPlus(he1, ze1) =>
      let analyzed = ana_action(ctx, ze1, a, Num);
      switch (analyzed) {
      | Some(ze) => Some((RPlus(he1, ze), Num))
      | _ => None
      };
    | NEHole(ze1) =>
      let tSynthesized = syn(ctx, erase_exp(ze1));
      switch (tSynthesized) {
      | Some(ht) =>
        let eSynthesized = syn_action(ctx, (ze1, ht), a);
        switch (eSynthesized) {
        | Some((ze2, _)) => Some((NEHole(ze2), Hole))
        | _ => None
        };
      | _ => None
      };
    | _ => None
    };
  };

  switch (a) {
  | Move(_) =>
    let ze2 = exp_action(e, a);
    switch (ze2) {
    | Some(z) => Some((z, t))
    | _ => syn_action_zipper(ctx, (e, t), a)
    };
  | Del =>
    switch (e) {
    | Cursor(_) => Some((Cursor(EHole), Hole))
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(Asc) =>
    switch (e) {
    | Cursor(he1) => Some((RAsc(he1, Cursor(t)), t))
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(Var(str)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (TypCtx.mem(str, ctx)) {
        Some((Cursor(Var(str)), TypCtx.find(str, ctx)));
      } else {
        syn_action_zipper(ctx, (e, t), a);
      }
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(Lam(str)) =>
    switch (e) {
    | Cursor(EHole) =>
      Some((
        RAsc(Lam(str, EHole), LArrow(Cursor(Hole), Hole)),
        Arrow(Hole, Hole),
      ))
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(Ap) =>
    switch (e) {
    | Cursor(he1) =>
      let tMatched = matchedArrow(t);
      switch (tMatched) {
      | Some(Arrow(_, t2)) => Some((RAp(he1, Cursor(EHole)), t2))
      | _ => Some((RAp(NEHole(he1), Cursor(EHole)), Hole))
      };
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(Lit(n)) =>
    switch (e) {
    | Cursor(EHole) => Some((Cursor(Lit(n)), Num))
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(Plus) =>
    switch (e) {
    | Cursor(he1) =>
      if (consistent(t, Num)) {
        Some((RPlus(he1, Cursor(EHole)), Num));
      } else {
        Some((RPlus(NEHole(he1), Cursor(EHole)), Num));
      }
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Construct(NEHole) =>
    switch (e) {
    | Cursor(he1) => Some((NEHole(Cursor(he1)), Hole))
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | Finish =>
    switch (e) {
    | Cursor(NEHole(he1)) =>
      let tSynthesized = syn(ctx, he1);
      switch (tSynthesized) {
      | Some(typ) => Some((Cursor(he1), typ))
      | _ => syn_action_zipper(ctx, (e, t), a)
      };
    | _ => syn_action_zipper(ctx, (e, t), a)
    }
  | _ => syn_action_zipper(ctx, (e, t), a)
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  let ana_action_subsumption =
      (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
    let ht1 = syn(ctx, erase_exp(e));
    switch (ht1) {
    | Some(ht) =>
      let somePair = syn_action(ctx, (e, ht), a);
      switch (somePair) {
      | Some((ze, ht2)) =>
        if (consistent(t, ht2)) {
          Some(ze);
        } else {
          None;
        }
      | _ => None
      };
    | _ => None
    };
  };

  let ana_action_zipper =
      (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
    switch (e) {
    | Lam(str, ze1) =>
      let tMatched = matchedArrow(t);
      switch (tMatched) {
      | Some(Arrow(ht1, ht2)) =>
        let extendedCtx = TypCtx.add(str, ht1, ctx);
        let analyzed = ana_action(extendedCtx, ze1, a, ht2);
        switch (analyzed) {
        | Some(ze2) => Some(Lam(str, ze2))
        | _ => ana_action_subsumption(extendedCtx, e, a, t)
        };
      | _ => ana_action_subsumption(ctx, e, a, t)
      };
    | _ => ana_action_subsumption(ctx, e, a, t) // try subsumption
    };
  };

  switch (a) {
  | Move(_) =>
    let ze2 = exp_action(e, a);
    switch (ze2) {
    | Some(ze) => Some(ze)
    | _ => ana_action_zipper(ctx, e, a, t)
    };
  | Del =>
    switch (e) {
    | Cursor(_) => Some(Cursor(EHole))
    | _ => ana_action_zipper(ctx, e, a, t)
    }
  | Construct(Asc) =>
    switch (e) {
    | Cursor(he1) => Some(RAsc(he1, Cursor(t)))
    | _ => ana_action_zipper(ctx, e, a, t)
    }
  | Construct(Var(str)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (TypCtx.mem(str, ctx) && !consistent(t, TypCtx.find(str, ctx))) {
        Some(NEHole(Cursor(Var(str))));
      } else {
        ana_action_zipper(ctx, e, a, t);
      }
    | _ => ana_action_zipper(ctx, e, a, t)
    }
  | Construct(Lam(str)) =>
    switch (e) {
    | Cursor(EHole) =>
      let tMatched = matchedArrow(t);
      switch (tMatched) {
      | Some(Arrow(_, _)) => Some(Lam(str, Cursor(EHole)))
      | _ =>
        Some(NEHole(RAsc(Lam(str, EHole), LArrow(Cursor(Hole), Hole))))
      };
    | _ => ana_action_zipper(ctx, e, a, t)
    }
  | Construct(Lit(n)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (!consistent(t, Num)) {
        Some(NEHole(Cursor(Lit(n))));
      } else {
        ana_action_zipper(ctx, e, a, t);
      }
    | _ => ana_action_zipper(ctx, e, a, t)
    }
  | Finish =>
    switch (e) {
    | Cursor(NEHole(he1)) =>
      if (ana(ctx, he1, t)) {
        Some(Cursor(he1));
      } else {
        ana_action_zipper(ctx, e, a, t);
      }
    | _ => ana_action_zipper(ctx, e, a, t)
    }
  | _ => ana_action_zipper(ctx, e, a, t)
  };
};
