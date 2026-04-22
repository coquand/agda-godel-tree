{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RouteADf -- Provable-layer Th 13 lift (Route A), mechanical
-- Fun1 + Fun2 cases whose axiom RHS is a single variable.
--
-- Transcribes Guard 1963 Theorem 13 at the Provable layer.  The key
-- conceptual correspondence:
--
--   Guard's  num : Fun1   <->   our  cor : Fun1  (Guard.CodeOfReify)
--
-- In Guard 1963 (Def 12, p.16), an underlined variable x inside a
-- Goedel-numbered term is interpreted as  num x  (a BRA  Fun1  in x),
-- NOT as the constant Goedel number of the variable symbol.  Th 13's
-- conclusion  "f_x = _y"  (x and y underlined) unfolds via Def 12 to
-- a BRA term in the variables x, y, not a closed Goedel number.
--
-- The proof of Th 13 combines Th 12 (which gives the self-case
-- "f_x = fx" encoded) with  num-congruence  (ax4Cong1 num) applied to
-- the hypothesis  f(x) = y : from  f(x) = y  derive  num(f(x)) = num y ,
-- then rewrite the RHS of Th 12's encoded equation from  num(f(x))
-- to  num y .
--
-- In our system,  axEqCong1 cor  fires unconditionally on any terms
-- (built-in Fun1 congruence — no special constructor needed).  Hence
-- for each Fun1/Fun2 whose defining axiom has the form  f(args) = rhs
-- with  rhs  a single variable, thm13At lifts cleanly by
--   (1) encAx* + fromDeriv    (Guard Th 12)
--   (2) prCong1 cor on hyp    (num-cong)
--   (3) prCong1 cor on the axiom + prSym/prTrans  (bridging cor(rhs))
--   (4) prCongR Pair rewrite  (rewrite cor rhs ~> cor y in outer Pair)
--   (5) prTrans gluing
--
-- This file covers all such "simple" cases:
--   Fun1 : I, Fst, Snd, KT, Refl
--   Fun2 : Const, IfLfL, IfLfN
--
-- Compound cases (Comp, Comp2, Lift, Post, Fan, RecNd, TreeEqNN,
-- Goodstein, RecPNd), where the axiom's RHS is a structured expression
-- (e.g. f(g(x)) for Comp), require Guard's meta-induction on functor
-- definition length and a bridging lemma between the structurally-
-- encoded RHS and  cor (compound) .  Deferred to a follow-up.
--
-- TreeEqLL/LN/NL have a closed constant RHS (O or poo) that bridges to
--  cor (closed-term)  via corOfReify; a small extension of the
-- simple pattern (one prTrans + corOfReify), also deferred.
--
-- Conventions: --safe --without-K --exact-split, no postulates, no
-- holes.  Use ~/.cabal/bin/agda-2.9.0 to typecheck.

module Guard.RouteADf where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical using (trivCT)
open import Guard.CodeOfReify using (cor)
open import Guard.ProofEnc
open import Guard.Formula
open import Guard.Provable
open import Guard.ProvableEqLifts

------------------------------------------------------------------------
-- Case f = I.  axI : ap1 I t = t.
------------------------------------------------------------------------

DfI : Term -> Term -> Term
DfI x _ = encAxI (ap1 cor x)

-- Encoded form of the Th 13 conclusion "I_x = _y".
encEqI : Term -> Term -> Term
encEqI x y =
  ap2 Pair
    (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) (ap1 cor x)))
    (ap1 cor y)

DfICorrSelf : (x : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfI x x)) (encEqI x x))
DfICorrSelf x = encAxICorr trivCT (ap1 cor x)

thm13AtI : {hyp : Formula} (x y : Term) ->
  Provable hyp (atomic (eqn (ap1 I x) y)) ->
  Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfI x y)) (encEqI x y)))
thm13AtI {hyp} x y dIxy =
  prTrans _ (encEqI x x) (encEqI x y) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) (ap1 cor x))
  self = fromDeriv (encAxICorr trivCT (ap1 cor x))
  corAx : Provable hyp (atomic (eqn (ap1 cor (ap1 I x)) (ap1 cor x)))
  corAx = prCong1 cor (ap1 I x) x (fromDeriv (axI x))
  corHyp : Provable hyp (atomic (eqn (ap1 cor (ap1 I x)) (ap1 cor y)))
  corHyp = prCong1 cor (ap1 I x) y dIxy
  corxy : Provable hyp (atomic (eqn (ap1 cor x) (ap1 cor y)))
  corxy = prTrans (ap1 cor x) (ap1 cor (ap1 I x)) (ap1 cor y)
            (prSym (ap1 cor (ap1 I x)) (ap1 cor x) corAx) corHyp
  rewr = prCongR Pair (ap1 cor x) (ap1 cor y) A corxy

------------------------------------------------------------------------
-- Case f = Fst.  axFst : ap1 Fst (ap2 Pair a b) = a.
------------------------------------------------------------------------

DfFst : Term -> Term -> Term -> Term
DfFst a b _ = encAxFst (ap1 cor a) (ap1 cor b)

encEqFst : Term -> Term -> Term -> Term
encEqFst a b y =
  ap2 Pair
    (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst))
      (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
        (ap2 Pair (ap1 cor a) (ap1 cor b))))))
    (ap1 cor y)

DfFstCorrSelf : (a b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfFst a b a)) (encEqFst a b a))
DfFstCorrSelf a b = encAxFstCorr trivCT (ap1 cor a) (ap1 cor b)

thm13AtFst : {hyp : Formula} (a b y : Term) ->
  Provable hyp (atomic (eqn (ap1 Fst (ap2 Pair a b)) y)) ->
  Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfFst a b y)) (encEqFst a b y)))
thm13AtFst {hyp} a b y dFst =
  prTrans _ (encEqFst a b a) (encEqFst a b y) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst))
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
          (ap2 Pair (ap1 cor a) (ap1 cor b)))))
  self = fromDeriv (encAxFstCorr trivCT (ap1 cor a) (ap1 cor b))
  lhs : Term
  lhs = ap1 Fst (ap2 Pair a b)
  corAx : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor a)))
  corAx = prCong1 cor lhs a (fromDeriv (axFst a b))
  corHyp : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor y)))
  corHyp = prCong1 cor lhs y dFst
  coray : Provable hyp (atomic (eqn (ap1 cor a) (ap1 cor y)))
  coray = prTrans (ap1 cor a) (ap1 cor lhs) (ap1 cor y)
            (prSym (ap1 cor lhs) (ap1 cor a) corAx) corHyp
  rewr = prCongR Pair (ap1 cor a) (ap1 cor y) A coray

------------------------------------------------------------------------
-- Case f = Snd.  axSnd : ap1 Snd (ap2 Pair a b) = b.
------------------------------------------------------------------------

DfSnd : Term -> Term -> Term -> Term
DfSnd a b _ = encAxSnd (ap1 cor a) (ap1 cor b)

encEqSnd : Term -> Term -> Term -> Term
encEqSnd a b y =
  ap2 Pair
    (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd))
      (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
        (ap2 Pair (ap1 cor a) (ap1 cor b))))))
    (ap1 cor y)

DfSndCorrSelf : (a b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfSnd a b b)) (encEqSnd a b b))
DfSndCorrSelf a b = encAxSndCorr trivCT (ap1 cor a) (ap1 cor b)

thm13AtSnd : {hyp : Formula} (a b y : Term) ->
  Provable hyp (atomic (eqn (ap1 Snd (ap2 Pair a b)) y)) ->
  Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfSnd a b y)) (encEqSnd a b y)))
thm13AtSnd {hyp} a b y dSnd =
  prTrans _ (encEqSnd a b b) (encEqSnd a b y) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd))
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
          (ap2 Pair (ap1 cor a) (ap1 cor b)))))
  self = fromDeriv (encAxSndCorr trivCT (ap1 cor a) (ap1 cor b))
  lhs : Term
  lhs = ap1 Snd (ap2 Pair a b)
  corAx : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor b)))
  corAx = prCong1 cor lhs b (fromDeriv (axSnd a b))
  corHyp : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor y)))
  corHyp = prCong1 cor lhs y dSnd
  corby : Provable hyp (atomic (eqn (ap1 cor b) (ap1 cor y)))
  corby = prTrans (ap1 cor b) (ap1 cor lhs) (ap1 cor y)
            (prSym (ap1 cor lhs) (ap1 cor b) corAx) corHyp
  rewr = prCongR Pair (ap1 cor b) (ap1 cor y) A corby

------------------------------------------------------------------------
-- Case f = KT t.  axKT : ap1 (KT t) x = t.
-- Here  t  is a parameter of the functor;  x  is the argument.  The
-- "self" case is y = t (regardless of x), since ap1 (KT t) x = t
-- unconditionally.
------------------------------------------------------------------------

DfKT : Term -> Term -> Term -> Term
DfKT t x _ = encAxKT (ap1 cor t) (ap1 cor x)

-- encAxKTCorr uses a private  codeKTTag  = reify (natCode f6)  where
-- f6 = 32.  We rebuild that locally, grouping sucs in fours for
-- legibility.
private
  n32 : Nat
  n32 =
    suc (suc (suc (suc      -- 4
    (suc (suc (suc (suc     -- 8
    (suc (suc (suc (suc     -- 12
    (suc (suc (suc (suc     -- 16
    (suc (suc (suc (suc     -- 20
    (suc (suc (suc (suc     -- 24
    (suc (suc (suc (suc     -- 28
    (suc (suc (suc (suc     -- 32
    zero)))))))))))))))))))))))))))))))

  codeKTTagT : Term
  codeKTTagT = reify (natCode n32)

encEqKT : Term -> Term -> Term -> Term
encEqKT t x y =
  ap2 Pair
    (ap2 Pair (reify tagAp1) (ap2 Pair (ap2 Pair codeKTTagT (ap1 cor t))
      (ap1 cor x)))
    (ap1 cor y)

DfKTCorrSelf : (t x : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfKT t x t)) (encEqKT t x t))
DfKTCorrSelf t x = encAxKTCorr trivCT (ap1 cor t) (ap1 cor x)

thm13AtKT : {hyp : Formula} (t x y : Term) ->
  Provable hyp (atomic (eqn (ap1 (KT t) x) y)) ->
  Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfKT t x y)) (encEqKT t x y)))
thm13AtKT {hyp} t x y dKT =
  prTrans _ (encEqKT t x t) (encEqKT t x y) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp1) (ap2 Pair (ap2 Pair codeKTTagT (ap1 cor t))
        (ap1 cor x))
  self = fromDeriv (encAxKTCorr trivCT (ap1 cor t) (ap1 cor x))
  lhs : Term
  lhs = ap1 (KT t) x
  corAx : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor t)))
  corAx = prCong1 cor lhs t (fromDeriv (axKT t x))
  corHyp : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor y)))
  corHyp = prCong1 cor lhs y dKT
  corty : Provable hyp (atomic (eqn (ap1 cor t) (ap1 cor y)))
  corty = prTrans (ap1 cor t) (ap1 cor lhs) (ap1 cor y)
            (prSym (ap1 cor lhs) (ap1 cor t) corAx) corHyp
  rewr = prCongR Pair (ap1 cor t) (ap1 cor y) A corty

------------------------------------------------------------------------
-- Case: axRefl : t = t.  Not a Fun1, but the same Th 13 pattern
-- applies to the reflexivity axiom: given any  t = y , encode the
-- self-case "t = t" via encAxRefl and rewrite  cor t ~> cor y .
------------------------------------------------------------------------

DfRefl : Term -> Term -> Term
DfRefl t _ = encAxRefl (ap1 cor t)

encEqRefl : Term -> Term -> Term
encEqRefl t y = ap2 Pair (ap1 cor t) (ap1 cor y)

DfReflCorrSelf : (t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfRefl t t)) (encEqRefl t t))
DfReflCorrSelf t = encAxReflCorr trivCT (ap1 cor t)

thm13AtRefl : {hyp : Formula} (t y : Term) ->
  Provable hyp (atomic (eqn t y)) ->
  Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfRefl t y)) (encEqRefl t y)))
thm13AtRefl {hyp} t y dty =
  prTrans _ (encEqRefl t t) (encEqRefl t y) self rewr
  where
  self = fromDeriv (encAxReflCorr trivCT (ap1 cor t))
  corty : Provable hyp (atomic (eqn (ap1 cor t) (ap1 cor y)))
  corty = prCong1 cor t y dty
  rewr = prCongR Pair (ap1 cor t) (ap1 cor y) (ap1 cor t) corty

------------------------------------------------------------------------
-- Fun2 simple cases
-- =================
-- Binary-functor analog  DfF2 g args y .  Same pattern as DfF1, using
-- the Fun2-specific encAx* encoders.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Case g = Const.  axConst : ap2 Const a b = a.
------------------------------------------------------------------------

DfConst : Term -> Term -> Term -> Term
DfConst a b _ = encAxConst (ap1 cor a) (ap1 cor b)

encEqConst : Term -> Term -> Term -> Term
encEqConst a b y =
  ap2 Pair
    (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Const))
      (ap2 Pair (ap1 cor a) (ap1 cor b))))
    (ap1 cor y)

DfConstCorrSelf : (a b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfConst a b a)) (encEqConst a b a))
DfConstCorrSelf a b = encAxConstCorr trivCT (ap1 cor a) (ap1 cor b)

thm13AtConst : {hyp : Formula} (a b y : Term) ->
  Provable hyp (atomic (eqn (ap2 Const a b) y)) ->
  Provable hyp (atomic
    (eqn (ap1 (thmT trivCT) (DfConst a b y)) (encEqConst a b y)))
thm13AtConst {hyp} a b y dConst =
  prTrans _ (encEqConst a b a) (encEqConst a b y) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Const))
        (ap2 Pair (ap1 cor a) (ap1 cor b)))
  self = fromDeriv (encAxConstCorr trivCT (ap1 cor a) (ap1 cor b))
  lhs : Term
  lhs = ap2 Const a b
  corAx : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor a)))
  corAx = prCong1 cor lhs a (fromDeriv (axConst a b))
  corHyp : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor y)))
  corHyp = prCong1 cor lhs y dConst
  coray : Provable hyp (atomic (eqn (ap1 cor a) (ap1 cor y)))
  coray = prTrans (ap1 cor a) (ap1 cor lhs) (ap1 cor y)
            (prSym (ap1 cor lhs) (ap1 cor a) corAx) corHyp
  rewr = prCongR Pair (ap1 cor a) (ap1 cor y) A coray

------------------------------------------------------------------------
-- Case g = IfLf, left branch.  axIfLfL : IfLf O (Pair a b) = a.
------------------------------------------------------------------------

DfIfLfL : Term -> Term -> Term -> Term
DfIfLfL a b _ = encAxIfLfL (ap1 cor a) (ap1 cor b)

encEqIfLfL : Term -> Term -> Term -> Term
encEqIfLfL a b y =
  ap2 Pair
    (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 IfLf))
      (ap2 Pair (ap2 Pair O O)
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
          (ap2 Pair (ap1 cor a) (ap1 cor b)))))))
    (ap1 cor y)

DfIfLfLCorrSelf : (a b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfIfLfL a b a)) (encEqIfLfL a b a))
DfIfLfLCorrSelf a b = encAxIfLfLCorr trivCT (ap1 cor a) (ap1 cor b)

thm13AtIfLfL : {hyp : Formula} (a b y : Term) ->
  Provable hyp (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) y)) ->
  Provable hyp (atomic
    (eqn (ap1 (thmT trivCT) (DfIfLfL a b y)) (encEqIfLfL a b y)))
thm13AtIfLfL {hyp} a b y dIf =
  prTrans _ (encEqIfLfL a b a) (encEqIfLfL a b y) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 IfLf))
        (ap2 Pair (ap2 Pair O O)
          (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
            (ap2 Pair (ap1 cor a) (ap1 cor b))))))
  self = fromDeriv (encAxIfLfLCorr trivCT (ap1 cor a) (ap1 cor b))
  lhs : Term
  lhs = ap2 IfLf O (ap2 Pair a b)
  corAx : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor a)))
  corAx = prCong1 cor lhs a (fromDeriv (axIfLfL a b))
  corHyp : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor y)))
  corHyp = prCong1 cor lhs y dIf
  coray : Provable hyp (atomic (eqn (ap1 cor a) (ap1 cor y)))
  coray = prTrans (ap1 cor a) (ap1 cor lhs) (ap1 cor y)
            (prSym (ap1 cor lhs) (ap1 cor a) corAx) corHyp
  rewr = prCongR Pair (ap1 cor a) (ap1 cor y) A coray

------------------------------------------------------------------------
-- Case g = IfLf, nd branch.  axIfLfN : IfLf (Pair x y) (Pair a b) = b.
------------------------------------------------------------------------

DfIfLfN : Term -> Term -> Term -> Term -> Term -> Term
DfIfLfN x y a b _ =
  encAxIfLfN (ap1 cor x) (ap1 cor y) (ap1 cor a) (ap1 cor b)

encEqIfLfN : Term -> Term -> Term -> Term -> Term -> Term
encEqIfLfN x y a b z =
  ap2 Pair
    (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 IfLf))
      (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
          (ap2 Pair (ap1 cor x) (ap1 cor y))))
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
          (ap2 Pair (ap1 cor a) (ap1 cor b)))))))
    (ap1 cor z)

DfIfLfNCorrSelf : (x y a b : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfIfLfN x y a b b)) (encEqIfLfN x y a b b))
DfIfLfNCorrSelf x y a b =
  encAxIfLfNCorr trivCT (ap1 cor x) (ap1 cor y) (ap1 cor a) (ap1 cor b)

thm13AtIfLfN : {hyp : Formula} (x y a b z : Term) ->
  Provable hyp (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) z)) ->
  Provable hyp (atomic
    (eqn (ap1 (thmT trivCT) (DfIfLfN x y a b z)) (encEqIfLfN x y a b z)))
thm13AtIfLfN {hyp} x y a b z dIf =
  prTrans _ (encEqIfLfN x y a b b) (encEqIfLfN x y a b z) self rewr
  where
  A : Term
  A = ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 IfLf))
        (ap2 Pair
          (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
            (ap2 Pair (ap1 cor x) (ap1 cor y))))
          (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair))
            (ap2 Pair (ap1 cor a) (ap1 cor b))))))
  self = fromDeriv (encAxIfLfNCorr trivCT (ap1 cor x) (ap1 cor y)
                                          (ap1 cor a) (ap1 cor b))
  lhs : Term
  lhs = ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)
  corAx : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor b)))
  corAx = prCong1 cor lhs b (fromDeriv (axIfLfN x y a b))
  corHyp : Provable hyp (atomic (eqn (ap1 cor lhs) (ap1 cor z)))
  corHyp = prCong1 cor lhs z dIf
  corbz : Provable hyp (atomic (eqn (ap1 cor b) (ap1 cor z)))
  corbz = prTrans (ap1 cor b) (ap1 cor lhs) (ap1 cor z)
            (prSym (ap1 cor lhs) (ap1 cor b) corAx) corHyp
  rewr = prCongR Pair (ap1 cor b) (ap1 cor z) A corbz

------------------------------------------------------------------------
-- Implications / what remains
-- =====================================================================
--
-- The 8 cases above (I, Fst, Snd, KT, Refl, Const, IfLfL, IfLfN) cover
-- every Fun1 + Fun2 whose axiom  f(args) = rhs  has  rhs  a single
-- variable from the argument list.  Each followed the 5-step schema
-- above mechanically; the only variation is the spelling of the
-- encoded-LHS  A .
--
-- Remaining cases (deferred):
--
--  * TreeEqLL / TreeEqLN / TreeEqNL : rhs is a closed constant ( O  or
--     poo  or  poo ).  The rewrite step requires one bridging prTrans
--    using  corOfReify : ap1 cor (reify t) = reify (code (reify t))
--    applied to the closed reified-tree rhs, then the usual  cor  cong
--    + rewrite.  ~30 lines per case.
--
--  * TreeEqNN, Goodstein : rhs is a compound expression (IfLf(...)).
--    Requires unfolding the compound-structure encoding to  cor  of
--    the value.  Needs meta-induction on the structure.
--
--  * Comp f g, Comp2 h f g, Lift f, Post f h, Fan h1 h2 h,
--    RecNd z s, RecPNd s p : compound Fun1/Fun2 whose axiom RHS is a
--    compound functor application (e.g.  Comp f g (x) = f(g(x)) ).
--    The encoded RHS is structurally encoded (tagAp1 nestings), not
--    directly  cor (f(g(x))) .  Bridging requires Guard's meta-induction
--    on functor definition length + structural encoding lemmas.
--
--  * RecLf, RecPLf : rhs is the base-case element ( z  resp.  O ).
--    Similar to KT but with the closed-constant bridging issue.
--
-- Committing the simple cases as a first batch: 8 cases, ~320 lines
-- including this commentary, structured uniformly.  All typecheck under
-- --safe --without-K --exact-split with no postulates, no holes (one
-- pre-existing CoverageNoExactSplit warning on deductionThm carried
-- through from ProvableLemmas).
