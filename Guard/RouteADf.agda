{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RouteADf -- Provable-layer Th 13 lift, case f = I (de-risk).
--
-- Transcribes Guard 1963 Theorem 13 at the Provable layer for the
-- singulary functor f = I.  The key conceptual correspondence:
--
--   Guard's  num : Fun1   <->   our  cor : Fun1  (Guard.CodeOfReify)
--
-- In Guard 1963 (Def 12, p.16), an underlined variable x inside a
-- Goedel-numbered term is interpreted as  num x , NOT as the constant
-- Goedel number of the variable symbol.  Th 13's conclusion  "f_x = y"
-- (with both x and y underlined) unfolds via Def 12 to
--
--   3J(3J("f", num x)+1, num y)
--
-- a BRA term in the variables x, y — not a closed Goedel number.
-- The proof of Th 13 combines Th 12 ( th(Df(x)) = "f_x = fx" ) with
--  num-congruence  ax4Cong1 num  applied to the hypothesis  f(x) = y ,
-- which yields  num(f(x)) = num y , and the RHS of Th 12 rewrites
-- from  num(f(x))  to  num y .
--
-- In our tree setting, the analog of  num  is  cor  (Guard.CodeOfReify):
-- a BRA  Fun1  defined by Rec on tree structure whose specification
--  corOfReify : ap1 cor (reify t) = reify (code (reify t))
-- is the analog of Guard's  num(sx) = "sx"  numeral identity.  And
--  axEqCong1 cor  fires unconditionally (built-in Fun1 congruence).
--
-- So the target RHS of  thm13AtI  uses  ap1 cor x  and  ap1 cor y  in
-- the slots that Guard writes as  num x  and  num y .  For any actual
-- substitution  x := reify t_x ,  y := reify t_y  (which is what the
-- chain supplies at closure time),  ap1 cor (reify t)  resolves to
--  reify (code (reify t))  via  corOfReify , reducing to the closed
-- Goedel-number-of-encoded-equation term that the reductio needs.
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
open import Guard.ProofEnc using (encAxI ; encAxICorr)
open import Guard.Formula
open import Guard.Provable
open import Guard.ProvableEqLifts

------------------------------------------------------------------------
-- DfI : Term -> Term -> Term
--
-- DfI x y = encAxI (ap1 cor x) .  y is not used at the Term level;
-- its role is played by the Provable-layer hypothesis  ap1 I x = y
-- (consumed by thm13AtI below).  The same pattern as Guard 1963's
-- Df(x): a singulary BRA functor whose argument is only  x .

DfI : Term -> Term -> Term
DfI x _ = encAxI (ap1 cor x)

------------------------------------------------------------------------
-- encEqForm x y : the encoded "f_x = _y" equation, with Guard's
-- underlining  num = cor  in place.
--
-- Shape: ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I))
-- (ap1 cor x))) (ap1 cor y) .  The first Pair slot is  "f_x"  (with x
-- underlined via cor); the second is  "_y"  (with y underlined via
-- cor).  Compare Guard 1963 Def 12's example:
--  "fx = g(hx,0)" ~~> 3J(3J("f", num x)+1, num g(hx,0))  .

encEqForm : Term -> Term -> Term
encEqForm x y =
  ap2 Pair
    (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) (ap1 cor x)))
    (ap1 cor y)

------------------------------------------------------------------------
-- DfICorrSelf : unconditional Deriv witness at the self-case (y = x).
--
-- This is Guard's Th 12 specialized to  f = I :  th(Df(x)) = "f_x = fx" .
-- Under the Def 12 equivalence  "fx" = num(fx)  (applicable since fx
-- is a term that can be regarded either as the Goedel number of the
-- syntactic term  f(x)  or as  num(fx)  with the whole expression
-- underlined), the self-case gives
--   thmT trivCT (DfI x x) = encEqForm x x  .
--
-- One-liner via encAxICorr.

DfICorrSelf : (x : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT trivCT) (DfI x x)) (encEqForm x x))
DfICorrSelf x = encAxICorr trivCT (ap1 cor x)

------------------------------------------------------------------------
-- thm13AtI : Guard 1963 Theorem 13, case f = I, at the Provable layer.
--
-- Direct transcription of the proof on guard15.pdf p.16:
--
--   f(x) = y  |-  th(Df(x))
--            = 3J(3J("f", num x)+1, num(f(x)))     by Th 12
--            = 3J(3J("f", num x)+1, num y         )  by ax4Cong1 num
--            = "f_x = _y"                          by Def 12
--
-- Our transcription at f = I, in the order Guard uses:
--
--  Step 1 : encAxICorr produces  thmT trivCT (DfI x y) = encEqForm x x
--           -- "th(Df(x)) = 'f_x = fx'"  under the Def 12 equivalence
--           -- (Guard's Th 12 specialized at f = I).
--  Step 2 : From the hypothesis  ap1 I x = y ,  prCong1 cor  gives
--             ap1 cor (ap1 I x) = ap1 cor y
--           -- "num(f(x)) = num y"  (the axCong1 num move).
--  Step 3 : From  axI  (ap1 I x = x),  prCong1 cor  gives
--             ap1 cor (ap1 I x) = ap1 cor x
--           -- a pure consequence of cor's congruence; composing with
--           -- step 2 via  prSym + prTrans  yields
--             ap1 cor x = ap1 cor y .
--  Step 4 : prCongR Pair rewrites  ap1 cor x  to  ap1 cor y  in the
--           second slot of the outer  ap2 Pair , moving
--             encEqForm x x  ~>  encEqForm x y .
--  Step 5 : prTrans glues steps 1 and 4.

thm13AtI : {hyp : Formula} (x y : Term) ->
  Provable hyp (atomic (eqn (ap1 I x) y)) ->
  Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfI x y)) (encEqForm x y)))
thm13AtI {hyp} x y dIxy =
  prTrans (ap1 (thmT trivCT) (DfI x y)) (encEqForm x x) (encEqForm x y)
    self pairRewrite
  where
  A : Term
  A = ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) (ap1 cor x))

  -- Step 1: Guard's Th 12 specialized at f = I.
  self : Provable hyp (atomic (eqn (ap1 (thmT trivCT) (DfI x y)) (encEqForm x x)))
  self = fromDeriv (encAxICorr trivCT (ap1 cor x))

  -- Step 2: num-cong on the hypothesis.
  corIxy : Provable hyp (atomic (eqn (ap1 cor (ap1 I x)) (ap1 cor y)))
  corIxy = prCong1 cor (ap1 I x) y dIxy

  -- Step 3a: num-cong on axI (polymorphic in hyp, lifted via fromDeriv).
  corIxx : Provable hyp (atomic (eqn (ap1 cor (ap1 I x)) (ap1 cor x)))
  corIxx = prCong1 cor (ap1 I x) x (fromDeriv (axI x))

  -- Step 3b: cor x = cor y , via prSym + prTrans on (3a), (2).
  corxy : Provable hyp (atomic (eqn (ap1 cor x) (ap1 cor y)))
  corxy = prTrans (ap1 cor x) (ap1 cor (ap1 I x)) (ap1 cor y)
            (prSym (ap1 cor (ap1 I x)) (ap1 cor x) corIxx)
            corIxy

  -- Step 4: rewrite cor x ~> cor y inside the encoded equation's RHS
  -- slot via axEqCongR Pair.
  pairRewrite : Provable hyp (atomic
                  (eqn (ap2 Pair A (ap1 cor x)) (ap2 Pair A (ap1 cor y))))
  pairRewrite = prCongR Pair (ap1 cor x) (ap1 cor y) A corxy

------------------------------------------------------------------------
-- Implications for Route A
-- =====================================================================
--
-- The f = I case is closed.  The other Fun1 cases (Fst, Snd, Comp f g,
-- Comp2 h f g, Rec z s, KT t) are mechanical variants: for each we
-- have an  encAx*  encoder in  Guard.ProofEnc , whose  encAx*Corr
-- lemma plays the role of  encAxICorr  here.  The Provable-layer
-- rewrite step (4) is shared: rewrite  cor (arg)  to  cor (target-value)
-- via  prCongR Pair  on the rightmost slot, after applying the Fun1's
-- defining axiom + num-cong to the hypothesis.
--
-- Binary analogue  DfF2 : Fun2 -> Term -> Term -> Term -> Term
-- follows the same pattern using  encAxFst / encAxSnd / ... /
-- encAxTreeEq*  encoders.
--
-- After scaling Df through all Fun1 + Fun2 cases, chain steps 1-5 on
-- guard15.pdf p.17 translate as documented in NEXT-SESSION-BRA-
-- GODELII.md.  The closure step's  corOfReify  dissolves the abstract
--  ap1 cor (var zero)  into  reify (code (encT pe))  upon substitution
-- of a concrete encoded proof  encT pe  for  var zero  — handing
-- Gödel I the closed reified-cGSCR term it already operates on.
