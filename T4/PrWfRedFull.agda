{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfRedFull -- FULL validity  wfRedFull = pi wfRed wfFunRec  (tree-validity
-- AND funcode-validity), and its soundness over the meta shadow.
--
--   funValid_codeF1 / funValid_codeF2 : every shadow funcode validates.
--   wfFunRec_shadow  : wfFunRec (codeDer d) = O .
--   wfRedFull p      = pi (wfRed p) (wfFunRec p) .
--   wfRedFull_eq     : ap1 wfRedFull p = pi (wfRed p)(wfFunRec p) .
--   wfRedFullShadow  : wfRedFull (codeDer d) = O .
--
-- wfRedFull p = O  iff  p  is a genuine derivation tree (base-reject on the
-- tree component) whose carried funcodes are all well-formed.  This is the
-- validity used by the object reduction relation RedU in the internal CR.
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

module T4.PrWfRedFull where

open import T4.Base

open import T4.PrTriShadow
  using ( DerM ; mRefl ; mAp1c ; mAp2c ; mO ; mU ; mV ; mC ; mRb ; mRs
        ; Fun1M ; Fun2M ; f1S ; f1Zero ; f1Id ; f1Comp ; f2Proj ; f2Rec
        ; codeF1 ; codeF2 ; codeDer )
open import T4.PrWfFunShadow using ( wfFun_codeF1 ; wfFun_codeF2 ; isF1_codeF1 ; isF2_codeF2 )
open import T4.PrWfFun using ( wfFun ; isF1 ; isF2 )
open import T4.PrCodeObj using ( cRec ; cComp )
open import T4.PrWfFunRec
  using ( wfFunRec ; funValid ; wfFunRec_reflO ; wfFunRec_ap1c ; wfFunRec_ap2c
        ; wfFunRec_rO ; wfFunRec_rU ; wfFunRec_rV ; wfFunRec_rC ; wfFunRec_rRb
        ; wfFunRec_rRs )
open import T4.PrWfRed using ( wfRed )
open import T4.PrWfRedShadow using ( wfRedShadow )
open import T4.ParEnds using ( pi_O_O )

open import BRA3.Church using ( pi )
open import BRA3.PairAlgebra using ( compose1U_eq )

------------------------------------------------------------------------
-- pi O O collapse from two O children.

piBothO : (l r : Term) -> Deriv (eqF l O) -> Deriv (eqF r O) ->
          Deriv (eqF (ap2 pi l r) O)
piBothO l r el er =
  ruleTrans (congL pi r el) (ruleTrans (congR pi O er) pi_O_O)

------------------------------------------------------------------------
-- SECTION 1.  Every shadow funcode validates (funValid is one-level/shallow).

-- funValid = ap1 wfFun (PrWfFunRec), so these are exactly the deep soundness.
funValid_codeF1 : (fm : Fun1M) -> Deriv (eqF (funValid (codeF1 fm)) O)
funValid_codeF2 : (fm : Fun2M) -> Deriv (eqF (funValid (codeF2 fm)) O)
funValid_codeF1 fm = wfFun_codeF1 fm
funValid_codeF2 fm = wfFun_codeF2 fm

------------------------------------------------------------------------
-- SECTION 2.  wfFunRec (codeDer d) = O.

-- fv3 g h1 h2 = O  from the three component validities.
fv3_zero : (g h1 h2 : Term) ->
  Deriv (eqF (funValid g) O) -> Deriv (eqF (funValid h1) O) -> Deriv (eqF (funValid h2) O) ->
  Deriv (eqF (ap2 pi (funValid g) (ap2 pi (funValid h1) (funValid h2))) O)
fv3_zero g h1 h2 eg e1 e2 =
  piBothO (funValid g) (ap2 pi (funValid h1) (funValid h2)) eg
          (piBothO (funValid h1) (funValid h2) e1 e2)

wfFunRec_shadow : (d : DerM) -> Deriv (eqF (ap1 wfFunRec (codeDer d)) O)
wfFunRec_shadow mRefl = wfFunRec_reflO
wfFunRec_shadow (mAp1c fm d) =
  ruleTrans (wfFunRec_ap1c (codeF1 fm) (codeDer d))
            (piBothO (isF1 (codeF1 fm)) (ap2 pi (funValid (codeF1 fm)) (ap1 wfFunRec (codeDer d)))
                     (isF1_codeF1 fm)
                     (piBothO (funValid (codeF1 fm)) (ap1 wfFunRec (codeDer d))
                              (funValid_codeF1 fm) (wfFunRec_shadow d)))
wfFunRec_shadow (mAp2c fm d1 d2) =
  ruleTrans (wfFunRec_ap2c (codeF2 fm) (codeDer d1) (codeDer d2))
            (piBothO (isF2 (codeF2 fm))
                     (ap2 pi (funValid (codeF2 fm))
                       (ap2 pi (ap1 wfFunRec (codeDer d1)) (ap1 wfFunRec (codeDer d2))))
                     (isF2_codeF2 fm)
                     (piBothO (funValid (codeF2 fm))
                              (ap2 pi (ap1 wfFunRec (codeDer d1)) (ap1 wfFunRec (codeDer d2)))
                              (funValid_codeF2 fm)
                              (piBothO (ap1 wfFunRec (codeDer d1)) (ap1 wfFunRec (codeDer d2))
                                       (wfFunRec_shadow d1) (wfFunRec_shadow d2))))
wfFunRec_shadow (mO d) = ruleTrans (wfFunRec_rO (codeDer d)) (wfFunRec_shadow d)
wfFunRec_shadow (mU d) = ruleTrans (wfFunRec_rU (codeDer d)) (wfFunRec_shadow d)
wfFunRec_shadow (mV d1 d2) =
  ruleTrans (wfFunRec_rV (codeDer d1) (codeDer d2))
            (piBothO (ap1 wfFunRec (codeDer d1)) (ap1 wfFunRec (codeDer d2))
                     (wfFunRec_shadow d1) (wfFunRec_shadow d2))
wfFunRec_shadow (mC g h1 h2 d) =
  ruleTrans (wfFunRec_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d))
            (piBothO (ap1 wfFun (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)))
                     (ap1 wfFunRec (codeDer d))
                     (wfFun_codeF1 (f1Comp g h1 h2))
                     (wfFunRec_shadow d))
wfFunRec_shadow (mRb g h1 h2 d) =
  ruleTrans (wfFunRec_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d))
            (piBothO (ap1 wfFun (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)))
                     (ap1 wfFunRec (codeDer d))
                     (wfFun_codeF2 (f2Rec g h1 h2))
                     (wfFunRec_shadow d))
wfFunRec_shadow (mRs g h1 h2 d1 d2) =
  ruleTrans (wfFunRec_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2))
            (piBothO (ap1 wfFun (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)))
                     (ap2 pi (ap1 wfFunRec (codeDer d1)) (ap1 wfFunRec (codeDer d2)))
                     (wfFun_codeF2 (f2Rec g h1 h2))
                     (piBothO (ap1 wfFunRec (codeDer d1)) (ap1 wfFunRec (codeDer d2))
                              (wfFunRec_shadow d1) (wfFunRec_shadow d2)))

------------------------------------------------------------------------
-- SECTION 3.  Full validity  wfRedFull = pi wfRed wfFunRec .

wfRedFull : Fun1
wfRedFull = C pi wfRed wfFunRec

wfRedFull_eq : (p : Term) ->
  Deriv (eqF (ap1 wfRedFull p) (ap2 pi (ap1 wfRed p) (ap1 wfFunRec p)))
wfRedFull_eq p = ax_C pi wfRed wfFunRec p

wfRedFullShadow : (d : DerM) -> Deriv (eqF (ap1 wfRedFull (codeDer d)) O)
wfRedFullShadow d =
  ruleTrans (wfRedFull_eq (codeDer d))
            (piBothO (ap1 wfRed (codeDer d)) (ap1 wfFunRec (codeDer d))
                     (wfRedShadow d) (wfFunRec_shadow d))
