{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EvalUMuObj -- Term-indexed object-induction Mu (v2; lean shape).
--
-- Bridges  evalU  on  gLcodeDef Lstar  to  FirstHit.Search.g , delivering
--
--   runDeriv : (w x : Term) (hyp : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))) ->
--     Sigma Term (\ n0 ->
--       Deriv (eqF (ap2 evalU (ap1 parse gLname) n0) (ap1 s (subjOf w x hyp))))
--
-- See  T4/CGI-RUN-OBJINDUCT-HANDOFF-v2.md  for the build map.
--
-- This file is incremental: Section 1 (the  predFlipDef  value lemmas).

module T4.EvalUMuObj where

open import T4.Base
open import T4.ThmT          using ( thmT )
open import T4.Kdef          using ( Kcode )
open import T4.KdefDiag      using ( predFlipDef )
open import T4.KdefRecog     using
  ( outKdef ; hitKdef ; hitKdef_le_one ; hitKdef_fires )
open import T4.FirstHit      using ( module Search )
open import T4.KGodel1Bridge using ( Lstar )

open import BRA3.Church          using ( isZero ; TisZeroZ ; TisZeroSucc ; sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using ( compose1U ; compose1U_eq )
open import BRA3.Contrapositive  using ( compI )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )

------------------------------------------------------------------------
-- The Search module instance, fixed at the K-recogniser  hitKdef Lstar (outKdef Lstar) .

module _ where
  pK : Fun1
  pK = hitKdef Lstar (outKdef Lstar)

  pK_le_one : (r : Term) -> Deriv (leq (ap1 pK r) (ap1 s O))
  pK_le_one = hitKdef_le_one Lstar (outKdef Lstar)

  open Search pK pK_le_one public renaming ( g to gSearch ; LeastNumber to LN ; leastNumber to lnum )

------------------------------------------------------------------------
-- The "Run" module:  parametric in  w / x / hyp .  Inside it, the first hit
--  fH = w1 (lnum w (hitKdef_fires Lstar w x hyp))  and the subject  z = outKdef Lstar fH
-- are pinned, then Section 1's three value lemmas about  predFlipDef Lstar  follow.

module Run
  (w x : Term)
  (hyp : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)))
  where

  hitAtW : Deriv (eqF (ap1 pK w) (ap1 s O))
  hitAtW = hitKdef_fires Lstar w x hyp

  searchLN : LN w
  searchLN = lnum w hitAtW

  fH : Term
  fH = LN.w1 searchLN

  z : Term
  z = ap1 (outKdef Lstar) fH

  ----------------------------------------------------------------------
  -- SECTION 1.  predFlipDef value lemmas (~30 LoC).
  --
  -- predFlipDef Lstar = compose1U isZero pK , so  ap1 (predFlipDef Lstar) r
  -- = ap1 isZero (ap1 pK r) .  Then for  r < fH ,  pK r = O  (firstness) and
  -- isZero O = sO ; at  r = fH ,  pK fH = sO  (least_hit) and isZero (sO) = O .

  predFlipDef_unfold :
    (r : Term) ->
    Deriv (eqF (ap1 (predFlipDef Lstar) r) (ap1 isZero (ap1 pK r)))
  predFlipDef_unfold r = compose1U_eq isZero pK r

  -- Firstness:  leq (s r) fH  ->  predFlipDef Lstar r = s O .
  predFlipDef_misses :
    (r : Term) ->
    Deriv (imp (leq (ap1 s r) fH) (eqF (ap1 (predFlipDef Lstar) r) (ap1 s O)))
  predFlipDef_misses r =
    let isFirst_r : Deriv (imp (leq (ap1 s r) fH) (eqF (ap1 pK r) O))
        isFirst_r = LN.isFirst searchLN r

        -- (pK r = O)  ->  (isZero (pK r) = isZero O)   (congruence under isZero).
        isZ_eq : Deriv (imp (eqF (ap1 pK r) O)
                            (eqF (ap1 isZero (ap1 pK r)) (ap1 isZero O)))
        isZ_eq = ax_eqCong1 isZero (ap1 pK r) O

        -- (isZero (pK r) = isZero O)  ->  (isZero (pK r) = sO)   via TisZeroZ.
        isZ_sO : Deriv (imp (eqF (ap1 isZero (ap1 pK r)) (ap1 isZero O))
                            (eqF (ap1 isZero (ap1 pK r)) (ap1 s O)))
        isZ_sO = appendEqRight (ap1 isZero (ap1 pK r)) (ap1 isZero O) (ap1 s O) TisZeroZ

        -- combine: leq (s r) fH  ->  isZero (pK r) = sO .
        isZ_at_pKr : Deriv (imp (leq (ap1 s r) fH) (eqF (ap1 isZero (ap1 pK r)) (ap1 s O)))
        isZ_at_pKr = compI isFirst_r (compI isZ_eq isZ_sO)

        -- prepend  predFlipDef_unfold r  to rewrite the LHS.
        bridge : Deriv (imp (eqF (ap1 isZero (ap1 pK r)) (ap1 s O))
                            (eqF (ap1 (predFlipDef Lstar) r) (ap1 s O)))
        bridge = prependEqLeft (ap1 (predFlipDef Lstar) r) (ap1 isZero (ap1 pK r)) (ap1 s O)
                   (predFlipDef_unfold r)
    in compI isZ_at_pKr bridge

  -- At the first hit:  predFlipDef Lstar fH = O .
  predFlipDef_at_fH : Deriv (eqF (ap1 (predFlipDef Lstar) fH) O)
  predFlipDef_at_fH =
    let isHit_fH : Deriv (eqF (ap1 pK fH) (ap1 s O))
        isHit_fH = LN.isHit searchLN

        -- pK fH = sO , so  isZero (pK fH) = isZero (sO) .
        e1 : Deriv (eqF (ap1 isZero (ap1 pK fH)) (ap1 isZero (ap1 s O)))
        e1 = cong1 isZero isHit_fH

        -- TisZeroSucc : isZero (s var0) = O .  ruleInst at 0 := O.
        e2 : Deriv (eqF (ap1 isZero (ap1 s O)) O)
        e2 = ruleInst 0 O TisZeroSucc

    in ruleTrans (predFlipDef_unfold fH) (ruleTrans e1 e2)
