{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SuLegParts -- confident foundational pieces for the su-leg head-stability
-- (certHeadSu_obj / objJoinClash):
--
--   inner2HeadIs2 : Fst (inner2 pkg) = natCode 2      (cellRO/cellRS both ad-headed)
--   inner1HeadIs2 : Fst (inner1 pkg) = natCode 2      (cellAd + inner2, all ad-headed)
--   refuter21_imp : imp (natCode 2 = natCode 1) Q     (ex falso via predecessor: s(sO)=sO -> sO=O)
--
-- These give, for the  test1 = O  branch of certHeadSu, that the src step-body
-- head is  natCode 2 = tagAd , clashing with the su hypothesis  tagSu = natCode 1.
-- Single-antecedent `byCases` (Goal fixed = natCode 2), reusing StepDispatchImp +
-- CellHead + ImpEq.  No holes, no postulates, no termination warnings; --safe.

module T4.SuLegParts where

open import T4.Base

open import T4.ParEnds using ( inner1 ; inner2 ; test2 ; test3 )
open import T4.CellHead using ( hd_cellAd ; hd_cellRO ; hd_cellRS )
open import T4.StepDispatchImp using ( to_cellAd_imp ; to_inner2_imp ; to_cellRO_imp ; to_cellRS_imp )
open import T4.ImpEq using ( impCong1 ; impRuleTrans ; impSym )

open import BRA3.Logic          using ( impTrans )
open import BRA3.Contrapositive using ( liftP ; identP )
open import BRA3.Church         using ( predecessor ; T_p_S_v0 )
open import BRA3.ChurchT80      using ( succEqO_to_anything )
open import T4.PHP              using ( byCases )

------------------------------------------------------------------------
-- inner2 head = natCode 2  (cellRO / cellRS both ad-headed).

inner2HeadIs2 : (pkg : Term) ->
  Deriv (eqF (ap1 Fst (ap1 inner2 pkg)) (natCode 2))
inner2HeadIs2 pkg =
  byCases (eqF (ap1 test3 pkg) O) (eqF (ap1 Fst (ap1 inner2 pkg)) (natCode 2))
    (impRuleTrans (impCong1 Fst (to_cellRS_imp pkg))
                  (liftP (eqF (ap1 test3 pkg) O) (hd_cellRS pkg)))
    (impRuleTrans (impCong1 Fst (to_cellRO_imp pkg))
                  (liftP (neg (eqF (ap1 test3 pkg) O)) (hd_cellRO pkg)))

------------------------------------------------------------------------
-- inner1 head = natCode 2  (cellAd + inner2).

inner1HeadIs2 : (pkg : Term) ->
  Deriv (eqF (ap1 Fst (ap1 inner1 pkg)) (natCode 2))
inner1HeadIs2 pkg =
  byCases (eqF (ap1 test2 pkg) O) (eqF (ap1 Fst (ap1 inner1 pkg)) (natCode 2))
    (impRuleTrans (impCong1 Fst (to_inner2_imp pkg))
                  (liftP (eqF (ap1 test2 pkg) O) (inner2HeadIs2 pkg)))
    (impRuleTrans (impCong1 Fst (to_cellAd_imp pkg))
                  (liftP (neg (eqF (ap1 test2 pkg) O)) (hd_cellAd pkg)))

------------------------------------------------------------------------
-- natCode 2 = natCode 1 is ex falso (predecessor: pred(natCode 2)=natCode 1,
-- pred(natCode 1)=O, so natCode 1 = O = s O contradiction).

refuter21_imp : (Q : Formula) ->
  Deriv (imp (eqF (natCode 2) (natCode 1)) Q)
refuter21_imp Q =
  let xf : Formula
      xf = eqF (natCode 2) (natCode 1)
      p2 : Deriv (eqF (ap1 predecessor (natCode 2)) (natCode 1))
      p2 = ruleInst 0 (natCode 1) T_p_S_v0
      p1 : Deriv (eqF (ap1 predecessor (natCode 1)) O)
      p1 = ruleInst 0 O T_p_S_v0
      peImp : Deriv (imp xf (eqF (ap1 predecessor (natCode 2)) (ap1 predecessor (natCode 1))))
      peImp = impCong1 predecessor (identP xf)
      toO : Deriv (imp xf (eqF (natCode 1) O))
      toO = impRuleTrans (impSym (liftP xf p2))
              (impRuleTrans peImp (liftP xf p1))
  in impTrans toO (succEqO_to_anything O Q)
