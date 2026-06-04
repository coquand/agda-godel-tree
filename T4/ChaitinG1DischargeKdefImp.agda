{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1DischargeKdefImp -- Carneiro-lifted (imp Rf) variant of
-- T4.ChaitinG1DischargeKdef.
--
-- The original  DischargeKdef  module is parametric in
--   (w x : Term)  (h : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)))
-- + substitution-stability witnesses on  w .
--
-- The imp-lifted variant  DischargeKdefImp  is parametric in
--   (Rf : Formula)
--   (w x : Term)
--   (hyp_imp : Deriv (imp Rf (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))))
-- + the SAME substitution-stability witnesses (no  h  dependency).
--
-- Exports:
--   * k_max , x'  (Terms -- IDENTICAL to the closed module, h-independent)
--   * imp_isHit_recog , imp_isHit , imp_missSucc (Carneiro-lifted Derivs)
--   * isFirst_recog (closed -- least_first is closed)
--   * imp_dNeg_at_kmax
--
-- All h-dependent Derivs are replaced by their  imp Rf  variants.

module T4.ChaitinG1DischargeKdefImp where

open import T4.Base
open import T4.ThmT            using ( thmT )
open import T4.KdefRecog       using ( hitKdef ; hitKdef_le_one
                                       ; outKdef )
open import T4.KdefRecogImp    using ( imp_hitKdef_fires
                                       ; imp_dNeg_from_hitKdef )
open import T4.Kdef            using ( Kcode )
open import T4.KdefDiag        using ( predFlipDef )
open import T4.KGodel1BridgeDef using ( Lstar )
open import T4.StepU2          using ( step ; cfgEV ; cfgRT )
open import T4.ChaitinG1Arith
open import T4.ImpExtras       using ( imp_compI ; imp_byCases )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp ; impEqTrans ; impCong1 ; impCongL ; impCongR )

import T4.FirstHit
import T4.FirstHitImp

open import BRA3.Church          using ( pi ; sigma ; sub ; isZero
                                       ; TisZeroZ ; TisZeroSucc )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchT73       using ( T73 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.PairAlgebra     using ( axComp )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.Contrapositive  using ( compI ; liftP )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )

------------------------------------------------------------------------
-- The imp-lifted Discharge module.

module DischargeKdefImp
  (Rf       : Formula)
  (w        : Term)
  (x        : Term)
  (hyp_imp  : Deriv (imp Rf (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))))
  (sub0_w   : (a : Term) -> Eq (substT zero a w) w)
  (sub1_w   : (a : Term) -> Eq (substT (suc zero) a w) w)
  (sim_w    : (a b : Term) ->
              Eq (simSubstT zero a (suc zero) b w) w)
  where

  ----------------------------------------------------------------------
  -- 1.  Recogniser, fires (imp-lifted), least-number (imp-lifted).

  p_recog : Fun1
  p_recog = hitKdef Lstar (outKdef Lstar)

  p_recog_le_one : (r : Term) -> Deriv (leq (ap1 p_recog r) (ap1 s O))
  p_recog_le_one = hitKdef_le_one Lstar (outKdef Lstar)

  open T4.FirstHit.Search p_recog p_recog_le_one
    using ( gStep )
  open T4.FirstHitImp.SearchImp p_recog p_recog_le_one
    using ( ImpLeastNumber ; imp_leastNumber ; imp_least_hit )

  -- The imp-lifted firing fact:  imp Rf (eqF (p_recog w) (s O)) .
  imp_fired : Deriv (imp Rf (eqF (ap1 p_recog w) (ap1 s O)))
  imp_fired = imp_hitKdef_fires Rf Lstar w x hyp_imp

  -- ln_imp : ImpLeastNumber Rf w  -- the imp-lifted least-number record.
  ln_imp : ImpLeastNumber Rf w
  ln_imp = imp_leastNumber Rf w imp_fired

  predFun : Fun1
  predFun = o

  gFun : Fun1
  gFun = predFlipDef Lstar

  ----------------------------------------------------------------------
  -- 2.  k_max + substitution-stability witnesses (CLOSED in Rf -- the
  -- Term k_max is identical to the closed module, depending only on w).

  k_max : Term
  k_max = ImpLeastNumber.w1 ln_imp
  -- definitionally  = ap2 gRec O (ap1 s w) .

  -- gRec_of_kmax shape for sub0/sub1/sim rewrites:
  gRec_of_kmax : Fun2
  gRec_of_kmax = R o gStep pi

  k_max_via_gRec : Eq k_max (ap2 gRec_of_kmax O (ap1 s w))
  k_max_via_gRec = refl

  k_max_sub0 : (a : Term) -> Eq (substT zero a k_max) k_max
  k_max_sub0 a =
    eqCong (\ inner -> ap2 gRec_of_kmax O (ap1 s inner)) (sub0_w a)

  k_max_sub1 : (a : Term) -> Eq (substT (suc zero) a k_max) k_max
  k_max_sub1 a =
    eqCong (\ inner -> ap2 gRec_of_kmax O (ap1 s inner)) (sub1_w a)

  k_max_sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b k_max) k_max
  k_max_sim a b =
    eqCong (\ inner -> ap2 gRec_of_kmax O (ap1 s inner)) (sim_w a b)

  ----------------------------------------------------------------------
  -- 3.  imp_isHit_recog / imp_isHit / imp_missSucc / isFirst_recog .

  imp_isHit_recog : Deriv (imp Rf (eqF (ap1 p_recog k_max) (ap1 s O)))
  imp_isHit_recog = ImpLeastNumber.isHit ln_imp

  -- imp_isHit :  imp Rf (eqF (ap1 gFun k_max) O) .
  -- Original (closed):
  --   isHit = ruleTrans (axComp isZero p_recog k_max)
  --             (ruleTrans (cong1 isZero isHit_recog)
  --                        (ruleInst zero O TisZeroSucc))
  imp_isHit : Deriv (imp Rf (eqF (ap1 gFun k_max) O))
  imp_isHit =
    let e1 : Deriv (eqF (ap1 gFun k_max) (ap1 isZero (ap1 p_recog k_max)))
        e1 = axComp isZero p_recog k_max

        e2_imp : Deriv (imp Rf (eqF (ap1 isZero (ap1 p_recog k_max))
                                     (ap1 isZero (ap1 s O))))
        e2_imp = impCong1 isZero (ap1 p_recog k_max) (ap1 s O) imp_isHit_recog

        e3 : Deriv (eqF (ap1 isZero (ap1 s O)) O)
        e3 = ruleInst zero O TisZeroSucc

        step1 :
          Deriv (imp Rf (eqF (ap1 gFun k_max)
                              (ap1 isZero (ap1 p_recog k_max))))
        step1 = impLift {Rf} e1

        step2 :
          Deriv (imp Rf (eqF (ap1 gFun k_max) (ap1 isZero (ap1 s O))))
        step2 = impEqTrans (ap1 gFun k_max) (ap1 isZero (ap1 p_recog k_max))
                  (ap1 isZero (ap1 s O)) step1 e2_imp

    in impEqTrans (ap1 gFun k_max) (ap1 isZero (ap1 s O)) O
         step2 (impLift {Rf} e3)

  -- isFirst_recog : CLOSED (least_first is closed).
  isFirst_recog : (y : Term) ->
    Deriv (imp (leq (ap1 s y) k_max) (eqF (ap1 p_recog y) O))
  isFirst_recog = ImpLeastNumber.isFirst ln_imp

  -- imp_missSucc :  two-level Carneiro-lifted .
  --
  -- Original missSucc has shape:
  --   Deriv (imp (leq (s y) k_max) (eqF (gFun y) (s (predFun y))))
  --
  -- The h-dependence is INDIRECT: missSucc only uses isFirst_recog (closed)
  -- and closed cong/axiom chains.  So we can copy the closed body and
  -- lift only at the final step via impLift.
  --
  -- (Indeed, missSucc in the original DischargeKdef is built from
  --  isFirst_recog (which is closed) via compI + cong1 + appendEqRight
  --  + prependEqLeft, all closed.   No witness/h enters missSucc.)

  missSucc :
    (y : Term) ->
    Deriv (imp (leq (ap1 s y) k_max)
               (eqF (ap1 gFun y) (ap1 s (ap1 predFun y))))
  missSucc y =
    let e_gFun : Deriv (eqF (ap1 gFun y) (ap1 isZero (ap1 p_recog y)))
        e_gFun = axComp isZero p_recog y
        e_pO : Deriv (imp (leq (ap1 s y) k_max) (eqF (ap1 p_recog y) O))
        e_pO = isFirst_recog y
        e_isZ_step :
          Deriv (imp (leq (ap1 s y) k_max)
                     (eqF (ap1 isZero (ap1 p_recog y)) (ap1 isZero O)))
        e_isZ_step = compI e_pO (ax_eqCong1 isZero (ap1 p_recog y) O)
        e_isZ_O : Deriv (eqF (ap1 isZero O) (ap1 s O))
        e_isZ_O = TisZeroZ
        e_s_oy_sym : Deriv (eqF (ap1 s O) (ap1 s (ap1 o y)))
        e_s_oy_sym = ruleSym (cong1 s (ax_o y))
        chain1 : Deriv (imp (leq (ap1 s y) k_max)
                            (eqF (ap1 gFun y) (ap1 isZero O)))
        chain1 = compI e_isZ_step
                   (prependEqLeft (ap1 gFun y) (ap1 isZero (ap1 p_recog y))
                                  (ap1 isZero O) e_gFun)
        chain2 : Deriv (imp (leq (ap1 s y) k_max)
                            (eqF (ap1 gFun y) (ap1 s O)))
        chain2 = compI chain1
                   (appendEqRight (ap1 gFun y) (ap1 isZero O) (ap1 s O) e_isZ_O)
    in compI chain2
         (appendEqRight (ap1 gFun y) (ap1 s O) (ap1 s (ap1 o y)) e_s_oy_sym)

  -- closed support facts re-exported from ChaitinG1Arith.

  subSuccBridge_at :
    (y : Term) ->
    Deriv (imp (leq (ap1 s y) k_max)
               (eqF (ap1 s (ap2 sub k_max (ap1 s y)))
                    (ap2 sub k_max y)))
  subSuccBridge_at y = subSuccBridge y k_max

  leqDecrease_at :
    (y : Term) -> Deriv (imp (leq (ap1 s y) k_max) (leq y k_max))
  leqDecrease_at y = leqDecrease y k_max

  subBoundsAux_at :
    (y : Term) ->
    Deriv (imp (leq (ap1 s y) k_max)
               (leq (ap1 s (ap2 sub k_max (ap1 s y))) k_max))
  subBoundsAux_at y = subBoundsAux y k_max

  leqRefl_k_max : Deriv (leq k_max k_max)
  leqRefl_k_max = ruleInst zero k_max T73

  sub_k_max_k_max : Deriv (eqF (ap2 sub k_max k_max) O)
  sub_k_max_k_max = sub_self k_max

  ----------------------------------------------------------------------
  -- 4.  imp_dNeg_at_kmax -- the Carneiro-lifted dNeg fact.

  x' : Term
  x' = ap1 (outKdef Lstar) k_max

  imp_dNeg_at_kmax :
    Deriv (imp Rf (eqF (ap1 thmT k_max) (ap1 (Kcode Lstar) x')))
  imp_dNeg_at_kmax =
    imp_dNeg_from_hitKdef Rf Lstar (outKdef Lstar) k_max imp_isHit_recog
