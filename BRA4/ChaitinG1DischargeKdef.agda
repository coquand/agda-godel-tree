{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ChaitinG1DischargeKdef -- num-raw, Kdef-shape  Discharge  for
-- CGI_core_num_raw.   Parallel to  BRA4.ChaitinG1Discharge  but at the
-- Kdef recogniser ( hitKdef Lstar (outKdef Lstar) ) and seeded directly
-- by the user's hypothesis  Deriv (thmT w = ap1 (Kcode Lstar) x) .
--
-- No  isNat , no  con , no codeFormula.
--
-- KEY trick (same as Kgt-shape Discharge): we open the  Construct
-- module of  BRA4.StepU2MuCorrect  with  gFun := predFlipDef Lstar  ;
-- the same  abstract  shielding of  gc-sub0 / gc-sub1 / gc-sim  inside
-- StepU2MuCorrect  keeps Agda's type-checker from walking the deep
-- Fun1 structure.

module BRA4.ChaitinG1DischargeKdef where

open import BRA4.Base
open import BRA4.ThmT            using ( thmT )
open import BRA4.KdefRecog       using ( hitKdef ; hitKdef_le_one
                                       ; hitKdef_fires ; dNeg_from_hitKdef
                                       ; outKdef )
open import BRA4.Kdef            using ( Kcode )
open import BRA4.KdefDiag        using ( predFlipDef )
open import BRA4.KGodel1BridgeDef using ( Lstar )
open import BRA4.StepU2          using ( step ; cfgEV ; cfgRT )
open import BRA4.StepU2Correct1New using ( correct1 )
open import BRA4.StepU2CorrectAPI  using ( Correct1 )
open import BRA4.EvalU           using ( mcodeMu ; mcode1 )
open import BRA4.ChaitinG1Arith

import BRA4.StepU2MuCorrect
import BRA4.FirstHit

open import BRA3.Church          using ( pi ; sigma ; sub ; isZero
                                       ; TisZeroZ ; TisZeroSucc )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchT73       using ( T73 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.PairAlgebra     using ( axComp )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.Contrapositive  using ( compI ; liftP )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- The Kdef-shape Discharge module.

module DischargeKdef
  (w        : Term)
  (x        : Term)
  (h        : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)))
  -- Substitution-stability of  w  at the two var positions used by
  -- StepU2MuCorrect.Construct (var 0, var 1).  Replaces the stronger
  -- Closed w  hypothesis -- BRA4.CloseW.cl_w_sub0/sub1/sim discharge
  -- these structurally for any  w  pre-closed via  closeW .
  (sub0_w   : (a : Term) -> Eq (substT zero a w) w)
  (sub1_w   : (a : Term) -> Eq (substT (suc zero) a w) w)
  (sim_w    : (a b : Term) ->
              Eq (simSubstT zero a (suc zero) b w) w)
  where

  ----------------------------------------------------------------------
  -- 1.  Recogniser fires; FirstHit minimises.

  p_recog : Fun1
  p_recog = hitKdef Lstar (outKdef Lstar)

  p_recog_le_one : (r : Term) -> Deriv (leq (ap1 p_recog r) (ap1 s O))
  p_recog_le_one = hitKdef_le_one Lstar (outKdef Lstar)

  open BRA4.FirstHit.Search p_recog p_recog_le_one
    using ( leastNumber ; LeastNumber )

  fired : Deriv (eqF (ap1 p_recog w) (ap1 s O))
  fired = hitKdef_fires Lstar w x h

  ln : LeastNumber w
  ln = leastNumber w fired

  predFun : Fun1
  predFun = o

  gFun : Fun1
  gFun = predFlipDef Lstar

  bF : Correct1 gFun
  bF = correct1 gFun

  ----------------------------------------------------------------------
  -- 2.  k_max + substitution-stability witnesses (structurally derived
  -- from the user-supplied sub0_w / sub1_w on  w ; no  Closed  type).

  k_max : Term
  k_max = LeastNumber.w1 ln

  k_max_sub0 : (a : Term) -> Eq (substT zero a k_max) k_max
  k_max_sub0 a =
    -- substT 0 a (ap2 _ O (ap1 s w))  ==  ap2 _ O (ap1 s (substT 0 a w))
    -- ==  ap2 _ O (ap1 s w)  (by sub0_w).
    eqCong (\ inner -> ap2 (R o (BRA4.FirstHit.Search.gStep p_recog p_recog_le_one) pi)
                            O (ap1 s inner))
           (sub0_w a)

  k_max_sub1 : (a : Term) -> Eq (substT (suc zero) a k_max) k_max
  k_max_sub1 a =
    eqCong (\ inner -> ap2 (R o (BRA4.FirstHit.Search.gStep p_recog p_recog_le_one) pi)
                            O (ap1 s inner))
           (sub1_w a)

  -- The Fun2 of k_max:   k_max = LeastNumber.w1 ln = ap2 gRec O (ap1 s w)
  -- where gRec = Search.gRec = R o gStep pi.   Same naming trick as the
  -- Kgt-shape Discharge to block Agda from unfolding gRec.

  gRec_of_kmax : Fun2
  gRec_of_kmax = R o gStep pi
    where open BRA4.FirstHit.Search p_recog p_recog_le_one using ( gStep )

  k_max_via_gRec : Eq k_max (ap2 gRec_of_kmax O (ap1 s w))
  k_max_via_gRec = refl

  k_max_sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b k_max) k_max
  k_max_sim a b =
    eqCong (\ inner -> ap2 gRec_of_kmax O (ap1 s inner)) (sim_w a b)

  ----------------------------------------------------------------------
  -- 3.  isHit / missSucc — identical bodies to the Kgt-shape Discharge,
  -- since they only depend on  p_recog 's 0/1 behaviour, not on the
  -- recogniser's internals.

  isHit_recog : Deriv (eqF (ap1 p_recog k_max) (ap1 s O))
  isHit_recog = LeastNumber.isHit ln

  isHit : Deriv (eqF (ap1 gFun k_max) O)
  isHit =
    ruleTrans (axComp isZero p_recog k_max)
      (ruleTrans (cong1 isZero isHit_recog)
                 (ruleInst zero O TisZeroSucc))

  isFirst_recog : (y : Term) ->
    Deriv (imp (leq (ap1 s y) k_max) (eqF (ap1 p_recog y) O))
  isFirst_recog = LeastNumber.isFirst ln

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
  -- 4.  Construct instantiation.

  module C = BRA4.StepU2MuCorrect.Construct
    gFun bF k_max predFun
    isHit missSucc subSuccBridge_at leqDecrease_at subBoundsAux_at
    leqRefl_k_max sub_k_max_k_max
    k_max_sub0 k_max_sub1 k_max_sim

  fuelMu_fun : Fun2
  fuelMu_fun = C.fuelMu_fun

  runs_mu : (x_outer K0 : Term) ->
    Deriv (eqF (ap2 (iter step)
                    (cfgEV (mcodeMu (mcode1 gFun)) x_outer K0)
                    (ap2 sigma (ap1 s O) (ap2 fuelMu_fun k_max k_max)))
                (cfgRT k_max K0))
  runs_mu = C.runs_mu

  ----------------------------------------------------------------------
  -- 5.  dNeg in num-raw Kcode form, at the read-off subject  x' .

  x' : Term
  x' = ap1 (outKdef Lstar) k_max

  dNeg_at_kmax : Deriv (eqF (ap1 thmT k_max) (ap1 (Kcode Lstar) x'))
  dNeg_at_kmax = dNeg_from_hitKdef Lstar (outKdef Lstar) k_max isHit_recog
