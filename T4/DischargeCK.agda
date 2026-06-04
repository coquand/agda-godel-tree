{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DischargeCK -- surprise-GII task (b): the  Discharge  step at the CK
-- single-atom characteristic-function shape.   A mechanical port of
-- T4.ChaitinG1DischargeKdefConj , re-pointed from the conjunction recogniser
-- ( hitKdefConj enum N (outKdefConj enum N) ) to the single-atom CK recogniser
-- ( T4.CKRecog.hitCK CK i1 (outCK CK i1) ) and the CK diagonal predicate
-- gFunCK = isZero . hitCK CK i1 (outCK CK i1) .
--
-- The FirstHit search + the  StepU2MuCorrect.Construct  mu-loop substrate are
-- GENERIC in the predicate  gFun  and the recogniser's 0/1 behaviour, so the
-- body is verbatim; only the recogniser / predicate / code-builder change.
-- Output:  k_max , x' = outCK k_max , runs_mu , and
--   dNeg_at_kmax :  thmT k_max = ap1 (KcodeCK CK i1) x'
-- ( = negCKcode (ap1 num x') (cVarc i1)  by  KcodeCK_eval -- the exact  dNeg
--   that  T4.CgiClashCK.cgiClashCK  consumes ).

module T4.DischargeCK where

open import T4.Base
open import T4.ThmT            using ( thmT )
open import T4.CKRecog        using ( hitCK ; hitCK_le_one ; hitCK_fires
                                     ; dNeg_from_hitCK ; outCK ; KcodeCK )
open import T4.StepU2          using ( step ; cfgEV ; cfgRT )
open import T4.StepU2Correct1New using ( correct1 )
open import T4.StepU2CorrectAPI  using ( Correct1 )
open import T4.EvalU           using ( mcodeMu ; mcode1 )
open import T4.ChaitinG1Arith

import T4.StepU2MuCorrect
import T4.FirstHit

open import BRA3.Church          using ( pi ; sigma ; sub ; isZero
                                       ; TisZeroZ ; TisZeroSucc )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchT73       using ( T73 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.PairAlgebra     using ( axComp ; compose1U )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.Contrapositive  using ( compI ; liftP )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- The CK-shape Discharge module.

module DischargeCK
  (CK       : Fun2)
  (i1       : Nat)
  (w        : Term)
  (x        : Term)
  (h        : Deriv (eqF (ap1 thmT w) (ap1 (KcodeCK CK i1) x)))
  (sub0_w   : (a : Term) -> Eq (substT zero a w) w)
  (sub1_w   : (a : Term) -> Eq (substT (suc zero) a w) w)
  (sim_w    : (a b : Term) ->
              Eq (simSubstT zero a (suc zero) b w) w)
  where

  ----------------------------------------------------------------------
  -- 1.  Recogniser fires; FirstHit minimises.

  p_recog : Fun1
  p_recog = hitCK CK i1 (outCK CK i1)

  p_recog_le_one : (r : Term) -> Deriv (leq (ap1 p_recog r) (ap1 s O))
  p_recog_le_one = hitCK_le_one CK i1 (outCK CK i1)

  open T4.FirstHit.Search p_recog p_recog_le_one
    using ( leastNumber ; LeastNumber )

  fired : Deriv (eqF (ap1 p_recog w) (ap1 s O))
  fired = hitCK_fires CK i1 w x h

  ln : LeastNumber w
  ln = leastNumber w fired

  predFun : Fun1
  predFun = o

  gFun : Fun1
  gFun = compose1U isZero p_recog

  bF : Correct1 gFun
  bF = correct1 gFun

  ----------------------------------------------------------------------
  -- 2.  k_max + substitution-stability witnesses.

  k_max : Term
  k_max = LeastNumber.w1 ln

  k_max_sub0 : (a : Term) -> Eq (substT zero a k_max) k_max
  k_max_sub0 a =
    eqCong (\ inner -> ap2 (R o (T4.FirstHit.Search.gStep p_recog p_recog_le_one) pi)
                            O (ap1 s inner))
           (sub0_w a)

  k_max_sub1 : (a : Term) -> Eq (substT (suc zero) a k_max) k_max
  k_max_sub1 a =
    eqCong (\ inner -> ap2 (R o (T4.FirstHit.Search.gStep p_recog p_recog_le_one) pi)
                            O (ap1 s inner))
           (sub1_w a)

  gRec_of_kmax : Fun2
  gRec_of_kmax = R o gStep pi
    where open T4.FirstHit.Search p_recog p_recog_le_one using ( gStep )

  k_max_via_gRec : Eq k_max (ap2 gRec_of_kmax O (ap1 s w))
  k_max_via_gRec = refl

  k_max_sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b k_max) k_max
  k_max_sim a b =
    eqCong (\ inner -> ap2 gRec_of_kmax O (ap1 s inner)) (sim_w a b)

  ----------------------------------------------------------------------
  -- 3.  isHit / missSucc — depend only on  p_recog 's 0/1 behaviour.

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

  module C = T4.StepU2MuCorrect.Construct
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
  -- 5.  dNeg in num-raw KcodeCK form, at the read-off subject  x' .

  x' : Term
  x' = ap1 (outCK CK i1) k_max

  dNeg_at_kmax : Deriv (eqF (ap1 thmT k_max) (ap1 (KcodeCK CK i1) x'))
  dNeg_at_kmax = dNeg_from_hitCK CK i1 (outCK CK i1) k_max isHit_recog
