{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1Discharge -- discharge the Construct hypotheses for
-- Chaitin-Goedel I.
--
-- KEY TRICK (against Agda elaboration cost).   The Construct module's
-- internal  sim-mcode1 / sim-mcode2  recursion walks the Fun1 / Fun2
-- structure of  gFun .   At  gFun := predFlip Lstar  this structure
-- unfolds to thousands of nested  C  /  R  / Fan nodes (via  hitK ,
-- out_L ,  thmT , etc.), making the elaboration prohibitively slow.
--
-- We therefore SEAL  gFun  inside an  abstract  block.   The closure
-- witnesses  k_max_sub0 ,  k_max_sub1 ,  k_max_sim  and the Hit /
-- MissSucc lemmas are ALSO inside the abstract block (where  gFun
-- still reduces), so they type-check normally.   Outside  abstract ,
-- everything is opaque -- the Construct module's substitutions cannot
-- walk into  mcode1 gFun  any more.

module T4.ChaitinG1Discharge where

open import T4.Base
open import T4.IsNat           using ( isNat )
open import T4.KFormula        using ( Kgt )
open import T4.KRecog          using ( hitK ; hitK_le_one )
open import T4.KOut            using ( out_L )
open import T4.KFire           using ( fireAtProof_T )
open import T4.KDiag           using ( predFlip )
open import T4.KGodel1Bridge   using ( Lstar )
open import T4.StepU2          using ( step ; cfgEV ; cfgRT )
open import T4.StepU2Correct1New using ( correct1 )
open import T4.StepU2CorrectAPI  using ( Correct1 )
open import T4.EvalU           using ( mcodeMu ; mcode1 )
open import T4.Encode          using ( encode )
open import T4.ChaitinG1Arith

import T4.StepU2MuCorrect
import T4.FirstHit

open import BRA3.Church          using ( pi ; sigma ; sub ; isZero
                                       ; TisZeroZ ; TisZeroSucc )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.ChurchT73       using ( T73 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.PairAlgebra     using ( axComp )
open import BRA3.Dispatch        using ( Closed ; closedAt
                                        ; closed_O ; closed_ap1 ; closed_ap2 )
open import BRA3.RuleInst2       using ( simSubstT )
open import BRA3.Contrapositive  using ( compI ; liftP )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.CourseOfValues  using ( iter )

------------------------------------------------------------------------
-- The Discharge module.

module Discharge
  (x        : Term)
  (nx       : isNat x)
  (d        : Deriv (Kgt Lstar x))
  (cl_encD  : Closed (encode d))
  (sim_encD : (a b : Term) ->
              Eq (simSubstT zero a (suc zero) b (encode d)) (encode d))
  where

  ----------------------------------------------------------------------
  -- 1.  Open FirstHit at the recogniser (concrete; no abstract here).

  p_recog : Fun1
  p_recog = hitK Lstar (out_L Lstar)

  p_recog_le_one : (r : Term) -> Deriv (leq (ap1 p_recog r) (ap1 s O))
  p_recog_le_one = hitK_le_one Lstar (out_L Lstar)

  open T4.FirstHit.Search p_recog p_recog_le_one
    using ( leastNumber ; LeastNumber )

  ln : LeastNumber (encode d)
  ln = leastNumber (encode d) (fireAtProof_T Lstar x nx d)

  predFun : Fun1
  predFun = o

  ----------------------------------------------------------------------
  -- 2.  THE BIG ABSTRACT BLOCK.   All Construct parameters live HERE
  -- so the Fun1 structure of  predFlip Lstar  is not visible outside.

  gFun : Fun1
  gFun = predFlip Lstar

  bF : Correct1 gFun
  bF = correct1 gFun

  k_max : Term
  k_max = LeastNumber.w1 ln

  cl_kmax : Closed k_max
  cl_kmax =
    closed_ap2 _ O (ap1 s (encode d))
      closed_O
      (closed_ap1 s (encode d) cl_encD)

  k_max_sub0 : (a : Term) -> Eq (substT zero a k_max) k_max
  k_max_sub0 a = closedAt cl_kmax zero a

  k_max_sub1 : (a : Term) -> Eq (substT (suc zero) a k_max) k_max
  k_max_sub1 a = closedAt cl_kmax (suc zero) a

  -- k_max = LeastNumber.w1 ln = ap2 gRec O (ap1 s (encode d))
  -- where gRec is the Search.gRec Fun2.   simSubstT walks Term structure:
  --   simSubstT 0 a 1 b k_max = ap2 gRec O (ap1 s (simSubstT 0 a 1 b (encode d)))
  -- which equals k_max by sim_encD.
  --
  -- We BIND the Fun2 explicitly to avoid Agda inferring it as the
  -- Search.gRec unfolding (which would trigger the deep gStep / hitK /
  -- out_L recursion).

  gRec_of_kmax : Fun2
  gRec_of_kmax = R o gStep pi
    where open T4.FirstHit.Search p_recog p_recog_le_one using ( gStep )

  k_max_via_gRec : Eq k_max (ap2 gRec_of_kmax O (ap1 s (encode d)))
  k_max_via_gRec = refl

  k_max_sim : (a b : Term) -> Eq (simSubstT zero a (suc zero) b k_max) k_max
  k_max_sim a b =
    eqCong (\ inner -> ap2 gRec_of_kmax O (ap1 s inner)) (sim_encD a b)

  -- isHit:  gFun k_max = isZero (p_recog k_max) = isZero (s O) = O.

  isHit_recog : Deriv (eqF (ap1 p_recog k_max) (ap1 s O))
  isHit_recog = LeastNumber.isHit ln

  isHit : Deriv (eqF (ap1 gFun k_max) O)
  isHit =
    ruleTrans (axComp isZero p_recog k_max)
      (ruleTrans (cong1 isZero isHit_recog)
                 (ruleInst zero O TisZeroSucc))

  -- missSucc:  under (leq (s y) k_max), gFun y = s (o y).

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
  -- 3.  Construct instantiation.   With gFun and k_max abstract, the
  -- Construct module body's sim-mcode1 / substT computations are stuck
  -- on the opaque  mcode1 gFun  and  k_max , so elaboration is fast.

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
