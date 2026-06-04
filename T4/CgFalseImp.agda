{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgFalseImp -- Phase 1 closing wrapper.
--
-- Wires  T4.StepU2MuCorrectImp.ImpConstruct.imp_runs_mu  (the
-- Carneiro-lifted Construct.runs_mu) into
-- T4.CgFunImp.cgFalseImp_general  to produce the final
-- Carneiro-lifted (imp Rf) cgFalse  derivation:
--
--   cgFalseImp :
--     (Rf : Formula) (w : Term)
--     (sub0_Rf , sub1_Rf , sim_Rf : Rf-closedness at vars 0/1) ->
--     Deriv (imp Rf (eqF (ap1 thmT (closeW w))
--                         (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w))))) ->
--     Deriv (imp Rf (eqF (ap1 thmT (cgFun w)) codeFalse))
--
-- The Rf-closedness witnesses are propagated to  ImpConstruct  (where
-- they're needed for the ruleIndNat motive  Q := imp Rf P  and the
-- ruleInst2 bridge in the bundle wrapper).

module T4.CgFalseImp where

open import T4.Base
open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.Kdef             using ( Kcode )
open import T4.KdefRecog        using ( outKdef )
open import T4.KGodel1BridgeDef using ( Lstar )
open import T4.CloseW           using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )
open import T4.CgFun            using ( cgFun )
open import T4.StepU2Correct1New using ( correct1 )
open import T4.StepU2CorrectAPI  using ( Correct1 )

open import T4.Thm12.ImpHelpers using ( impRefl )

import T4.ChaitinG1DischargeKdefImp as DKI
import T4.StepU2MuCorrectImp        as MCI

open import T4.CgFunImp   using ( cgFalseImp_general )
open import T4.CgiClashImp using ( ImpSomeProof ; Sigma )

open import BRA3.RuleInst2 using ( simSubstT ; simSubstF )
open import BRA3.Formula   using ( substF )

------------------------------------------------------------------------
-- cgFalseImp :  Carneiro-lifted cgFalse, Phase 1 closed.

cgFalseImp :
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (eqF (ap1 thmT (closeW w))
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w))))) ->
  Deriv (imp Rf (eqF (ap1 thmT (cgFun w)) codeFalse))
cgFalseImp Rf w sub0_Rf sub1_Rf sim_Rf hyp_imp =
  let
    cw : Term
    cw = closeW w

    x_subj : Term
    x_subj = ap1 (outKdef Lstar) cw

    open DKI.DischargeKdefImp
      Rf cw x_subj hyp_imp (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
      using ( gFun ; predFun ; k_max ; imp_isHit
            ; missSucc ; subSuccBridge_at ; leqDecrease_at ; subBoundsAux_at
            ; leqRefl_k_max ; sub_k_max_k_max
            ; k_max_sub0 ; k_max_sub1 ; k_max_sim )

    bF : Correct1 gFun
    bF = correct1 gFun

    open MCI.ImpConstruct
      Rf gFun bF k_max predFun
      imp_isHit
      missSucc subSuccBridge_at leqDecrease_at subBoundsAux_at
      leqRefl_k_max sub_k_max_k_max
      k_max_sub0 k_max_sub1 k_max_sim
      sub0_Rf sub1_Rf sim_Rf
      using ( fuelMu_fun ; imp_runs_mu )

    result : ImpSomeProof Rf
    result = cgFalseImp_general Rf cw (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
              hyp_imp fuelMu_fun imp_runs_mu

  in Sigma.snd result

------------------------------------------------------------------------
-- cgFalseImpDed :  deduction-theorem internalisation of  cgFalse .
--
-- The meta function
--     cgFalse : (w : Term) -> Deriv X(w) -> Deriv Y(w)
-- internalises (within BRA's Hilbert system) to a closed Hilbert formula
--     imp X(w) Y(w)
-- via the deduction theorem.   For  w  closed at vars 0/1  ( numerals ,
-- codes ,  any  Term  with neither  var 0  nor  var 1  free ) the three
-- closedness witnesses collapse to reflexivity and the form is exactly
-- the user's expected
--
--   cgFalseImp_w :
--     Deriv (imp (eqF (ap1 thmT w)
--                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))
--                 (eqF (ap1 thmT (cgFun w)) codeFalse))
--
-- with NO meta arrow ;  a big improvement over the meta  cgFalse .
--
-- Derived from  cgFalseImp  by:
--   * Setting the Carneiro hypothesis  Rf := X(w) .
--   * Closedness of  Rf  at vars 0/1  +  sim  derived from  w 's
--     closedness via  eqCong  on the K-formula motive.
--   * The  closeW w = w  identity  ( derivable from  sub0_w O  +
--     sub1_w O ) bridges  impRefl X(w)  to the  closeW -shape
--     hypothesis expected by  cgFalseImp .

cgFalseImpDed :
  (w : Term) ->
  ((a : Term) -> Eq (substT zero a w) w) ->
  ((a : Term) -> Eq (substT (suc zero) a w) w) ->
  ((a b : Term) -> Eq (simSubstT zero a (suc zero) b w) w) ->
  Deriv (imp (eqF (ap1 thmT w)
                   (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))
              (eqF (ap1 thmT (cgFun w)) codeFalse))
cgFalseImpDed w sub0_w sub1_w sim_w =
  let
    HypAt : Term -> Formula
    HypAt t = eqF (ap1 thmT t) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) t))

    Hyp : Formula
    Hyp = HypAt w

    -- Hyp's closedness at vars 0 / 1 + sim , derived from  w 's
    -- closedness via  eqCong HypAt .
    sub0_Hyp : (a : Term) -> Eq (substF zero a Hyp) Hyp
    sub0_Hyp a = eqCong HypAt (sub0_w a)

    sub1_Hyp : (a : Term) -> Eq (substF (suc zero) a Hyp) Hyp
    sub1_Hyp a = eqCong HypAt (sub1_w a)

    sim_Hyp : (a b : Term) -> Eq (simSubstF zero a (suc zero) b Hyp) Hyp
    sim_Hyp a b = eqCong HypAt (sim_w a b)

    -- closeW w  =  substT zero O (substT (suc zero) O w)  =  w
    -- via  sub1_w O  +  sub0_w O .
    cw_eq_w : Eq (closeW w) w
    cw_eq_w =
      eqTrans
        (eqCong (substT zero O) (sub1_w O))
        (sub0_w O)

    -- hyp_imp : Deriv (imp Hyp (HypAt (closeW w)))  via  impRefl Hyp
    -- bridged through  cw_eq_w .
    hyp_imp :
      Deriv (imp Hyp
             (eqF (ap1 thmT (closeW w))
                   (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w)))))
    hyp_imp =
      eqSubst (\ t -> Deriv (imp Hyp (HypAt t)))
              (eqSym cw_eq_w) (impRefl Hyp)
  in cgFalseImp Hyp w sub0_Hyp sub1_Hyp sim_Hyp hyp_imp

------------------------------------------------------------------------
-- cgFalseImpAtVar2 :  cgFalseImpDed instantiated at  w := var 2 .
--
-- All three closedness witnesses collapse to  refl  because  substT
-- zero  /  substT (suc zero)  /  simSubstT zero ... (suc zero)  on
-- var 2 = var (suc (suc zero))  are all reflexivity (the var-pattern
-- of substT yields  var 2  unchanged when natEq 0 2 = false  and
-- natEq 1 2 = false ) .   The result is a closed Hilbert formula
-- internalising the meta arrow  cgFalse  at the universal witness
-- var 2 ;   for any concrete  t  closed at vars 0/1 ,  ruleInst (suc
-- (suc zero)) t  specialises it to  Deriv (imp X(t) Y(t)) .

cgFalseImpAtVar2 :
  Deriv (imp (eqF (ap1 thmT (var (suc (suc zero))))
                   (ap1 (Kcode Lstar)
                         (ap1 (outKdef Lstar) (var (suc (suc zero))))))
              (eqF (ap1 thmT (cgFun (var (suc (suc zero))))) codeFalse))
cgFalseImpAtVar2 =
  cgFalseImpDed (var (suc (suc zero)))
    (\ _ -> refl) (\ _ -> refl) (\ _ _ -> refl)

------------------------------------------------------------------------
-- cgFalseImpAtVar0 :  re-dispatch  cgFalseImpAtVar2  to  var 0  via
-- ruleInst .   Pure Hilbert universal instantiation:   substF (suc
-- (suc zero)) (var zero)  replaces every  var 2  occurrence with
-- var 0  throughout the formula .   On the X (hypothesis) side this
-- recovers exactly  X(var 0) ;   on the Y (conclusion) side the
-- substituted term  substT (suc (suc zero)) (var zero) (cgFun (var
-- (suc (suc zero))))  has  var 0  wherever  cgFun (var 2)  had  var 2
-- (which originally came from  closeW (var 2) = var 2  in cgFun's
-- internal  cw  slots) -- this is NOT  cgFun (var zero) , because
-- cgFun (var zero)  embeds  closeW (var zero) = O  in those slots .

cgFalseImpAtVar0 :
  Deriv (substF (suc (suc zero)) (var zero)
          (imp (eqF (ap1 thmT (var (suc (suc zero))))
                     (ap1 (Kcode Lstar)
                           (ap1 (outKdef Lstar) (var (suc (suc zero))))))
                (eqF (ap1 thmT (cgFun (var (suc (suc zero))))) codeFalse)))
cgFalseImpAtVar0 =
  ruleInst (suc (suc zero)) (var zero) cgFalseImpAtVar2
