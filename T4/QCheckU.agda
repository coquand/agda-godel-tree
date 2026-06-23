{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.QCheckU -- the OBJECT reflection of the BUNDLED CR predicate on the unsized
-- coding into a single Fun1  qcheckU , exactly as T4.QCheck does for validity
-- alone, but with the conjunctive body
--
--   conj3 x = sigma (wfRed (triF x))
--                   (sigma (eqDecO (srcF (triF x)) (tgtF x))
--                          (eqDecO (tgtF (triF x)) (devF (srcF x))))
--
-- so  conj3 x = O  iff (validity preserved AND src endpoint AND tgt endpoint).
-- Then  Q x := imp (wfRed x = O) (conj3 x = O)  and
--
--   qcheckU_sound    : imp (qcheckU x = O) Q x
--   qcheckU_complete : imp (Q x) (qcheckU x = O)
--
-- (The dispatch proves  Q x  -- i.e. conj3 x = O under validity -- per tag.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.QCheckU where

open import T4.Base

open import T4.WfRed using ( wfRed )
open import T4.DerTri using ( triF )
open import T4.DerSrc using ( srcF )
open import T4.DerTgt using ( tgtF )
open import T4.DerDev using ( devF )
open import T4.EqDecO using ( eqDecO )

open import BRA3.Church          using ( pi ; sigma ; isZero ; predecessor )
open import BRA3.SubT.NatEq      using ( natEqF )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.PairAlgebra     using ( compose1U ; compose1U_eq )
open import BRA3.Dispatch        using
  ( condFork ; condFork_false ; condFork_true_nc
  ; T116_at_terms ; T117_at_terms ; closed_O )

open import BRA3.Logic           using ( eqSymImp ; impTrans )
open import BRA3.Contrapositive  using ( compI ; liftP ; bComb ; bCombTwo ; identP )
open import BRA3.ChurchCM        using ( caseElim )
open import T4.Thm12.ImpHelpers  using ( impEqTrans ; impLift ; impRuleSym )

------------------------------------------------------------------------
-- SECTION 1.  The conjunctive body  conj3 : Fun1  and the carrier  qcheckU .

srcEqF : Fun1                       -- eqDecO (srcF (triF x)) (tgtF x)
srcEqF = compose1U isZero (C natEqF (compose1U srcF triF) tgtF)

tgtEqF : Fun1                       -- eqDecO (tgtF (triF x)) (devF (srcF x))
tgtEqF = compose1U isZero (C natEqF (compose1U tgtF triF) (compose1U devF srcF))

conj3 : Fun1
conj3 = C sigma (compose1U wfRed triF) (C sigma srcEqF tgtEqF)

private
  zFun : Fun1
  zFun = C pi Z conj3

qcheckU : Fun1
qcheckU = C condFork zFun wfRed

------------------------------------------------------------------------
-- SECTION 2.  Unfolding and the Snd-branch equation.

private
  trans2 : (P Q : Formula) (a b c : Term) ->
           Deriv (imp P (imp Q (eqF a b))) ->
           Deriv (imp P (imp Q (eqF b c))) ->
           Deriv (imp P (imp Q (eqF a c)))
  trans2 P Q a b c f g =
    let fflip : Deriv (imp P (imp Q (eqF b a)))
        fflip = bCombTwo (liftP P (liftP Q (eqSymImp a b))) f
        lifted : Deriv (imp P (imp Q (imp (eqF b c) (eqF a c))))
        lifted = bCombTwo (liftP P (liftP Q (ax_eqTrans b a c))) fflip
    in bCombTwo lifted g

qcheckU_unfold : (x : Term) ->
  Deriv (eqF (ap1 qcheckU x)
             (ap2 condFork (ap2 pi O (ap1 conj3 x)) (ap1 wfRed x)))
qcheckU_unfold x =
  let W : Term
      W = ap1 conj3 x
      zEq : Deriv (eqF (ap1 zFun x) (ap2 pi O W))
      zEq = ruleTrans (ax_C pi Z conj3 x)
              (congL pi (ap1 conj3 x) (axZ x))
      cEq : Deriv (eqF (ap1 qcheckU x)
                       (ap2 condFork (ap1 zFun x) (ap1 wfRed x)))
      cEq = ax_C condFork zFun wfRed x
  in ruleTrans cEq (congL condFork (ap1 wfRed x) zEq)

private
  qWhenVO : (x : Term) ->
    Deriv (imp (eqF (ap1 wfRed x) O)
               (eqF (ap1 qcheckU x) (ap1 conj3 x)))
  qWhenVO x =
    let V : Term
        V = ap1 wfRed x
        W : Term
        W = ap1 conj3 x
        Z2 : Term
        Z2 = ap2 pi O W
        sndChain : Deriv (eqF (ap2 condFork Z2 O) W)
        sndChain = ruleTrans (condFork_false Z2) (T116_at_terms O W closed_O)
        rest : Deriv (imp (eqF V O) (eqF (ap2 condFork Z2 V) W))
        rest = impEqTrans (ap2 condFork Z2 V) (ap2 condFork Z2 O) W
                 (ax_eqCongR condFork V O Z2)
                 (impLift sndChain)
    in impEqTrans (ap1 qcheckU x) (ap2 condFork Z2 V) W
         (impLift (qcheckU_unfold x)) rest

------------------------------------------------------------------------
-- SECTION 3.  Soundness:  qcheckU x = O  =>  Q x .

qcheckU_sound : (x : Term) ->
  Deriv (imp (eqF (ap1 qcheckU x) O)
             (imp (eqF (ap1 wfRed x) O)
                  (eqF (ap1 conj3 x) O)))
qcheckU_sound x =
  let V : Term
      V = ap1 wfRed x
      W : Term
      W = ap1 conj3 x
      Hq : Formula
      Hq = eqF (ap1 qcheckU x) O
      Hv : Formula
      Hv = eqF V O
      fWQ : Deriv (imp Hq (imp Hv (eqF W (ap1 qcheckU x))))
      fWQ = liftP Hq (impRuleSym (qWhenVO x))
      fQO : Deriv (imp Hq (imp Hv (eqF (ap1 qcheckU x) O)))
      fQO = axK Hq Hv
  in trans2 Hq Hv W (ap1 qcheckU x) O fWQ fQO

------------------------------------------------------------------------
-- SECTION 4.  Completeness:  Q x  =>  qcheckU x = O .

qcheckU_complete : (x : Term) ->
  Deriv (imp (imp (eqF (ap1 wfRed x) O)
                  (eqF (ap1 conj3 x) O))
             (eqF (ap1 qcheckU x) O))
qcheckU_complete x =
  let V : Term
      V = ap1 wfRed x
      W : Term
      W = ap1 conj3 x
      Z2 : Term
      Z2 = ap2 pi O W
      Hv : Formula
      Hv = eqF V O
      Qx : Formula
      Qx = imp Hv (eqF W O)
      Rf : Formula
      Rf = imp Qx (eqF (ap1 qcheckU x) O)

      X_R : Deriv (imp Hv Rf)
      X_R =
        let qEqX : Deriv (imp Hv (imp Qx (eqF (ap1 qcheckU x) W)))
            qEqX = bComb (liftP Hv (axK (eqF (ap1 qcheckU x) W) Qx)) (qWhenVO x)
            gQx : Deriv (imp Hv (imp Qx Qx))
            gQx = liftP Hv (identP Qx)
            gHv : Deriv (imp Hv (imp Qx Hv))
            gHv = axK Hv Qx
            wO : Deriv (imp Hv (imp Qx (eqF W O)))
            wO = bCombTwo gQx gHv
        in trans2 Hv Qx (ap1 qcheckU x) W O qEqX wO

      Y_R : Deriv (imp (neg Hv) Rf)
      Y_R =
        let nHv : Formula
            nHv = neg Hv
            spV : Deriv (imp nHv (eqF V (ap1 s (ap1 predecessor V))))
            spV = impRuleSym (ruleInst 0 V L_sp)
            fstChain : Deriv (eqF (ap2 condFork Z2 (ap1 s (ap1 predecessor V))) O)
            fstChain = ruleTrans (condFork_true_nc Z2 (ap1 predecessor V))
                                 (T117_at_terms O W closed_O)
            congStep : Deriv (imp nHv
                        (eqF (ap2 condFork Z2 V)
                             (ap2 condFork Z2 (ap1 s (ap1 predecessor V)))))
            congStep = compI spV
                         (ax_eqCongR condFork V (ap1 s (ap1 predecessor V)) Z2)
            rest : Deriv (imp nHv (eqF (ap2 condFork Z2 V) O))
            rest = impEqTrans (ap2 condFork Z2 V)
                     (ap2 condFork Z2 (ap1 s (ap1 predecessor V))) O
                     congStep (impLift fstChain)
            qO : Deriv (imp nHv (eqF (ap1 qcheckU x) O))
            qO = impEqTrans (ap1 qcheckU x) (ap2 condFork Z2 V) O
                   (impLift (qcheckU_unfold x)) rest
        in bComb (liftP nHv (axK (eqF (ap1 qcheckU x) O) Qx)) qO
  in caseElim {X = Hv} {Y = neg Hv} {Rf = Rf}
       (identP (neg Hv)) X_R Y_R
