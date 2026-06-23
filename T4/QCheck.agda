{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.QCheck -- the OBJECT reflection of the triangle-preservation predicate
--
--   Q x  :=  imp (wfRedSized x = O) (wfRedSized (triFSized x) = O)
--
-- into a single Fun1  qcheck  with
--
--   qcheck x  =  condFork (pi O (wfRedSized (triFSized x))) (wfRedSized x)
--
-- so that  qcheck x = O  is an equation EQUIVALENT to  Q x :
--
--   qcheck_sound    : imp (qcheck x = O) Q x              ( =>  )
--   qcheck_complete : imp (Q x) (qcheck x = O)            ( <=  )
--
-- The condFork dispatch:  if  wfRedSized x = O  then the result is the
-- Snd branch  wfRedSized (triFSized x) ; otherwise it is the Fst branch  O .
-- So  qcheck x = O  iff  ( wfRedSized x = O  =>  wfRedSized(triFSized x) = O ) .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.QCheck where

open import T4.Base

open import T4.WfRedSized using ( wfRedSized )
open import T4.DerTriS    using ( triFSized )

open import BRA3.Church          using ( pi ; predecessor )
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
-- SECTION 1.  The carrier  qcheck : Fun1 .

private
  -- zFun x = pi (Z x) (compose1U wfRedSized triFSized x) = pi O (W x)
  zFun : Fun1
  zFun = C pi Z (compose1U wfRedSized triFSized)

qcheck : Fun1
qcheck = C condFork zFun wfRedSized

------------------------------------------------------------------------
-- Shorthands and the unfolding equation.

private
  -- depth-2 equational transitivity in context [P,Q].
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

qcheck_unfold : (x : Term) ->
  Deriv (eqF (ap1 qcheck x)
             (ap2 condFork (ap2 pi O (ap1 wfRedSized (ap1 triFSized x)))
                           (ap1 wfRedSized x)))
qcheck_unfold x =
  let W : Term
      W = ap1 wfRedSized (ap1 triFSized x)
      zEq : Deriv (eqF (ap1 zFun x) (ap2 pi O W))
      zEq = ruleTrans (ax_C pi Z (compose1U wfRedSized triFSized) x)
              (ruleTrans (congL pi (ap1 (compose1U wfRedSized triFSized) x) (axZ x))
                         (congR pi O (compose1U_eq wfRedSized triFSized x)))
      cEq : Deriv (eqF (ap1 qcheck x)
                       (ap2 condFork (ap1 zFun x) (ap1 wfRedSized x)))
      cEq = ax_C condFork zFun wfRedSized x
  in ruleTrans cEq (congL condFork (ap1 wfRedSized x) zEq)

------------------------------------------------------------------------
-- SECTION 2.  qcheck x = W x  whenever  wfRedSized x = O  (the Snd branch).

private
  qWhenVO : (x : Term) ->
    Deriv (imp (eqF (ap1 wfRedSized x) O)
               (eqF (ap1 qcheck x)
                    (ap1 wfRedSized (ap1 triFSized x))))
  qWhenVO x =
    let V : Term
        V = ap1 wfRedSized x
        W : Term
        W = ap1 wfRedSized (ap1 triFSized x)
        Z2 : Term
        Z2 = ap2 pi O W
        sndChain : Deriv (eqF (ap2 condFork Z2 O) W)
        sndChain = ruleTrans (condFork_false Z2) (T116_at_terms O W closed_O)
        rest : Deriv (imp (eqF V O) (eqF (ap2 condFork Z2 V) W))
        rest = impEqTrans (ap2 condFork Z2 V) (ap2 condFork Z2 O) W
                 (ax_eqCongR condFork V O Z2)
                 (impLift sndChain)
    in impEqTrans (ap1 qcheck x) (ap2 condFork Z2 V) W
         (impLift (qcheck_unfold x)) rest

------------------------------------------------------------------------
-- SECTION 3.  Soundness:  qcheck x = O  =>  Q x .

qcheck_sound : (x : Term) ->
  Deriv (imp (eqF (ap1 qcheck x) O)
             (imp (eqF (ap1 wfRedSized x) O)
                  (eqF (ap1 wfRedSized (ap1 triFSized x)) O)))
qcheck_sound x =
  let V : Term
      V = ap1 wfRedSized x
      W : Term
      W = ap1 wfRedSized (ap1 triFSized x)
      Hq : Formula
      Hq = eqF (ap1 qcheck x) O
      Hv : Formula
      Hv = eqF V O
      fWQ : Deriv (imp Hq (imp Hv (eqF W (ap1 qcheck x))))
      fWQ = liftP Hq (impRuleSym (qWhenVO x))
      fQO : Deriv (imp Hq (imp Hv (eqF (ap1 qcheck x) O)))
      fQO = axK Hq Hv
  in trans2 Hq Hv W (ap1 qcheck x) O fWQ fQO

------------------------------------------------------------------------
-- SECTION 4.  Completeness:  Q x  =>  qcheck x = O .

qcheck_complete : (x : Term) ->
  Deriv (imp (imp (eqF (ap1 wfRedSized x) O)
                  (eqF (ap1 wfRedSized (ap1 triFSized x)) O))
             (eqF (ap1 qcheck x) O))
qcheck_complete x =
  let V : Term
      V = ap1 wfRedSized x
      W : Term
      W = ap1 wfRedSized (ap1 triFSized x)
      Z2 : Term
      Z2 = ap2 pi O W
      Hv : Formula
      Hv = eqF V O
      Qx : Formula
      Qx = imp Hv (eqF W O)
      Rf : Formula
      Rf = imp Qx (eqF (ap1 qcheck x) O)

      ----------------------------------------------------------------
      -- X-branch :  wfRedSized x = O  =>  qcheck x = W = O .
      X_R : Deriv (imp Hv Rf)
      X_R =
        let qEqX : Deriv (imp Hv (imp Qx (eqF (ap1 qcheck x) W)))
            qEqX = bComb (liftP Hv (axK (eqF (ap1 qcheck x) W) Qx)) (qWhenVO x)
            gQx : Deriv (imp Hv (imp Qx Qx))
            gQx = liftP Hv (identP Qx)
            gHv : Deriv (imp Hv (imp Qx Hv))
            gHv = axK Hv Qx
            wO : Deriv (imp Hv (imp Qx (eqF W O)))
            wO = bCombTwo gQx gHv
        in trans2 Hv Qx (ap1 qcheck x) W O qEqX wO

      ----------------------------------------------------------------
      -- Y-branch :  wfRedSized x /= O  =>  qcheck x = Fst (pi O W) = O .
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
            qO : Deriv (imp nHv (eqF (ap1 qcheck x) O))
            qO = impEqTrans (ap1 qcheck x) (ap2 condFork Z2 V) O
                   (impLift (qcheck_unfold x)) rest
        in bComb (liftP nHv (axK (eqF (ap1 qcheck x) O) Qx)) qO
  in caseElim {X = Hv} {Y = neg Hv} {Rf = Rf}
       (identP (neg Hv)) X_R Y_R
