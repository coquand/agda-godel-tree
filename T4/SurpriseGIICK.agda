{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIICK -- the surprise-Goedel-II conclusion on the clos-faithful
-- CK-atom path :  feed  stageStepCK  ( S(r) -> S(r+1) ) into the shipped
-- external induction  surpriseG2F  ( base S(0) + iterate to S(N+1), where the
-- conjunction collapses to trueF ), landing  Deriv (0 = 1) .
--
-- RESIDUALS = exactly clos's "we write K(x0,..) as Kr x0 = O" ( the CK identity
-- both directions ) + coverBridge + checkFires + ConOpenInt + Lt M N .

open import T4.Base
open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )

module T4.SurpriseGIICK
  (Lstar_meta : Nat)
  (consts     : SurpriseConstsConj)
  (Kr         : Nat -> (Nat -> Nat) -> Fun1)
  where

open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.SurpriseG2.SurpriseG2FinalFormula using ( surpriseG2F )
open import T4.CheckAlphN using ( checkAlphN )
open import T4.ProgEnc    using ( enc )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )

open import T4.StageStepCK Lstar_meta consts Kr
  using ( stageStepCK ; charAtom ; Krest ; KBCf ; KA ; N ; M )

module _
  (ltMN       : Lt M N)
  (checkFires : Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)))
  (con        : ConOpenInt)
  (bridgeBwd  : (r : Nat) (picks : Picks) -> Deriv (imp (charAtom r picks) (Krest r picks)))
  (bridgeFwd  : (r : Nat) (picks : Picks) -> Deriv (imp (Krest r picks) (charAtom r picks)))
  (dCB        : (r : Nat) (picks : Picks) -> Deriv (imp (KBCf r) (KA r)))
  where

  surpriseGIICK : Deriv (eqF O (ap1 s O))
  surpriseGIICK =
    surpriseG2F consts ltMN
      (stageStepCK checkFires con bridgeBwd bridgeFwd dCB)
