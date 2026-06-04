{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StageStepCK -- the inductive step  S(r) -> S(r+1)  ASSEMBLED on the
-- clos-faithful CK-atom path :  for each fixed tail  p(r+1),..,pN  ( = picks )
-- we derive  not (Kr x0 = O)  ( = imp (Kr x0=O) falseF ), convert it to
-- not K_rest  by the CK identity, and  stageStepF  ( shipped ) wraps the
-- meta-induction ( decLeN dispatch, impFalseToNeg, r>N trueF-collapse ).
--
--   stageStepCK : StageStepSpecF consts  =  (r) -> S(r) -> S(suc r) .
--
-- RESIDUALS ( = clos's "we write K(x0,..) as Kr x0 = O", supplied per (r,picks) ) :
--   * Kr        : the antecedent characteristic ( a  Fun1 , per (r,picks) ) ;
--   * bridgeBwd : imp (Kr x0=O) K_rest     -- feeds the encode antecedent ;
--   * bridgeFwd : imp K_rest (Kr x0=O)     -- converts  not(Kr x0=O)  to  not K_rest ;
--   * dCB       : imp Q(x1) KdefAlph(r)    -- coverBridge ( "by enum correctness" ) ;
--   * checkFires, con (= ConOpenInt) .
-- ALL of Steps 1-6 ( frontEnd, monoShift, encode+sub, encoded_mp, ONE thm13 on Kr,
-- coverBridge-internalise, abstract Chaitin-GI, ConOpenInt ) are BUILT and composed.

open import T4.Base

open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )

module T4.StageStepCK
  (Lstar_meta : Nat)
  (consts     : SurpriseConstsConj)
  (Kr         : Nat -> (Nat -> Nat) -> Fun1)
  where

open import T4.Tags  using ( tag_mp )
open import T4.Code  using ( falseF )

open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; StageStepSpecF ; Picks ; PicksBound )
open import T4.KdefBigConjFuelBridge       using ( KdefBigConjF )
open import T4.KdefAlph Lstar_meta         using ( KdefAlph )

open import T4.CheckAlphN using ( checkAlphN )
open import T4.ProgEnc    using ( enc )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )

open import BRA3.RuleInst2      using ( NatLe )
open import BRA3.Contrapositive using ( compI )

import T4.ThmT
import T4.Code
import T4.EncodeStepCK
import T4.ChaitinStepCK
import T4.SurpriseG2.StageStepF

------------------------------------------------------------------------
-- The day- r , tail- picks  formulas.

N : Nat
N = SurpriseConstsConj.N consts
enum : Fun1
enum = SurpriseConstsConj.enum consts
M : Nat
M = SurpriseConstsConj.M consts

charAtom : (r : Nat) (picks : Picks) -> Formula
charAtom r picks = eqF (ap1 (Kr r picks) (var zero)) O

Krest : (r : Nat) (picks : Picks) -> Formula
Krest r picks = BigConjFormula consts (suc r) picks

KBCf : (r : Nat) -> Formula
KBCf r = KdefBigConjF enum (var (suc zero)) M (natCode r)

KA : (r : Nat) -> Formula
KA r = KdefAlph (natCode r)

------------------------------------------------------------------------
-- The CK-identity + coverBridge residuals, supplied per (r, picks).

module _
  (checkFires : Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)))
  (con : ConOpenInt)
  (bridgeBwd : (r : Nat) (picks : Picks) -> Deriv (imp (charAtom r picks) (Krest r picks)))
  (bridgeFwd : (r : Nat) (picks : Picks) -> Deriv (imp (Krest r picks) (charAtom r picks)))
  (dCB       : (r : Nat) (picks : Picks) -> Deriv (imp (KBCf r) (KA r)))
  where

  ------------------------------------------------------------------------
  -- The CK-shaped day clash :  S(r)  =>  not K_rest  ( for r <= N ).

  dayClashCK :
    (r : Nat) -> NatLe r N -> StagePredF consts r ->
    (picks : Picks) -> PicksBound consts picks ->
    Deriv (imp (Krest r picks) falseF)
  dayClashCK r rleN IH picks bound =
    let -- Steps 1-4 :  under (Kr x0=O), T proves Q(x1)  ( = step3CK ).
        prov3 : Deriv (imp (charAtom r picks)
                           (eqF (ap1 T4.ThmT.thmT
                                      (ap2 Pair (natCode tag_mp)
                                        (ap2 Pair
                                          (T4.EncodeStepCK.wrapped consts r rleN (Kr r picks)
                                             picks bound (bridgeBwd r picks) IH)
                                          (T4.EncodeStepCK.w2CK consts r rleN (Kr r picks)
                                             picks bound))))
                                (T4.Code.codeFormula (KBCf r))))
        prov3 = T4.EncodeStepCK.step3CK consts r rleN (Kr r picks)
                  picks bound (bridgeBwd r picks) IH

        W3 : Term
        W3 = ap2 Pair (natCode tag_mp)
               (ap2 Pair
                 (T4.EncodeStepCK.wrapped consts r rleN (Kr r picks)
                    picks bound (bridgeBwd r picks) IH)
                 (T4.EncodeStepCK.w2CK consts r rleN (Kr r picks) picks bound))

        -- Steps 5-6 :  not (Kr x0=O)  ( coverBridge + Chaitin-GI + ConOpenInt ).
        falseImp : Deriv (imp (charAtom r picks) falseF)
        falseImp = T4.ChaitinStepCK.clashFalseCK Lstar_meta consts (charAtom r picks) r
                     checkFires (dCB r picks) W3 prov3 con

        -- convert  not (Kr x0=O)  to  not K_rest  via the CK identity.
    in compI (bridgeFwd r picks) falseImp

  ------------------------------------------------------------------------
  -- S(r) -> S(r+1) :  wrap the meta-induction ( shipped  stageStepF ).

  stageStepCK : StageStepSpecF consts
  stageStepCK = T4.SurpriseG2.StageStepF.stageStepF consts dayClashCK
