{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step2Encode -- clos Step 2a : encode the  monoShift  output to a CLOSED
-- proof code  w  with  thmT w = code(P(x0) => Q(x1)) .   Kept GENERIC in an
-- ABSTRACT  consts  ( a module parameter ) so the concrete enumerator
-- ( T4.EnumProg.enum ) is NEVER unfolded -- instantiating at the concrete
-- CKMargin consts here blows up normalisation ( the enumerator is a large
-- program ); the concrete consts is supplied only at the very end.

module T4.Step2Encode where

open import T4.Base
open import T4.Code   using ( codeFormula )
open import T4.ThmT   using ( thmT )
open import T4.Encode using ( encode )
open import T4.EncodeClosed using ( closed_encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import BRA3.Dispatch using ( Closed )

open import T4.MonoShift using ( monoShift )
open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.KdefBigConjFuelBridge using ( KdefBigConjF )

module _ (consts : SurpriseConstsConj) (r : Nat) (picks : Picks)
  (dComp : Deriv (imp (BigConjFormula consts (suc r) picks)
                      (KdefBigConj (SurpriseConstsConj.M consts)
                                   (SurpriseConstsConj.enum consts) (natCode r))))
  where

  dPhi : Deriv (imp (BigConjFormula consts (suc r) picks)
                    (KdefBigConjF (SurpriseConstsConj.enum consts) (var (suc zero))
                                  (SurpriseConstsConj.M consts) (natCode r)))
  dPhi = monoShift consts r picks dComp

  -- the CLOSED proof code ( closedness from T4.EncodeClosed, no hypothesis ).
  w : Term
  w = encode dPhi

  w_closed : Closed w
  w_closed = closed_encode dPhi

  -- thmT w = code(P(x0) => Q(x1))  ( completeness of thmT ).
  step2a :
    Deriv (eqF (ap1 thmT w)
               (codeFormula (imp (BigConjFormula consts (suc r) picks)
                                 (KdefBigConjF (SurpriseConstsConj.enum consts) (var (suc zero))
                                               (SurpriseConstsConj.M consts) (natCode r)))))
  step2a = thmT_complete_rec dPhi
