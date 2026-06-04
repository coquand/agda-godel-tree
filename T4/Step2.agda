{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step2 -- clos Step 2 ( encode + x0 |-> num x0 ), GENERIC in an abstract
-- consts ( so the concrete enumerator is never unfolded ).
--
--   step2 : Deriv (eqF (ap1 thmT wrapped)
--                      (cImp (sbf spec0 (codeFormula K_rest))    -- LEFT : num-installed
--                            (codeFormula Q)))                   -- RIGHT : UNCHANGED
--
-- where  wrapped = pi tag_sb (pi spec0 w) ,  w = encode (monoShift ...)  ( CLOSED,
-- T4.EncodeClosed ),  spec0 = Pair (natCode 0) (num (var 0)) ,  Q = KdefBigConjF
-- ( fuel var 1 ).   The RIGHT part is fixed by  T4.Step2bInvariant.rightSbfInv
-- ( Q has no  var 0 ); the LEFT is the num-installed  K_rest -code, the antecedent
-- the downstream  encoded_mp  peels against the  picks  Sigma_1 run-data.

module T4.Step2 where

open import T4.Base
open import T4.Tags using ( tag_sb )
open import T4.Num  using ( num )
open import T4.Code using ( codeFormula )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.Encode using ( encode )
open import T4.EncodeClosed using ( closed_encode )
open import T4.SbF using ( sbf )
open import T4.SbStep using ( sbf_step_imp )
open import T4.DefWit using ( cImp )
open import T4.Step2bInvariant using ( rightSbfInv )
open import T4.MonoShift using ( monoShift )
open import BRA3.Dispatch using ( Closed )
open import BRA3.Church using ( pi )

open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.KdefBigConjFuelBridge using ( KdefBigConjF )

-- Deriv reflexivity ( a = a , via  u(a) = a  both ways ).
eqRefl : (a : Term) -> Deriv (eqF a a)
eqRefl a = ruleTrans (ruleSym (ax_u a)) (ax_u a)

module _ (consts : SurpriseConstsConj) (r : Nat) (picks : Picks)
  (dComp : Deriv (imp (BigConjFormula consts (suc r) picks)
                      (KdefBigConj (SurpriseConstsConj.M consts)
                                   (SurpriseConstsConj.enum consts) (natCode r))))
  where

  enum : Fun1
  enum = SurpriseConstsConj.enum consts
  M : Nat
  M = SurpriseConstsConj.M consts

  Krest : Formula
  Krest = BigConjFormula consts (suc r) picks
  Qf : Formula
  Qf = KdefBigConjF enum (var (suc zero)) M (natCode r)

  dPhi : Deriv (imp Krest Qf)
  dPhi = monoShift consts r picks dComp

  -- the CLOSED proof code.
  w : Term
  w = encode dPhi
  w_closed : Closed w
  w_closed = closed_encode dPhi

  S0 : Term
  S0 = ap1 num (var zero)
  spec0 : Term
  spec0 = ap2 Pair (natCode zero) S0
  wrapped : Term
  wrapped = ap2 pi (natCode tag_sb) (ap2 pi spec0 w)

  Kc : Term
  Kc = codeFormula Krest
  Qc : Term
  Qc = codeFormula Qf

  step2a : Deriv (eqF (ap1 thmT w) (codeFormula (imp Krest Qf)))
  step2a = thmT_complete_rec dPhi

  -- thmT wrapped = cImp (sbf spec0 Kc) Qc   ( RIGHT part Qc unchanged ).
  step2 : Deriv (eqF (ap1 thmT wrapped) (cImp (ap2 sbf spec0 Kc) Qc))
  step2 =
    ruleTrans (thmT_at_sb spec0 w)
      (ruleTrans (congR sbf spec0 step2a)
        (sbf_step_imp zero S0 Kc Qc (ap2 sbf spec0 Kc) Qc
          (eqRefl (ap2 sbf spec0 Kc)) (rightSbfInv enum S0 M r)))
