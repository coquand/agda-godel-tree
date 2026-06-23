{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DescSndImp -- the IMP-FORM (Carneiro) value bound:
--   argValueBound_imp : imp (neg (p = O)) (leq (pArg p) (pred p)) .
--
-- Rather than thread  ne  through the whole DescSnd arithmetic cascade, we
-- transport the BARE bound at the manifest successor  s (pred p)  (where its
-- nonzero hypothesis is bare) back along  p = s (pred p)  (succForm, imp-form).
-- A single sub-congruence on both arguments, two impCong steps + impLift.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DescSndImp where

open import T4.Base

open import T4.DerCodeS using ( pArg )
open import T4.WfRedExtract using ( argValueBound )
open import T4.DescSnd using ( posNeqO )

open import BRA3.Church    using ( sub ; predecessor )
open import BRA3.ChurchLeq using ( leq ; T76 )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.ChurchPredLemmas using ( L_sp )
open import BRA3.RuleInst2 using ( ruleInst2 )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongL ; impCongR ; impEqTrans ; impRuleSym )

------------------------------------------------------------------------
-- neSucc :  s q != O  (bare).

neSucc : (q : Term) -> Deriv (neg (eqF (ap1 s q) O))
neSucc q = posNeqO (ap1 s q)
  (mp (ruleInst2 0 O 1 q refl T78) (ruleInst 0 q T76))

------------------------------------------------------------------------
-- succForm_imp :  imp (c != O) (c = s (pred c)) .

succForm_imp : (c : Term) ->
  Deriv (imp (neg (eqF c O)) (eqF c (ap1 s (ap1 predecessor c))))
succForm_imp c = impRuleSym (ruleInst 0 c L_sp)

------------------------------------------------------------------------
-- argValueBound_imp :  the value bound, ne as antecedent.

argValueBound_imp : (p : Term) ->
  Deriv (imp (neg (eqF p O)) (leq (pArg p) (ap1 predecessor p)))
argValueBound_imp p =
  let sp : Term
      sp = ap1 s (ap1 predecessor p)               -- s (pred p)
      neS : Deriv (neg (eqF sp O))
      neS = neSucc (ap1 predecessor p)
      D : Deriv (leq (pArg sp) (ap1 predecessor sp))
      D = argValueBound sp neS
      sfi : Deriv (imp (neg (eqF p O)) (eqF p sp))
      sfi = succForm_imp p
      -- pArg p = Snd (Snd p) ; cong along p = sp (two nested Snd).
      argEq : Deriv (imp (neg (eqF p O)) (eqF (pArg p) (pArg sp)))
      argEq = impCong1 Snd (ap1 Snd p) (ap1 Snd sp)
                (impCong1 Snd p sp sfi)
      predEq : Deriv (imp (neg (eqF p O))
                 (eqF (ap1 predecessor p) (ap1 predecessor sp)))
      predEq = impCong1 predecessor p sp sfi
      stepA : Deriv (imp (neg (eqF p O))
                (eqF (ap2 sub (pArg p) (ap1 predecessor p))
                     (ap2 sub (pArg sp) (ap1 predecessor p))))
      stepA = impCongL sub (pArg p) (pArg sp) (ap1 predecessor p) argEq
      stepB : Deriv (imp (neg (eqF p O))
                (eqF (ap2 sub (pArg sp) (ap1 predecessor p))
                     (ap2 sub (pArg sp) (ap1 predecessor sp))))
      stepB = impCongR sub (ap1 predecessor p) (ap1 predecessor sp) (pArg sp) predEq
      chain : Deriv (imp (neg (eqF p O))
                (eqF (ap2 sub (pArg p) (ap1 predecessor p))
                     (ap2 sub (pArg sp) (ap1 predecessor sp))))
      chain = impEqTrans (ap2 sub (pArg p) (ap1 predecessor p))
                         (ap2 sub (pArg sp) (ap1 predecessor p))
                         (ap2 sub (pArg sp) (ap1 predecessor sp))
                stepA stepB
  in impEqTrans (ap2 sub (pArg p) (ap1 predecessor p))
                (ap2 sub (pArg sp) (ap1 predecessor sp))
                O
       chain (impLift D)
