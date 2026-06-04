{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RightPartInvariant -- the "right part unchanged" lemma of clos Step 2 :
-- the num-installation  x0 |-> num x0  ( substF 0 (num (var 0)) ) does NOT
-- change the consequent  KdefBigConjF enum (var 1) M (natCode r)  of the
-- monoShift output, because that formula has NO  var 0  free ( its fuel is
-- var 1 , its programs the closed  enum k , its subject the closed natCode r ).
--
--   rightInv M r : Eq (substF zero (ap1 num (var zero))
--                         (KdefBigConjF enum (var (suc zero)) M (natCode r)))
--                     (KdefBigConjF enum (var (suc zero)) M (natCode r))
--
-- A clean induction on M ( each  perProgNegF  mentions only  var 1 ), mirroring
-- T4.KdefBigConjFuelBridge.distKBC 's structure but landing on the IDENTITY.
-- This is what lets  ruleInst 0 (num (var 0))  on the  monoShift output act
-- ONLY on  K_rest  ( clos's "replace x0 by num x0", var-0-safe ).

module T4.RightPartInvariant where

open import T4.Base
open import T4.Num  using ( num )
open import T4.Kdef using ( runProg )
open import T4.SubstNoVar using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF )

module _ (enum : Fun1) where

  S0 : Term
  S0 = ap1 num (var zero)         -- = num x0

  ----------------------------------------------------------------------
  -- Per-conjunct :  substF 0 S0  fixes  perProgNegF  ( fuel var 1 , closed
  --   enum k / natCode r ;  var 0  does not occur ).

  perProgInv :
    (r k : Nat) ->
    Eq (substF zero S0 (perProgNegF enum (var (suc zero)) (natCode r) k))
       (perProgNegF enum (var (suc zero)) (natCode r) k)
  perProgInv r k =
    eqTrans
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum z) (var (suc zero)))
                              (ap1 s (substT zero S0 (natCode r)))))
              (substT_NoVar zero S0 (natCode k) (NoVar_natCode k)))
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum (natCode k)) (var (suc zero)))
                              (ap1 s z)))
              (substT_NoVar zero S0 (natCode r) (NoVar_natCode r)))

  ----------------------------------------------------------------------
  -- The whole consequent is invariant.

  rightInv :
    (M r : Nat) ->
    Eq (substF zero S0 (KdefBigConjF enum (var (suc zero)) M (natCode r)))
       (KdefBigConjF enum (var (suc zero)) M (natCode r))
  rightInv zero    r = perProgInv r zero
  rightInv (suc M) r =
    eqTrans
      (eqCong (\ H -> neg (imp H
                            (neg (substF zero S0 (KdefBigConjF enum (var (suc zero)) M (natCode r))))))
              (perProgInv r (suc M)))
      (eqCong (\ T -> neg (imp (perProgNegF enum (var (suc zero)) (natCode r) (suc M)) (neg T)))
              (rightInv M r))
