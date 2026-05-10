{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.NatMax -- the binary max function on natural numbers,
-- factored out so modules that need it without depending on
-- BRA2.DerivTBounded can import directly.
--
-- DerivTBounded uses natMax in its rank/level combiners (mp,
-- ruleTrans, indBT, etc.), and we want to enrich indBTB to take
-- a WellFormedIndBT side condition.  WellFormedIndBT in turn
-- transitively needs natMax (through SubstCompose -> NatMaxLemmas);
-- factoring natMax here breaks the import cycle that would
-- otherwise force WellFormedIndBT to be inlined inside
-- DerivTBounded.

module BRA2.NatMax where

open import BRA2.Base

------------------------------------------------------------------------
-- Binary max on Nat.

natMax : Nat -> Nat -> Nat
natMax zero    m       = m
natMax (suc n) zero    = suc n
natMax (suc n) (suc m) = suc (natMax n m)
