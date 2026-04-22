{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ConBRAv2 -- BRA-layer consistency sentence (Option G version).
--
-- Re-exports Guard.ConBRA's  conBRAEqn  and  ConBRA  definitions
-- (they are already BRA-compatible — Guard.ConBRA doesn't use the
-- Provable data type; it lives purely at Term / Formula / thmT).
--
-- This module exists to provide a "BRA-named" entry point mirroring
-- the Option G port plan (Guard.ConBRA → Guard.ConBRAv2) without
-- renaming the underlying equation.  Downstream BRA-layer users
-- (Guard.GodelIIBRAv2 etc.) can open either module interchangeably.
--
-- No postulates, no holes.

module Guard.ConBRAv2 where

open import Guard.ConBRA public
  using (conBRAEqn ; ConBRA ; conBRAEqnAt ; conBRAEqnSubstZero)
