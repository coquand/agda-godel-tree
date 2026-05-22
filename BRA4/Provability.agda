{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Provability -- the abstract contract a "provability functor"
--  prov : Fun1  must satisfy for Goedel I/II to go through, in
-- BRA4's Pair-encoding.
--
-- The intended semantics is:  prov  is a BRA-primitive  Fun1
-- (built from  thmT  + a "witness-existence" wrapper) such that
--
--   ap1 prov (natCode (codeFormulaNat P)) = natCode 1   iff   Deriv P .
--
-- We axiomatise only the "left-to-right" direction (the HBL-1
-- internalisation contract  provInternalize ): if BRA proves P, then
-- BRA proves  prov(natCode codeP) = 1 .  This is what Goedel I needs.
--
-- ProvContract is a record; the concrete  prov : Fun1  built downstream
-- (eventually from  thmT  + bounded-witness search) will produce a
-- value of this record.  Goedel I / II consumers take a
--  ProvContract prov  parameter and use  provInternalize  exclusively;
-- they do NOT unfold  prov 's definition.

module BRA4.Provability where

open import BRA4.Base
open import BRA4.Code
open import BRA4.NatBridge

------------------------------------------------------------------------
-- The atomic formula  prov(t) = natCode 1 .

provFormula : Fun1 -> Term -> Formula
provFormula prov t = eqF (ap1 prov t) (natCode 1)

------------------------------------------------------------------------
-- ProvContract -- HBL-1 internalisation.

record ProvContract (prov : Fun1) : Set where
  field
    provInternalize :
      (P : Formula) ->
      Deriv P ->
      Deriv (provFormula prov (natCode (codeFormulaNat P)))
