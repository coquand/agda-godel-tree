{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinGodelIStatement -- the STATEMENT (only) of Chaitin's
-- incompleteness theorem as phrased in surprise.pdf, p.2:
--
--   "Chaitin's incompleteness theorem states that for any rich enough
--    consistent mathematical theory, there exists a (large enough) integer L
--    ... such that, for any integer x, the statement  K(x) > L  cannot be
--    proved within the theory."
--
-- The theory T is fixed (its derivability is  Deriv , its internal proof
-- checker is  thmT ).  The pieces are exactly the ones already built:
--   * consistency of T                = Deriv ConSchema        (T4.ConInj)
--   * the formula  K(x) > L           = Kgt (natCode L) (natCode x)  (T4.KFormula)
--       Kgt L x = ~~( |e| <= L  ->  ~( machine(e) outputs x ) ) , with the
--       description  e (var 0)  and fuel (var 1) FREE -- i.e. universally
--       quantified -- so it is literally "no program of size <= L outputs x".
--   * "T proves phi"                  = Deriv phi              (BRA3.Deriv)
--
-- This is the STATEMENT, not a proof.  (What is proved so far is the reductio
-- CORE -- T4.KGodel1Canon.chaitin_G1_canonical -- conditional on the search
-- firing + interpreter correctness; closing those, via thmT-completeness, is
-- what turns this Set into a theorem.)

module T4.ChaitinGodelIStatement where

open import T4.Base
open import T4.ConInj   using ( ConSchema )
open import T4.KFormula using ( Kgt )
open import T4.NatExp   using ( Sg )

------------------------------------------------------------------------
-- Negation (P -> Empty); Empty comes from BRA3.Base via T4.Base.

Not : Set -> Set
Not P = P -> Empty

------------------------------------------------------------------------
-- "T proves the formula phi" = phi is derivable in T.
--   (Kgt has free var 0 / var 1, so its derivability is "for all e, n",
--    i.e. genuine  K(x) > L .)

Provable : Formula -> Set
Provable phi = Deriv phi

------------------------------------------------------------------------
-- Chaitin-Goedel-I (surprise.pdf p.2).

ChaitinGodelI : Set
ChaitinGodelI =
  Deriv ConSchema ->                                   -- T consistent
  Sg Nat (\ L ->                                       -- exists integer L
    (x : Nat) ->                                       -- for every integer x
    Not (Provable (Kgt (natCode L) (natCode x))))      -- K(x) > L unprovable
