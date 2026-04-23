{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm14TPrime -- the encoded axiom  t'  for Guard's Theorem 14.
--
-- guard15 p.17:  t'  is a numeral such that
--     th(t') = "x0 = x1 ⊃ x0 /= x1 ⊃ 0 = 1" .
-- In our system:
--     tPrimeFormula = (var 0 = var 1) ⊃ ((~ (var 0 = var 1)) ⊃ botEq).
--
-- The encoded Term uses the  encAxExFalso  tag (n35) from
-- Guard.ProofEncFormula; the DerivF witness  tPrimeDeriv  is a direct
-- instance of  axExFalso  (Guard.DerivF).  Correctness is definitional.
--
-- Variable choice: Guard's  x0 ↔ var 0 ,  x1 ↔ var 1 .  The chain's
-- active variables  var 0  (proof slot) and  var 1  (diagonalized)
-- clash with these; but  t'  is always ruleInst'd away to the
-- relevant chain Terms before composition, so the naming is harmless.

module Guard.Thm14TPrime where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ProofEncFormula using (encAxExFalso ; encAxExFalsoCorr)
open import Guard.ThFunTForHF using (thmT)

------------------------------------------------------------------------
-- Free variable indices used by  t' .

private
  v0 : Nat ; v0 = zero
  v1 : Nat ; v1 = suc zero

  v0C : Term ; v0C = reify (code (var v0))
  v1C : Term ; v1C = reify (code (var v1))

------------------------------------------------------------------------
-- Atomic equation "x0 = x1" and its code.

Peq : Formula
Peq = atomic (eqn (var v0) (var v1))

PeqC : Term
PeqC = reify (codeFormula Peq)

------------------------------------------------------------------------
-- botEq = "0 = 1" and its code.

botEq : Formula
botEq = atomic (eqn O (ap2 Pair O O))

botEqC : Term
botEqC = reify (codeFormula botEq)

------------------------------------------------------------------------
-- Target formula of  t' .

tPrimeFormula : Formula
tPrimeFormula = Peq imp ((not Peq) imp botEq)

------------------------------------------------------------------------
-- The encoded Term  t' .

tPrime : Term
tPrime = encAxExFalso PeqC botEqC

------------------------------------------------------------------------
-- DerivF-level witness.

tPrimeDeriv : Deriv tPrimeFormula
tPrimeDeriv = axExFalso Peq botEq

------------------------------------------------------------------------
-- Correctness of the encoded proof: thmT(t') unfolds to the Gödel-code
-- of  tPrimeFormula .  Direct from  encAxExFalsoCorr  by the usual
-- reify/codeFormula reduction.

tPrimeCorr : Deriv (atomic (eqn (ap1 thmT tPrime) (reify (codeFormula tPrimeFormula))))
tPrimeCorr = encAxExFalsoCorr PeqC botEqC
