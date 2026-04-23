{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm14T -- the encoded axiom  t  for Guard's Theorem 14.
--
-- guard15 p.17:  t  is a numeral such that
--     th(t) = "x0 = x2 ⊃ x1 = x2 ⊃ x0 = x1" .
-- Our  Guard.DerivF.axEqTrans a b c  has the formula
--     (a = b) ⊃ ((a = c) ⊃ (b = c))
-- i.e. the common-pivot variable "a" is on the LEFT of both
-- hypotheses, whereas Guard's pivot  x2  is on the RIGHT.  Since these
-- are logically equivalent up to symmetry of  = , either orientation
-- can play the role of  t  in the Thm 14 chain; the only consequence
-- of using ours is that steps 1 and 2 of the chain must feed  encRuleSym
-- -wrapped proofs into the eventual modus-ponens slots.  That cost (two
-- sym applications) is well below the alternative of a ~20-step Hilbert
-- derivation of Guard's orientation from ours.
--
-- Variable correspondence with Guard's  t :
--   Guard's x0  ↔  our  var 2
--   Guard's x1  ↔  our  var 3
--   Guard's x2  ↔  our  var 4   (the common-pivot variable)
-- Indices chosen to avoid collision with the Thm 14 chain's active
-- variables ( var 0  is the proof slot,  var 1  is diagonalized).

module Guard.Thm14T where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ProofEncFormula using (encAxEqTrans ; encAxEqTransCorr)
open import Guard.ThFunTForHF using (thmT)

------------------------------------------------------------------------
-- Fresh variable indices for  t 's three free variables.

private
  v2 : Nat ; v2 = suc (suc zero)
  v3 : Nat ; v3 = suc v2
  v4 : Nat ; v4 = suc v3

  v2C : Term ; v2C = reify (code (var v2))
  v3C : Term ; v3C = reify (code (var v3))
  v4C : Term ; v4C = reify (code (var v4))

------------------------------------------------------------------------
-- The encoded axiom  t  (a Term of our object language).
--
-- Under our axEqTrans orientation this encodes the formula
--   (var 4 = var 2) ⊃ ((var 4 = var 3) ⊃ (var 2 = var 3)) .
-- After ruleInst substitutions  var 4 := "num j" , var 2 := "th(x_)" ,
-- var 3 := "sub(i,i)" , the formula becomes
--   (num j = th(x_)) ⊃ ((num j = sub(i,i)) ⊃ (th(x_) = sub(i,i))) ,
-- whose conclusion matches guard15's step 3 target.

t : Term
t = encAxEqTrans v4C v2C v3C

------------------------------------------------------------------------
-- Target formula of  t  at the Formula level.

tFormula : Formula
tFormula = (atomic (eqn (var v4) (var v2)))
           imp ((atomic (eqn (var v4) (var v3)))
                 imp (atomic (eqn (var v2) (var v3))))

------------------------------------------------------------------------
-- DerivF-level proof of  t 's formula.

tDeriv : Deriv tFormula
tDeriv = axEqTrans (var v4) (var v2) (var v3)

------------------------------------------------------------------------
-- Correctness of the encoded proof: thmT(t) unfolds to the
-- Gödel-code of  tFormula .  Follows directly from
--  encAxEqTransCorr ; the definitional equality
--    reify (codeFormula tFormula) = <encAxEqTransCorr's RHS>
-- holds because codeFormula and reify both reduce on fully-concrete
-- variable indices.

tCorr : Deriv (atomic (eqn (ap1 thmT t) (reify (codeFormula tFormula))))
tCorr = encAxEqTransCorr v4C v2C v3C
