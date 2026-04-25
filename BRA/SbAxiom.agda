{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SbAxiom -- the computational bridge between  sb  (BRA.Sb) and
-- the BRA-internal substitution-rule-encoding output  outRuleInst
-- (BRA.Thm.Parts.RuleInst).
--
-- The point of this file is to discharge a small, isolated meta
-- equality without adding any new Deriv axioms.
--
-- Recall:
--
--   sbDef                (BRA.Sb)
--     :  ap2 sb (ap2 Pair (reify codeA) (reify (natCode k)))
--                (reify codeP)
--      = reify (codedSubst codeA (code (var k)) codeP) .
--
--   codeCommutesFormula  (BRA.CodeCommutes)
--     :  codeFormula (substF k t F)
--      = codedSubst (code t) (code (var k)) (codeFormula F) .
--
--   outRuleInst k t P    (BRA.Thm.Parts.RuleInst)
--     =  codeFormula (substF k t P) .
--
-- Composing these yields  sbForOutRuleInst : the application of  sb
-- to a (closed) coded term  t , a variable index  k , and a coded
-- formula  P  reduces (in BRA, derivably) to  reify (outRuleInst k t P) .
--
-- This is the kernel of Goedel II step 4's "by the definition of j"
-- substitution: starting from a derivation about  sb  on coded data,
-- we can move freely to the  outRuleInst  /  substF -based
-- representation that  BRA.Thm.Parts.RuleInst.thmTDispRuleInst
-- expects.
--
-- No new postulates, no new Deriv axioms.  All the "novel" content is
-- in  sbDef  and  codeCommutesFormula ; this file just composes them.
--
-- The remaining work for Goedel II step 4 -- defining a parametric
-- subst-rule encoding  subEnc : Term -> Term  and connecting
--  ap1 thmT (subEnc x)  to  sb  parametrically in  x  -- is a separate
-- subproject (see  BRA/NEXT-SESSION-GODELII-V2.md ).  This file is
-- strictly the computational kernel.

module BRA.SbAxiom where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.CodeCommutes using (codeCommutesFormula)
open import BRA.Sb
open import BRA.Thm.Parts.RuleInst using (outRuleInst)

------------------------------------------------------------------------
-- sbForOutRuleInst:
--
--   ap2 sb (Pair (reify (code t)) (reify (natCode k))) (reify (codeFormula P))
--     =  reify (outRuleInst k t P) .
--
-- Equivalently: sb on closed coded inputs reduces to the coded
-- formula obtained by metalevel substitution.

sbForOutRuleInst : (k : Nat) (t : Term) (P : Formula) ->
  Deriv (atomic (eqn (ap2 sb (ap2 Pair (reify (code t)) (reify (natCode k)))
                              (reify (codeFormula P)))
                      (reify (outRuleInst k t P))))
sbForOutRuleInst k t P =
  let -- Step 1: sbDef applied at (codeA = code t, n = k, codeP = codeFormula P).
      base : Deriv (atomic (eqn (ap2 sb (ap2 Pair (reify (code t)) (reify (natCode k)))
                                         (reify (codeFormula P)))
                                 (reify (codedSubst (code t)
                                                     (code (var k))
                                                     (codeFormula P)))))
      base = sbDef (code t) k (codeFormula P)

      -- Step 2: codeCommutesFormula k t P gives the meta equality
      --   codeFormula (substF k t P)
      --     = codedSubst (code t) (code (var k)) (codeFormula P) ,
      -- and  outRuleInst k t P  is by definition the LHS, so we
      -- transport along the symmetric equality.

      cc : Eq (codedSubst (code t) (code (var k)) (codeFormula P))
              (outRuleInst k t P)
      cc = eqSym (codeCommutesFormula k t P)

      Goal : Tree -> Set
      Goal tree =
        Deriv (atomic (eqn (ap2 sb (ap2 Pair (reify (code t)) (reify (natCode k)))
                                    (reify (codeFormula P)))
                            (reify tree)))

  in eqSubst Goal cc base
