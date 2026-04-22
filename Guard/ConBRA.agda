{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ConBRA -- the BRA-style internal consistency sentence.
--
-- Following Guard 1963 (BRA, Theorem 14), the consistency statement
-- of BRA is "th(y) ≠ '0 = 1'" (for all y, no encoded proof y satisfies
-- thmT(trivC)(y) = codeBot).
--
-- In our setting:
--
--   conBRAEqn : Equation
--   conBRAEqn = eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT)
--                   falseT
--
--   ConBRA   : Formula
--   ConBRA   = atomic conBRAEqn
--
-- This is the BRA analog of Guard.ProvV3.conSentenceV3, which uses
-- thmT (reify cGSV3) instead of thmT trivCT.  The BRA form (using
-- trivCT) is the one that lives at the Triv ambient — sound per
-- Guard/SOUNDNESS.md.
--
-- This file is purely declarative; no proofs.

module Guard.ConBRA where

open import Guard.Base
open import Guard.Term
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3 using (thmT)
open import Guard.SubstTForPrecompClassical using (Triv ; trivCT ; trivCTDef)
open import Guard.ProvV3 using (codeBot ; codeBotT ; trueT ; falseT)
open import Guard.Formula

------------------------------------------------------------------------
-- The BRA-style consistency equation.
--
-- Reads: "for all proof encodings y, thmT(trivC)(y) is not codeBot",
-- i.e. "no y is a Triv-proof of  trueT = falseT ".
--
-- The free variable is var zero (the proof slot).  After substituting
-- a candidate proof encoding for var zero, the equation becomes a
-- closed assertion that thmT(trivC) does not produce codeBot on that
-- candidate.

conBRAEqn : Equation
conBRAEqn = eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT)
                falseT

------------------------------------------------------------------------
-- The BRA consistency formula (atomic wrapper).

ConBRA : Formula
ConBRA = atomic conBRAEqn

------------------------------------------------------------------------
-- Convenience: explicit form of the substituted equation.

conBRAEqnAt : (X : Term) -> Equation
conBRAEqnAt X = eqn (ap2 TreeEq (ap1 (thmT trivCT) X) codeBotT)
                    falseT

------------------------------------------------------------------------
-- Identity: the substituted form matches substEq zero X conBRAEqn.
-- (substReify on trivCT and codeBotT are both reify-of-closed-tree, so
-- substitution is identity on them.)

open import Guard.Nelson.SubstReify using (substReify)
open import Guard.SubstTForPrecompClassical using (trivC)

-- trivCT is abstract; use trivCTDef to bridge to (reify trivC) so that
-- substReify applies (it operates on `reify t` for tree t).

private
  substTrivCT : (X : Term) -> Eq (subst zero X trivCT) trivCT
  substTrivCT X =
    eqTrans (eqCong (subst zero X) trivCTDef)
            (eqTrans (substReify zero X (codeEqn Triv))
                     (eqSym trivCTDef))

conBRAEqnSubstZero : (X : Term) ->
  Eq (substEq zero X conBRAEqn) (conBRAEqnAt X)
conBRAEqnSubstZero X =
  eqCong2 eqn
    (eqCong2 (ap2 TreeEq)
      (eqCong2 ap1 (eqCong thmT (substTrivCT X))
                   refl)
      (substReify zero X codeBot))
    refl
