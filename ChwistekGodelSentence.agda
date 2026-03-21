{-# OPTIONS --without-K --exact-split #-}

module ChwistekGodelSentence where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability
open import ChwistekCodeLogic
open import ChwistekCodeQuant

------------------------------------------------------------------------
-- A. The template phi
------------------------------------------------------------------------

-- phi has one free code variable (index 0 from outside).
-- Under the fcAll binder:
--   cvz  (var 0) = used in csub (will be replaced by substFormulaCode0)
--   cvs cvz (var 1) = used in ccheck (will become the new var 0 = bound var)
--
-- After substFormulaCode0 (clit phiCode) phi:
--   cvar cvz → clit phiCode         (the self-code, plugged in)
--   cvar (cvs cvz) → cvar cvz       (shifted down, becomes bound var)
--
-- So the result is:
--   fcAll (fimp (fceq (ccheck (cvar cvz))
--                     (csub (clit phiCode) (clit phiCode)))
--               fbot)
--
-- which says "for all p, checkProof(p) != csub(phiCode, phiCode)"

phi : Formula
phi = fcAll (fimp (fceq (ccheck (cvar (cvs cvz)))
                        (csub (cvar cvz) (cvar cvz)))
                  fbot)

------------------------------------------------------------------------
-- B. The code of phi
------------------------------------------------------------------------

phiCode : Code
phiCode = encFormula phi

------------------------------------------------------------------------
-- C. The Goedel sentence
------------------------------------------------------------------------

GoedelSentence : Formula
GoedelSentence = substFormulaCode0 (clit phiCode) phi

------------------------------------------------------------------------
-- D. Unfolding
------------------------------------------------------------------------

GoedelSentence-shape : Formula
GoedelSentence-shape =
  fcAll (fimp (fceq (ccheck (cvar cvz))
                    (csub (clit phiCode) (clit phiCode)))
              fbot)

GoedelSentence-unfold : Eq GoedelSentence GoedelSentence-shape
GoedelSentence-unfold = refl

------------------------------------------------------------------------
-- E. The self-reference property
------------------------------------------------------------------------

-- evalCExp (csub (clit phiCode) (clit phiCode))
--   = just (encFormula GoedelSentence)
--
-- Proof:
--   evalCExp (csub (clit phiCode) (clit phiCode))
--   = maybeBind (just phiCode) (\ c1 ->
--     maybeBind (just phiCode) (\ c2 ->
--     maybeBind (decFormula c1) (\ a ->
--     just (encFormula (substFormulaCode0 (clit c2) a)))))
--   = maybeBind (decFormula phiCode) (\ a ->
--     just (encFormula (substFormulaCode0 (clit phiCode) a)))
--   By decFormula-encFormula phi:
--   = just (encFormula (substFormulaCode0 (clit phiCode) phi))
--   = just (encFormula GoedelSentence)

phiCode-decodes : Eq (decFormula phiCode) (just phi)
phiCode-decodes = decFormula-encFormula phi

GoedelSentence-self-ref :
  Eq (evalCExp (csub (clit phiCode) (clit phiCode)))
     (just (encFormula GoedelSentence))
GoedelSentence-self-ref =
  eqCong (\ r -> maybeBind r
           (\ a -> just (encFormula (substFormulaCode0 (clit phiCode) a))))
         phiCode-decodes

------------------------------------------------------------------------
-- F. Interpretation
------------------------------------------------------------------------

-- GoedelSentence =
--   fcAll (fimp (fceq (ccheck (cvar cvz))
--                     (csub (clit phiCode) (clit phiCode)))
--               fbot)
--
-- Reading:
--   "For all proof codes p,
--    if checkProof(p) equals eval(csub(phiCode, phiCode)),
--    then false."
--
-- By GoedelSentence-self-ref:
--   eval(csub(phiCode, phiCode)) = encFormula(GoedelSentence)
--
-- So GoedelSentence says:
--   "For all proof codes p,
--    checkProof(p) != encFormula(GoedelSentence)"
--
-- i.e., "I am not provable."
--
-- How circularity is avoided:
--
--   GoedelSentence does NOT contain encFormula(GoedelSentence).
--   It contains csub (clit phiCode) (clit phiCode), a finite CExp
--   that COMPUTES encFormula(GoedelSentence) at evaluation time.
--   phiCode is the code of the template phi, and csub applies the
--   classical quine trick: decode phi, substitute phiCode into it,
--   re-encode — producing the code of GoedelSentence.
--
-- Why GoedelSentence-unfold is the fixed-point property:
--
--   The Goedel fixed-point lemma says: for any property P(x),
--   there exists G such that G <-> P(code(G)).
--   Here P(c) = "no proof has checkProof = c", and
--   GoedelSentence-self-ref shows that the CExp inside G
--   evaluates to code(G). This IS the fixed point.
--
-- Next step:
--
--   Prove: if ProvableFormula GoedelSentence, then for the witness
--   proof code p, checkProof(p) = just GoedelSentence, hence
--   encFormula(GoedelSentence) = evalCExp(ccheck(clit p))
--   = evalCExp(csub(clit phiCode)(clit phiCode)), which means
--   fceq holds, contradicting GoedelSentence (which says it implies
--   fbot). This gives: Consistent -> Not (ProvableFormula GoedelSentence).
