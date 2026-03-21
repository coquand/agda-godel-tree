{-# OPTIONS --without-K --exact-split #-}

module ChwistekGodel1 where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability

------------------------------------------------------------------------
-- A. Empty and negation
------------------------------------------------------------------------

data Empty : Set where

MetaNot : Set -> Set
MetaNot A = A -> Empty

absurd : {A : Set} -> Empty -> A
absurd ()

------------------------------------------------------------------------
-- B. Meta-level consistency
------------------------------------------------------------------------

Consistent : Set
Consistent = MetaNot (ProvableFormula fbot)

------------------------------------------------------------------------
-- C. Inspection of G
------------------------------------------------------------------------

-- G = diag Snot
-- Snot = simp shole (sconst fbot)
-- diag Snot = instantiate Snot (encSchema Snot)
--           = fimp (instantiate shole (encSchema Snot))
--                  (instantiate (sconst fbot) (encSchema Snot))
--           = fimp (fcode (encSchema Snot)) fbot

G-shape : Eq G (diag Snot)
G-shape = refl

G-expand : Eq G (fimp (fcode (encSchema Snot)) fbot)
G-expand = refl

------------------------------------------------------------------------
-- D. What would be needed for Goedel I
------------------------------------------------------------------------

-- To derive a contradiction from a proof of G, we would need:
--
--   1. A proof code p such that checkProof p = just G
--      (this is what ProvableFormula G gives us)
--
--   2. A proof code q such that checkProof q = just (fcode (encSchema Snot))
--      (a proof of the antecedent of G)
--
--   3. Then mp applied to p and q would give a proof of fbot.
--
-- Step 3 is fine: the mp-builder below constructs the code.
-- Step 1 is the hypothesis.
-- Step 2 is IMPOSSIBLE in the current system.
--
-- The proof system has rules: ax-refl, ax-k, ax-s, mp, gen.
-- None of these can produce (fcode c) as a conclusion for any c.
-- fcode is an inert data leaf with no logical role.
--
-- Therefore: even if G is provable, we cannot use it to derive fbot.
-- The implication fimp (fcode X) fbot is vacuously safe because
-- fcode X is never provable.

------------------------------------------------------------------------
-- E. MP builder (what WOULD work if we had both pieces)
------------------------------------------------------------------------

-- Given proof codes for (fimp A B) and A, build a proof code for B.

mpCode : Code -> Code -> Code
mpCode p q = cnode (catom n33) (cnode p q)

-- If checkProof p = just (fimp A B) and checkProof q = just A,
-- then checkProof (mpCode p q) should reduce to just B.
-- This is the operational content of the mp rule in checkProof.

------------------------------------------------------------------------
-- F. The trivial conditional theorem
------------------------------------------------------------------------

-- We CAN prove: if G is provable AND its antecedent is provable,
-- then fbot is provable. But this is just mp and says nothing deep.

-- The real Goedel I would need the antecedent to be derivable FROM
-- the provability of G itself. That requires G to talk about
-- provability, which the current G does not.

------------------------------------------------------------------------
-- G. Honest assessment
------------------------------------------------------------------------

-- CURRENT STATUS: the proto-Goedel sentence G is INSUFFICIENT
-- for a genuine Goedel I argument.
--
-- G = fimp (fcode (encSchema Snot)) fbot
--
-- This formula says: "if (the code of Snot) then false."
-- But "the code of Snot" is just inert data inside fcode.
-- It has no connection to provability.
--
-- A real Goedel sentence must say:
--   "if there exists a proof of me, then false"
-- or equivalently:
--   "I am not provable"
--
-- For this, the formula must MENTION provability.
-- In our system, provability is ProvableFormula : Formula -> Set,
-- which lives at the meta-level (Agda's Set), not inside Formula.
--
-- WHAT IS NEEDED NEXT:
--
-- There are three options to bridge this gap:
--
-- Option 1: INTERNALIZE PROVABILITY
--   Extend Formula with quantification over Code and a proof
--   predicate fprf. This is a major logic extension.
--
-- Option 2: ARITHMETIZE
--   Encode Code values as Terms (natural numbers), express
--   checkProof as a recursive function inside the object
--   language. This abandons the Chwistek syntax-native style.
--
-- Option 3: META-LEVEL GOEDEL I WITH REPRESENTATION ASSUMPTIONS
--   Stay at the meta-level but assume derivability conditions:
--
--   (D1) If ProvableFormula A, then ProvableFormula (repr A)
--        for some representation function repr : Formula -> Formula
--
--   (D2) A soundness bridge connecting repr to ProvableFormula
--
--   This is the standard Hilbert-Bernays approach, adapted to
--   the meta-level. It would require postulates for D1 and D2,
--   unless we build repr from the existing enc/dec machinery.
--
-- RECOMMENDED NEXT STEP:
--
--   Option 3, but constructive: define a representation function
--   repr : Formula -> Formula using encFormula and fcode, state
--   the derivability conditions as meta-level properties, and
--   prove Goedel I from them. The derivability conditions
--   themselves become the next proof obligations.
--
--   Concretely:
--     repr A = fcode (encFormula A)
--     D1 becomes: ProvableFormula A -> ProvableFormula (fcode (encFormula A))
--     This is NOT provable in the current system because fcode
--     values are not provable.
--
--   This shows the REAL gap: we need a proof rule that can
--   derive fcode values. For example:
--
--     ax-code : (c : Code) -> Proof (fcode c)
--
--   Adding this single axiom would make fcode values provable
--   and enable the Goedel argument. But it would also make G
--   provable (since the antecedent of G is fcode X), which
--   combined with G being provable gives fbot -- exactly the
--   Goedel contradiction. This confirms the structure is right.
--
--   The resolution is that ax-code should NOT be added as a
--   blanket axiom. Instead, the system should be extended so
--   that specific fcode values can be derived through computation,
--   making the question of whether G's antecedent is derivable
--   the crux of the incompleteness argument.
