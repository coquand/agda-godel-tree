{-# OPTIONS --without-K --exact-split #-}

module TreeArithD3 where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import ChwistekProvability
  using (Bool; true; false; and; Maybe; nothing; just;
         maybeBind; maybeMap; eqNat; eqCode; eqNat-refl)
open import TreeArith

------------------------------------------------------------------------
-- 1. FormTA2: FormTA extended with existential quantification
------------------------------------------------------------------------

data FormTA2 : Set where
  fbotTA2  : FormTA2
  fatomTA2 : Nat -> FormTA2
  fimpTA2  : FormTA2 -> FormTA2 -> FormTA2
  fallTA2  : FormTA2 -> FormTA2
  fexTA2   : FormTA2 -> FormTA2
  feqTA2   : Code -> Code -> FormTA2

------------------------------------------------------------------------
-- 2. Substitution for FormTA2 (same pattern as substFormTA)
------------------------------------------------------------------------

substFormTA2 : Code -> FormTA2 -> FormTA2
substFormTA2 c fbotTA2        = fbotTA2
substFormTA2 c (fatomTA2 n)   = fatomTA2 n
substFormTA2 c (fimpTA2 a b)  = fimpTA2 (substFormTA2 c a) (substFormTA2 c b)
substFormTA2 c (fallTA2 a)    = fallTA2 a
substFormTA2 c (fexTA2 a)     = fexTA2 a
substFormTA2 c (feqTA2 x y)   = feqTA2 x y

------------------------------------------------------------------------
-- 3. Embedding: every FormTA is a FormTA2
------------------------------------------------------------------------

liftFormTA : FormTA -> FormTA2
liftFormTA fbotTA        = fbotTA2
liftFormTA (fatomTA n)   = fatomTA2 n
liftFormTA (fimpTA a b)  = fimpTA2 (liftFormTA a) (liftFormTA b)
liftFormTA (fallTA a)    = fallTA2 (liftFormTA a)
liftFormTA (feqTA c1 c2) = feqTA2 c1 c2

------------------------------------------------------------------------
-- 4. Semantic model for FormTA2
------------------------------------------------------------------------

GoodTA2 : FormTA2 -> Set
GoodTA2 fbotTA2        = EmptyTA
GoodTA2 (fatomTA2 _)   = UnitTA
GoodTA2 (fimpTA2 a b)  = GoodTA2 a -> GoodTA2 b
GoodTA2 (fallTA2 a)    = (c : Code) -> GoodTA2 a
GoodTA2 (fexTA2 a)     = SigmaTA Code (\ c -> GoodTA2 a)
GoodTA2 (feqTA2 c1 c2) = Eq c1 c2

------------------------------------------------------------------------
-- 5. Attempt to define ProvFormula2 : Code -> FormTA2
------------------------------------------------------------------------

-- Goal: express "A is provable" as a FormTA2 formula, i.e.,
--   "exists fuel, exists code, checkTATotal fuel code = encA"
-- where encA is the encoding of A.
--
-- With fexTA2 we CAN quantify existentially over codes.
-- Nat embeds into Code via catom, so fuel can be a code.
--
-- The blocker is feqTA2: it compares two CODES for syntactic equality.
-- We need to write:
--   fexTA2 (fexTA2 (feqTA2 (checkTATotal (cvar 1) (cvar 0)) encA))
--
-- But checkTATotal is an AGDA FUNCTION (Nat -> Code -> Code).
-- feqTA2 takes two Code TERMS, not two Code-valued FUNCTIONS.
-- There is no way to apply checkTATotal to CODE VARIABLES (cvar 1, cvar 0)
-- inside feqTA2.
--
-- feqTA2 compares GROUND codes. It cannot express
--   "the result of COMPUTING f(x,y) equals z"
-- for formula-level variables x and y.
--
-- This is the fundamental obstacle: FormTA2 has no mechanism for
-- CODE-LEVEL COMPUTATION on formula-level variables.

------------------------------------------------------------------------
-- 6. Obstacle chain
------------------------------------------------------------------------

-- (a) fexTA2 provides existential quantification over codes.    [DONE]
-- (b) Nat embeds into Code via catom.                           [DONE]
-- (c) checkTA is Nat -> Code -> Maybe FormTA.
--     We could totalize it: checkTATotal : Nat -> Code -> Code
--     mapping (n, c) to encFormTA (checkTA n c) or a failure code.
-- (d) To use checkTATotal inside feqTA2, we need to APPLY it
--     to formula-level bound variables. feqTA2 takes two
--     ground Code terms, NOT functions of bound variables.
-- (e) To apply functions to bound variables inside formulas,
--     the formula language needs COMPUTATION ON CODES:
--     ctCase (case-split on catom vs cnode) and ctFold
--     (primitive recursion on codes). These are exactly
--     the code-level computation primitives from Track 1.
-- (f) Without ctCase + ctFold, feqTA2 can only compare
--     CLOSED code terms. The existentially quantified variables
--     remain opaque -- we cannot compute checkTA on them.

------------------------------------------------------------------------
-- 7. Precise classification
------------------------------------------------------------------------

-- D3 requires the system to express internally:
--   "there exist fuel n and proof code c such that
--    the checker applied to n and c yields formula A."
--
-- This decomposes into TWO independent requirements:
--
-- Requirement 1: EXISTENTIAL QUANTIFICATION over codes.
--   Status: fexTA2 provides this. Solved by the extension above.
--
-- Requirement 2: CODE-LEVEL COMPUTATION in formulas.
--   The formula language must be able to express
--   "f(x) = y" for a computable f and bound variables x, y.
--   Status: FormTA2 CANNOT do this. feqTA2 only compares ground codes.
--   Needed: ctCase + ctFold (or equivalent computation primitives).
--
-- CONCLUSION: Existentials are NECESSARY but NOT SUFFICIENT for D3.
-- D3 also requires code-level computation primitives (ctCase + ctFold).

------------------------------------------------------------------------
-- 8. Even with both, provability requires REPRESENTABILITY
------------------------------------------------------------------------

-- Suppose we had FormTA3 with fexTA3 + ctCase + ctFold.
-- Then ProvFormula3 : Code -> FormTA3 would be definable.
-- D3 would state: if checkTA n c = just A, then there exist
-- m and q such that checkTA m q = just (ProvFormula3 (encFormTA A)).
--
-- Building such q requires encoding a PROOF OF ACCEPTANCE
-- as a new proof code that the checker itself accepts.
-- This is self-representation: the system must represent
-- its own proof-checking computation as a proof.
--
-- This is Guard's Theorem 12-13: the derivability conditions
-- require the proof system to be REPRESENTABLE in itself.
-- It is feasible but requires ~200 lines of encoding work
-- on top of ctCase + ctFold + existentials.

------------------------------------------------------------------------
-- 9. Summary record (no postulates, no holes)
------------------------------------------------------------------------

-- We package the findings as concrete Agda types.

-- The extension is real: fexTA2 is a strict superset of FormTA.
fexTA2-not-in-FormTA : FormTA2
fexTA2-not-in-FormTA = fexTA2 (feqTA2 (catom zero) (catom zero))

-- The embedding preserves structure.
lift-preserves-fbot : Eq (liftFormTA fbotTA) fbotTA2
lift-preserves-fbot = refl

lift-preserves-feq : (c1 c2 : Code) ->
  Eq (liftFormTA (feqTA c1 c2)) (feqTA2 c1 c2)
lift-preserves-feq c1 c2 = refl

-- GoodTA2 extends GoodTA: lifted formulas have the same semantics.
good2-fbot-empty : GoodTA2 fbotTA2 -> EmptyTA
good2-fbot-empty x = x

good2-feq-is-eq : (c1 c2 : Code) -> GoodTA2 (feqTA2 c1 c2) -> Eq c1 c2
good2-feq-is-eq c1 c2 h = h

-- The existential semantics is a genuine Sigma.
good2-ex-witness : GoodTA2 (fexTA2 (feqTA2 (catom zero) (catom zero)))
good2-ex-witness = mkSigmaTA (catom zero) refl

-- D3 obstacle: ProvFormula cannot be defined. We demonstrate the
-- type that WOULD be needed if it could be defined, and show it
-- is inhabited trivially for the meta-level version (which is not D3).

D3-meta-type : FormTA -> Set
D3-meta-type A = SigmaTA Nat (\ n -> SigmaTA Code (\ c -> Eq (checkTA n c) (just A)))
  -> SigmaTA Nat (\ m -> SigmaTA Code (\ q ->
       Eq (checkTA m q) (just (fimpTA A (fimpTA A A)))))

-- We CAN build a trivial witness: given Prov(A), produce Prov(A -> A -> A)
-- using axK. This is NOT D3 (D3 needs Prov("Prov(A)"), not Prov(A -> A -> A)),
-- but it demonstrates the meta-level plumbing works.

d3-meta-trivial : (A : FormTA) -> D3-meta-type A
d3-meta-trivial A _ = mkSigmaTA n1 (mkSigmaTA (encProofTA (axKTA A A)) (encodeTA-axK A A))

------------------------------------------------------------------------
-- 10. Final classification
------------------------------------------------------------------------

-- | Ingredient          | Available? | Where?                          |
-- |---------------------|------------|---------------------------------|
-- | Existentials        | YES        | fexTA2 in FormTA2 (this file)   |
-- | Code computation    | NO         | Needs ctCase + ctFold (Track 1) |
-- | Representability    | NO         | Needs encoding of checkTA       |
-- |---------------------|------------|---------------------------------|
-- | D3 formulable?      | NO         | Missing code computation        |
-- | D3 provable?        | NO         | Not even formulable yet         |
--
-- Existentials alone do NOT unlock D3.
-- The minimal set for D3: existentials + ctCase + ctFold + representability.
