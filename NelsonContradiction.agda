{-# OPTIONS --without-K --exact-split #-}

-- NelsonContradiction.agda
-- Test: Can the multiset-controlled structural reduction theory derive
-- a Nelson-style contradiction WITHOUT a proof checker?
--
-- Finding: Case 4 — Contradiction requires semantic notion of proof.
-- In a system weak enough for structural reduction to control everything,
-- "contradiction" (fbotN unprovable) is trivially true because the system
-- is too weak. In a system strong enough for interesting provability,
-- structural reduction alone is insufficient.

module NelsonContradiction where

open import ChwistekSyntax

------------------------------------------------------------------------
-- Local helpers
------------------------------------------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

Not : Set -> Set
Not A = A -> Empty

andB : Bool -> Bool -> Bool
andB true  b = b
andB false _ = false

IsTrue : Bool -> Set
IsTrue true  = Nat   -- inhabited (any Nat works)
IsTrue false = Empty

------------------------------------------------------------------------
-- 1. Proof language (same as NelsonMultiset)
------------------------------------------------------------------------

data ProofN : Set where
  pax   : Nat -> ProofN
  pmp   : ProofN -> ProofN -> ProofN
  pinst : ProofN -> ProofN
  pcut  : ProofN -> ProofN -> ProofN

------------------------------------------------------------------------
-- 2. Reduction (same as NelsonMultiset)
------------------------------------------------------------------------

reduceN : ProofN -> ProofN
reduceN (pcut (pinst u) (pmp v w)) = pmp (pcut (pinst u) v) (pcut (pinst u) w)
reduceN (pcut (pinst u) (pax n))   = pcut (pinst u) (pax n)
reduceN (pcut (pinst u) (pinst q)) = pcut (pinst u) (pinst q)
reduceN (pcut (pinst u) (pcut q r)) = pcut (pinst u) (pcut q r)
reduceN (pcut (pax n) q)    = pcut (pax n) q
reduceN (pcut (pmp a b) q)  = pcut (pmp a b) q
reduceN (pcut (pcut a b) q) = pcut (pcut a b) q
reduceN (pax n)    = pax n
reduceN (pmp p q)  = pmp p q
reduceN (pinst p)  = pinst p

------------------------------------------------------------------------
-- 3. Normal form detection
------------------------------------------------------------------------

isNormalCut : ProofN -> ProofN -> Bool
isNormal    : ProofN -> Bool

isNormalCut (pinst _) (pmp _ _) = false
isNormalCut (pinst u) (pax _)   = isNormal (pinst u)
isNormalCut (pinst u) (pinst q) = andB (isNormal (pinst u)) (isNormal (pinst q))
isNormalCut (pinst u) (pcut q r) = andB (isNormal (pinst u)) (isNormalCut q r)
isNormalCut (pax _)    q = isNormal q
isNormalCut (pmp a b)  q = andB (andB (isNormal a) (isNormal b)) (isNormal q)
isNormalCut (pcut a b) q = andB (isNormalCut a b) (isNormal q)

isNormal (pax _)    = true
isNormal (pinst p)  = isNormal p
isNormal (pmp p q)  = andB (isNormal p) (isNormal q)
isNormal (pcut p q) = isNormalCut p q

------------------------------------------------------------------------
-- 4. Iterated reduction (fuel-bounded)
------------------------------------------------------------------------

normalize : Nat -> ProofN -> ProofN
normalize zero    p = p
normalize (suc n) p = normalize n (reduceN p)

------------------------------------------------------------------------
-- 5. Minimal formula type and typing
------------------------------------------------------------------------

data FormN : Set where
  fatomN : Nat -> FormN
  fimpN  : FormN -> FormN -> FormN
  fbotN  : FormN

-- Non-degenerate typing: pax k proves ONLY fatomN k
data HasType : ProofN -> FormN -> Set where
  tAx   : (k : Nat) -> HasType (pax k) (fatomN k)
  tMp   : {p q : ProofN} {A B : FormN} ->
           HasType p (fimpN A B) -> HasType q A -> HasType (pmp p q) B
  tInst  : {p : ProofN} {A : FormN} -> HasType p A -> HasType (pinst p) A
  tCut   : {p q : ProofN} {A B : FormN} ->
           HasType p A -> HasType q (fimpN A B) -> HasType (pcut p q) B

------------------------------------------------------------------------
-- 6. FormN discriminators
------------------------------------------------------------------------

-- fatomN k is never equal to fimpN A B
fatomN-not-fimpN : (k : Nat) (A B : FormN) -> Not (Eq (fatomN k) (fimpN A B))
fatomN-not-fimpN k A B ()

-- fatomN k is never equal to fbotN
fatomN-not-fbotN : (k : Nat) -> Not (Eq (fatomN k) fbotN)
fatomN-not-fbotN k ()

-- fimpN A B is never equal to fbotN
fimpN-not-fbotN : (A B : FormN) -> Not (Eq (fimpN A B) fbotN)
fimpN-not-fbotN A B ()

------------------------------------------------------------------------
-- 7. KEY: No proof term has type fimpN A B
------------------------------------------------------------------------

-- In this system, the ONLY way to introduce a formula is via tAx,
-- which gives fatomN k. tMp gives the consequent of an implication,
-- tInst preserves the type, and tCut gives the consequent.
-- But to use tMp or tCut, you need a proof of fimpN _ _, which
-- itself would require tAx to produce fimpN — impossible.
-- So fimpN A B is unprovable for all A, B.

no-imp-proof : {p : ProofN} {A B : FormN} -> Not (HasType p (fimpN A B))
no-imp-proof (tMp {A = C} {B = fimpN A B} h1 h2) = no-imp-proof h1
no-imp-proof (tInst h) = no-imp-proof h
no-imp-proof (tCut {A = C} h1 h2) = no-imp-proof h2

------------------------------------------------------------------------
-- 8. KEY: No proof term has type fbotN
------------------------------------------------------------------------

-- To get fbotN via tMp, you need HasType p (fimpN A fbotN) — but
-- fimpN A fbotN is unprovable (by no-imp-proof).
-- To get fbotN via tCut, you need HasType q (fimpN A fbotN) — same.
-- tAx gives fatomN k, never fbotN.
-- tInst preserves type, so reduces to proving the inner term has fbotN.

no-bot-proof : {p : ProofN} -> Not (HasType p fbotN)
no-bot-proof (tMp {A = A} {B = fbotN} h1 h2) = no-imp-proof h1
no-bot-proof (tInst h) = no-bot-proof h
no-bot-proof (tCut {A = A} {B = fbotN} h1 h2) = no-imp-proof h2

------------------------------------------------------------------------
-- 9. Contradiction detection
------------------------------------------------------------------------

isContradiction : ProofN -> FormN -> Bool
isContradiction p fbotN       = true
isContradiction p (fatomN _)  = false
isContradiction p (fimpN _ _) = false

------------------------------------------------------------------------
-- 10. The "Nelson argument" — trivial version
------------------------------------------------------------------------

-- Nelson's argument would be:
--   (1) Assume proof p of fbotN
--   (2) Normalize p to get p'
--   (3) p' still proves fbotN (reduction preserves typing)
--   (4) But no normal form proves fbotN
--   (5) Contradiction
--
-- In our system, step (4) is unnecessary: no proof AT ALL
-- (normal or not) proves fbotN. The contradiction is immediate.

nelson-trivial : {p : ProofN} -> HasType p fbotN -> Empty
nelson-trivial h = no-bot-proof h

------------------------------------------------------------------------
-- 11. Also: no proof of any non-atomic formula
------------------------------------------------------------------------

-- The system is so weak that only fatomN k is provable.

data IsAtomic : FormN -> Set where
  mkAtomic : (k : Nat) -> IsAtomic (fatomN k)

every-typed-is-atomic : {p : ProofN} {A : FormN} -> HasType p A -> IsAtomic A
every-typed-is-atomic (tAx k) = mkAtomic k
every-typed-is-atomic (tMp {A = A} {B = B} h1 h2) =
  emptyElim (no-imp-proof h1)
every-typed-is-atomic (tInst h) = every-typed-is-atomic h
every-typed-is-atomic (tCut {A = A} {B = B} h1 h2) =
  emptyElim (no-imp-proof h2)

------------------------------------------------------------------------
-- VERDICT
------------------------------------------------------------------------

-- The attempt to derive a Nelson-style contradiction reveals a
-- fundamental boundary:
--
-- WEAK SYSTEM (this file): Structural reduction works perfectly
--   (NelsonMultiset.agda proves termination). fbotN is unprovable.
--   But the unprovability is TRIVIAL — it follows from the typing
--   system being too weak to prove anything beyond atoms. There is
--   no self-reference, no Goedel sentence, no interesting content.
--
-- STRONG SYSTEM (ChwistekSyntax.agda with ccheck): The formula
--   language includes fbot, fimp, feq, fall, fcode, fceq, fcAll.
--   Self-reference is possible via csub. But the proof language
--   would need evaluation/checking constructors (like ccheck),
--   introducing semantic content that structural reduction cannot
--   handle.
--
-- Nelson's program sits on this boundary:
--   - Structural methods suffice for reduction control
--   - But deriving a MEANINGFUL contradiction (not a trivial one)
--     requires the system to be expressive enough that structural
--     methods alone cannot control the proof dynamics
--
-- Case 4: Contradiction requires semantic notion of proof.

record NelsonVerdict : Set where
  constructor mkNelsonVerdict
  field
    trivialContradiction : Nat  -- nonzero = trivial contradiction proved
    meaningfulBarrier    : Nat  -- nonzero = meaningful version blocked

verdict : NelsonVerdict
verdict = mkNelsonVerdict (suc zero) (suc zero)
