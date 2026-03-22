{-# OPTIONS --without-K --exact-split #-}

-- BTADynamic.agda -- Minimal dynamic proof system with CUT
--
-- A tiny sequent-style system (ProofD) with axiom, modus ponens, and CUT.
-- Cut elimination is the swap reduction: pCutD p q -> pMpD q p.
-- The Nelson chain argument proves that no ProofD proves fbotD.
--
-- FINDING: The chain "works" but the result is trivially true because
-- the system is too weak for self-reference.  Making it non-trivial
-- reintroduces all Goedel II issues.

module BTADynamic where

open import ChwistekSyntax

------------------------------------------------------------------------
-- 0. Local helpers (no postulates, no holes)
------------------------------------------------------------------------

data EmptyD : Set where

data BoolD : Set where
  trueD  : BoolD
  falseD : BoolD

andD : BoolD -> BoolD -> BoolD
andD trueD  b = b
andD falseD _ = falseD

------------------------------------------------------------------------
-- 1. Tag constants (n70..n72)
------------------------------------------------------------------------

private
  -- Build n70 step by step
  n10D : Nat
  n10D = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  n20D : Nat
  n20D = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n10D)))))))))

  n30D : Nat
  n30D = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n20D)))))))))

  n40D : Nat
  n40D = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n30D)))))))))

  n50D : Nat
  n50D = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n40D)))))))))

  n60D : Nat
  n60D = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n50D)))))))))

  n70 : Nat
  n70 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n60D)))))))))

  n71 : Nat
  n71 = suc n70

  n72 : Nat
  n72 = suc n71

------------------------------------------------------------------------
-- 2. ProofD: proof terms with cut
------------------------------------------------------------------------

data ProofD : Set where
  pAxD  : Nat -> ProofD
  pMpD  : ProofD -> ProofD -> ProofD
  pCutD : ProofD -> ProofD -> ProofD

------------------------------------------------------------------------
-- 3. Encoding into Code
------------------------------------------------------------------------

encD : ProofD -> Code
encD (pAxD k)    = cnode (catom n70) (catom k)
encD (pMpD p q)  = cnode (catom n71) (cnode (encD p) (encD q))
encD (pCutD p q) = cnode (catom n72) (cnode (encD p) (encD q))

------------------------------------------------------------------------
-- 4. FormD: minimal formula type
------------------------------------------------------------------------

data FormD : Set where
  fbotD  : FormD
  fatomD : Nat -> FormD
  fimpD  : FormD -> FormD -> FormD

------------------------------------------------------------------------
-- 5. TypesD: typing relation
------------------------------------------------------------------------

data TypesD : ProofD -> FormD -> Set where
  tAxD  : (k : Nat) -> TypesD (pAxD k) (fatomD k)
  tMpD  : {p q : ProofD} {A B : FormD} ->
           TypesD p (fimpD A B) -> TypesD q A -> TypesD (pMpD p q) B
  tCutD : {p q : ProofD} {A B : FormD} ->
           TypesD p A -> TypesD q (fimpD A B) -> TypesD (pCutD p q) B

------------------------------------------------------------------------
-- 6. Cut elimination: pCutD p q  ->  pMpD q p  (swap and remove cut)
--
-- tCutD says: p proves A, q proves A->B, so pCutD p q proves B.
-- tMpD  says: first arg proves C->D, second proves C, result proves D.
-- So pMpD q p with tMpD (q : A->B) (p : A) gives B.  Same result.
------------------------------------------------------------------------

reduceD : ProofD -> ProofD
reduceD (pCutD p q) = pMpD q p
reduceD (pAxD k)    = pAxD k
reduceD (pMpD p q)  = pMpD p q

------------------------------------------------------------------------
-- 7. Normal form: no pCutD anywhere
------------------------------------------------------------------------

orD : BoolD -> BoolD -> BoolD
orD trueD  _ = trueD
orD falseD b = b

hasCutD : ProofD -> BoolD
hasCutD (pAxD _)    = falseD
hasCutD (pMpD p q)  = orD (hasCutD p) (hasCutD q)
hasCutD (pCutD _ _) = trueD

notD : BoolD -> BoolD
notD trueD  = falseD
notD falseD = trueD

normalD : ProofD -> BoolD
normalD p = notD (hasCutD p)

------------------------------------------------------------------------
-- 8. Type preservation for reduceD
------------------------------------------------------------------------

reduceD-typed : {p : ProofD} {A : FormD} -> TypesD p A -> TypesD (reduceD p) A
reduceD-typed (tAxD k)          = tAxD k
reduceD-typed (tMpD tp tq)      = tMpD tp tq
reduceD-typed (tCutD tp tq)     = tMpD tq tp

------------------------------------------------------------------------
-- 9. No normal form proves a non-atomic formula
--
-- Key insight: pAxD only proves atoms.  pMpD p q proves B when
-- p proves (A -> B), but to prove an implication via pMpD we need
-- p to prove (C -> (A -> B)), which again requires an implication
-- proof, leading to infinite regress.  The only base case is pAxD,
-- which only proves atoms.
--
-- We prove: any cut-free ProofD that types to some FormD must type
-- to an atom.  Specifically, TypesD (pAxD k) fbotD is impossible,
-- and TypesD (pMpD p q) A requires TypesD p (fimpD C A) -- but
-- we show no cut-free proof can type to an implication.
------------------------------------------------------------------------

-- Auxiliary: FormD is not an atom
private
  data IsAtomD : FormD -> Set where
    isAtomD : (k : Nat) -> IsAtomD (fatomD k)

  -- No typing derivation for pAxD k can give fbotD
  ax-not-bot : (k : Nat) -> TypesD (pAxD k) fbotD -> EmptyD
  ax-not-bot k ()

  -- No typing derivation for pAxD k can give an implication
  ax-not-imp : (k : Nat) (A B : FormD) -> TypesD (pAxD k) (fimpD A B) -> EmptyD
  ax-not-imp k A B ()

  -- A cut-free proof cannot prove an implication.
  -- We prove this by induction on ProofD, restricted to cut-free terms.
  -- A "cut-free" proof is built from pAxD and pMpD only.
  --
  -- pAxD k : only proves fatomD k (never an implication)
  -- pMpD p q : proves B where p proves (A -> B) and q proves A
  --            but p must also be cut-free, and p proves an implication,
  --            so by induction p cannot exist.

  -- We combine: no cut-free proof proves an implication, and
  -- no cut-free proof proves fbotD.

  -- Mutual induction: cutfree-not-imp and cutfree-not-bot
  cutfree-not-imp : (p : ProofD) (A B : FormD) ->
                     TypesD p (fimpD A B) -> Eq (hasCutD p) falseD -> EmptyD
  cutfree-not-bot : (p : ProofD) ->
                     TypesD p fbotD -> Eq (hasCutD p) falseD -> EmptyD

  orD-left : (a b : BoolD) -> Eq (orD a b) falseD -> Eq a falseD
  orD-left trueD  _ ()
  orD-left falseD _ _ = refl

  cutfree-not-imp (pAxD k) A B () _
  cutfree-not-imp (pMpD p q) A B (tMpD {_} {_} {C} tp tq) hcf =
    cutfree-not-imp p C (fimpD A B) tp (orD-left (hasCutD p) (hasCutD q) hcf)
  cutfree-not-imp (pCutD _ _) A B _ ()

  cutfree-not-bot (pAxD k) () _
  cutfree-not-bot (pMpD p q) (tMpD {_} {_} {C} tp tq) hcf =
    cutfree-not-imp p C fbotD tp (orD-left (hasCutD p) (hasCutD q) hcf)
  cutfree-not-bot (pCutD _ _) _ ()

------------------------------------------------------------------------
-- 10. Full normalization via structural recursion
--
-- eliminateAllCuts walks the proof tree and replaces every pCutD
-- by the equivalent pMpD (with swapped arguments).
------------------------------------------------------------------------

eliminateAllCuts : ProofD -> ProofD
eliminateAllCuts (pAxD k)    = pAxD k
eliminateAllCuts (pMpD p q)  = pMpD (eliminateAllCuts p) (eliminateAllCuts q)
eliminateAllCuts (pCutD p q) = pMpD (eliminateAllCuts q) (eliminateAllCuts p)

-- The result is cut-free
private
  elim-cutfree : (p : ProofD) -> Eq (hasCutD (eliminateAllCuts p)) falseD
  elim-cutfree (pAxD k)    = refl
  elim-cutfree (pMpD p q)  =
    merge-false (hasCutD (eliminateAllCuts p))
                (hasCutD (eliminateAllCuts q))
                (elim-cutfree p) (elim-cutfree q)
    where
    merge-false : (a b : BoolD) -> Eq a falseD -> Eq b falseD ->
                  Eq (orD a b) falseD
    merge-false trueD  _ () _
    merge-false falseD _ _  e2 = e2
  elim-cutfree (pCutD p q) =
    merge-false2 (hasCutD (eliminateAllCuts q))
                 (hasCutD (eliminateAllCuts p))
                 (elim-cutfree q) (elim-cutfree p)
    where
    merge-false2 : (a b : BoolD) -> Eq a falseD -> Eq b falseD ->
                   Eq (orD a b) falseD
    merge-false2 trueD  _ () _
    merge-false2 falseD _ _  e2 = e2

-- Type preservation for eliminateAllCuts
elim-typed : {p : ProofD} {A : FormD} ->
             TypesD p A -> TypesD (eliminateAllCuts p) A
elim-typed (tAxD k)      = tAxD k
elim-typed (tMpD tp tq)  = tMpD (elim-typed tp) (elim-typed tq)
elim-typed (tCutD tp tq) = tMpD (elim-typed tq) (elim-typed tp)

------------------------------------------------------------------------
-- 11. The Nelson chain: no ProofD proves fbotD
------------------------------------------------------------------------

-- conD: the meta-level consistency result
--
-- Given any p : ProofD with TypesD p fbotD:
-- 1. eliminateAllCuts p is cut-free  (elim-cutfree)
-- 2. eliminateAllCuts p still proves fbotD  (elim-typed)
-- 3. No cut-free proof proves fbotD  (cutfree-not-bot)
-- 4. Contradiction.

conD : (p : ProofD) -> TypesD p fbotD -> EmptyD
conD p tp = cutfree-not-bot
  (eliminateAllCuts p)
  (elim-typed tp)
  (elim-cutfree p)

------------------------------------------------------------------------
-- 12. Internalization analysis
--
-- The meta-level Nelson chain (conD) is an ABSOLUTE contradiction:
-- it says no ProofD proves fbotD, period.
--
-- However, this result is TRIVIAL: ProofD is extremely weak.
-- - tAxD only introduces atoms (fatomD k).
-- - There are no axioms that introduce implications.
-- - Therefore no proof can produce ANY non-atomic formula.
-- - fbotD is not atomic, so it is unprovable.
--
-- For the Nelson chain to be non-trivial, the proof system would
-- need to be strong enough for self-reference:
-- - Axiom schemas for arithmetic (to encode its own syntax)
-- - A provability predicate (to express "I am unprovable")
-- - Enough logical strength to derive the diagonal lemma
--
-- Adding these features brings back all the Goedel II machinery.
-- In particular, conD's proof technique (normalize then inspect)
-- would fail because:
-- (a) Normalization may not terminate in a stronger system.
-- (b) Normal forms in a stronger system CAN prove non-atoms
--     (via axiom schemas that directly introduce implications).
-- (c) The structural argument (cutfree-not-imp) breaks when
--     axioms can introduce arbitrary formula shapes.
--
-- CLASSIFICATION: This is neither Goedel-style (no fixed-point)
-- nor a genuine Nelson argument (no self-reference).  It is a
-- proof-theoretic triviality dressed in Nelson's vocabulary.
-- Making it non-trivial is exactly the Goedel II problem.
------------------------------------------------------------------------
