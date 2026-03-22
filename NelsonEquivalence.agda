{-# OPTIONS --without-K --exact-split #-}

-- NelsonEquivalence.agda
--
-- THE SHARP EQUIVALENCE THEOREM: R3 <-> Con
--
-- R3 ("no cut-free proof proves fbot") is EXACTLY equivalent to
-- Con ("no proof proves fbot"), under the structural assumptions
-- of cut elimination alone.  No consistency, soundness, reflection,
-- or induction on proof codes is needed -- only:
--   1. Cut elimination terminates (structural recursion on ProofE)
--   2. Cut elimination produces cut-free output (structural proof)
--   3. Cut elimination preserves typing (structural proof)
--
-- This equivalence is the deepest insight of Nelson's program:
-- cut elimination COLLAPSES R3 and Con.  Without cut elimination,
-- R3 would be strictly weaker.  With it, they are equivalent.
-- The very success of the reduction theory is what makes R3
-- as hard as Con.

module NelsonEquivalence where

open import ChwistekSyntax

------------------------------------------------------------------------
-- 0. Local helpers
------------------------------------------------------------------------

data EmptyN : Set where

------------------------------------------------------------------------
-- 1. FormE, ProofE, TypesE (redefined locally, same as NelsonObstruction)
------------------------------------------------------------------------

data FormE : Set where
  fbotE  : FormE
  fatomE : Nat -> FormE
  fimpE  : FormE -> FormE -> FormE

data ProofE : Set where
  pAxE  : Nat -> ProofE
  pMpE  : ProofE -> ProofE -> ProofE
  pCutE : ProofE -> ProofE -> ProofE
  pImpI : ProofE -> ProofE

data TypesE : ProofE -> FormE -> Set where
  tAxE  : (k : Nat) -> TypesE (pAxE k) (fatomE k)
  tMpE  : {p q : ProofE} {A B : FormE} ->
           TypesE p (fimpE A B) -> TypesE q A -> TypesE (pMpE p q) B
  tCutE : {p q : ProofE} {A B : FormE} ->
           TypesE p A -> TypesE q (fimpE A B) -> TypesE (pCutE p q) B
  tImpIE : {p : ProofE} {B : FormE} ->
            TypesE p B -> (A : FormE) -> TypesE (pImpI p) (fimpE A B)

------------------------------------------------------------------------
-- 2. Cut-free predicate (inductive, not Boolean)
------------------------------------------------------------------------

data CutFree : ProofE -> Set where
  cfAx   : (k : Nat) -> CutFree (pAxE k)
  cfMp   : {p q : ProofE} -> CutFree p -> CutFree q -> CutFree (pMpE p q)
  cfImpI : {p : ProofE} -> CutFree p -> CutFree (pImpI p)

------------------------------------------------------------------------
-- 3. Consistency and R3
------------------------------------------------------------------------

-- Con: no proof (of any shape) proves fbot
ConE : Set
ConE = (p : ProofE) -> TypesE p fbotE -> EmptyN

-- R3: no cut-free proof proves fbot
R3E : Set
R3E = (p : ProofE) -> CutFree p -> TypesE p fbotE -> EmptyN

------------------------------------------------------------------------
-- 4. Direction 1: Con -> R3 (trivial restriction)
------------------------------------------------------------------------

-- If no proof proves fbot, then in particular no cut-free proof does.
con-to-r3 : ConE -> R3E
con-to-r3 con p cf tp = con p tp

------------------------------------------------------------------------
-- 5. Cut elimination infrastructure
------------------------------------------------------------------------

eliminateAllCutsE : ProofE -> ProofE
eliminateAllCutsE (pAxE k)    = pAxE k
eliminateAllCutsE (pMpE p q)  = pMpE (eliminateAllCutsE p) (eliminateAllCutsE q)
eliminateAllCutsE (pCutE p q) = pMpE (eliminateAllCutsE q) (eliminateAllCutsE p)
eliminateAllCutsE (pImpI p)   = pImpI (eliminateAllCutsE p)

-- Cut elimination produces cut-free proofs (inductive version)
elim-cutfreeE : (p : ProofE) -> CutFree (eliminateAllCutsE p)
elim-cutfreeE (pAxE k)    = cfAx k
elim-cutfreeE (pMpE p q)  = cfMp (elim-cutfreeE p) (elim-cutfreeE q)
elim-cutfreeE (pCutE p q) = cfMp (elim-cutfreeE q) (elim-cutfreeE p)
elim-cutfreeE (pImpI p)   = cfImpI (elim-cutfreeE p)

-- Cut elimination preserves typing
elim-typedE : {p : ProofE} {A : FormE} ->
              TypesE p A -> TypesE (eliminateAllCutsE p) A
elim-typedE (tAxE k)       = tAxE k
elim-typedE (tMpE tp tq)   = tMpE (elim-typedE tp) (elim-typedE tq)
elim-typedE (tCutE tp tq)  = tMpE (elim-typedE tq) (elim-typedE tp)
elim-typedE (tImpIE tp A)  = tImpIE (elim-typedE tp) A

------------------------------------------------------------------------
-- 6. Direction 2: R3 -> Con (via cut elimination)
------------------------------------------------------------------------

-- Given R3 and any proof p of fbot, normalize p to get a cut-free
-- proof of fbot, then apply R3 to get a contradiction.
-- Three lines.  Uses ONLY structural properties 1-3.
r3-to-con : R3E -> ConE
r3-to-con r3 p tp = r3 (eliminateAllCutsE p) (elim-cutfreeE p) (elim-typedE tp)

------------------------------------------------------------------------
-- 7. The sharp equivalence: R3 <-> Con
------------------------------------------------------------------------

data PairS (A B : Set) : Set where
  mkPairS : A -> B -> PairS A B

r3-iff-con : PairS (R3E -> ConE) (ConE -> R3E)
r3-iff-con = mkPairS r3-to-con con-to-r3

------------------------------------------------------------------------
-- 8. Analysis of hidden assumptions
------------------------------------------------------------------------

-- The proof of R3 -> Con uses EXACTLY three structural properties:
--   1. Cut elimination terminates (Agda structural recursion)
--   2. Cut elimination produces cut-free output (elim-cutfreeE)
--   3. Cut elimination preserves typing (elim-typedE)
--
-- NONE of these require:
--   - Consistency (Con)
--   - Soundness
--   - Reflection
--   - Induction on proof codes
--
-- Therefore: R3 <-> Con with NO hidden assumptions beyond the
-- reduction theory (cut elimination).

------------------------------------------------------------------------
-- 9. Classification of Nelson's program
------------------------------------------------------------------------

-- Nelson's chain:
--   R1 (reduction preserves provability): STRUCTURAL (always holds)
--   R2 (normalization preserves provability): STRUCTURAL (always holds)
--   R3 (no normal form proves fbot): EQUIVALENT TO Con
--
-- The chain gives: R3 -> Con.
-- Combined with the trivial Con -> R3, we get R3 <-> Con.
-- The chain is TAUTOLOGICAL: it proves Con assuming R3, which IS Con.
--
-- WHY NORMAL-FORM ANALYSIS = CONSISTENCY
-- =======================================
-- R3 says "no normal form proves fbot."
-- Con says "no proof proves fbot."
-- These are equivalent because every proof CAN BE normalized
-- (cut elimination), and normalization preserves what the proof
-- proves (type preservation).  So if any proof proved fbot, its
-- normal form would also prove fbot, violating R3.  The bridge
-- is cut elimination -- a structural, mechanical procedure that
-- doesn't require knowing whether the system is consistent.
--
-- Normal-form analysis BECOMES consistency analysis because cut
-- elimination ensures that the normal-form fragment is as strong
-- as the full system.
--
-- NELSON'S PROGRAM: FINAL VERDICT
-- ================================
-- In the non-self-referential case (ProofE without fPrf), R3 IS
-- provable by syntactic analysis of normal forms (see
-- NelsonObstruction.cutfree-not-bot).  The Nelson chain succeeds.
--
-- In the self-referential case (with fPrf), R3 = Con, so proving
-- R3 = proving Con, which by Goedel II is impossible for a
-- consistent system that can represent its own provability predicate.
--
-- THE DEEPEST INSIGHT: Cut elimination COLLAPSES R3 and Con.
-- Without cut elimination, R3 would be strictly weaker (easier).
-- With cut elimination, they're equivalent.  So the very success
-- of the reduction theory (cut elimination works!) is what makes
-- R3 as hard as Con.
