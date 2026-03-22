{-# OPTIONS --without-K --exact-split #-}

-- NelsonObstruction.agda
--
-- POSITIVE RESULT: The Nelson chain (cut elimination + normal form analysis)
-- proves consistency of ProofE, a system with implication introduction (pImpI).
-- This is strictly stronger than BTADynamic's ProofD (which has no logical axioms).
--
-- NEGATIVE RESULT: In any self-referential extension (with fPrf), R3 (no normal
-- form proves fbot) becomes equivalent to Con.  The Nelson chain then yields
-- Con -> Con, which is tautological and not a genuine consistency proof.
--
-- CLASSIFICATION: R3 is the exact obstruction point.  R1 (cut elimination)
-- and R2 (type preservation) are structural and always hold.  R3 requires
-- knowing that axioms + rules cannot derive fbot, which IS the consistency
-- assumption in any self-referential system.

module NelsonObstruction where

open import ChwistekSyntax

------------------------------------------------------------------------
-- 0. Local helpers
------------------------------------------------------------------------

data EmptyE : Set where

data BoolE : Set where
  trueE  : BoolE
  falseE : BoolE

orE : BoolE -> BoolE -> BoolE
orE trueE  _ = trueE
orE falseE b = b

notE : BoolE -> BoolE
notE trueE  = falseE
notE falseE = trueE

------------------------------------------------------------------------
-- 1. FormE: formulas with bot, atoms, and implication
------------------------------------------------------------------------

data FormE : Set where
  fbotE  : FormE
  fatomE : Nat -> FormE
  fimpE  : FormE -> FormE -> FormE

------------------------------------------------------------------------
-- 2. ProofE: proof terms with cut AND implication introduction
--
-- pImpI is the K-axiom / weakening: from a proof of B, derive A -> B.
-- This makes ProofE strictly stronger than BTADynamic's ProofD:
-- ProofE can prove implications (ProofD cannot prove any non-atom).
------------------------------------------------------------------------

data ProofE : Set where
  pAxE  : Nat -> ProofE
  pMpE  : ProofE -> ProofE -> ProofE
  pCutE : ProofE -> ProofE -> ProofE
  pImpI : ProofE -> ProofE

------------------------------------------------------------------------
-- 3. TypesE: typing relation
------------------------------------------------------------------------

data TypesE : ProofE -> FormE -> Set where
  tAxE  : (k : Nat) -> TypesE (pAxE k) (fatomE k)
  tMpE  : {p q : ProofE} {A B : FormE} ->
           TypesE p (fimpE A B) -> TypesE q A -> TypesE (pMpE p q) B
  tCutE : {p q : ProofE} {A B : FormE} ->
           TypesE p A -> TypesE q (fimpE A B) -> TypesE (pCutE p q) B
  tImpIE : {p : ProofE} {B : FormE} ->
            TypesE p B -> (A : FormE) -> TypesE (pImpI p) (fimpE A B)

------------------------------------------------------------------------
-- 4. Cut elimination: pCutE p q -> pMpE q p
------------------------------------------------------------------------

reduceE : ProofE -> ProofE
reduceE (pCutE p q) = pMpE q p
reduceE (pAxE k)    = pAxE k
reduceE (pMpE p q)  = pMpE p q
reduceE (pImpI p)   = pImpI p

------------------------------------------------------------------------
-- 5. Type preservation for reduceE
------------------------------------------------------------------------

reduceE-typed : {p : ProofE} {A : FormE} ->
                TypesE p A -> TypesE (reduceE p) A
reduceE-typed (tAxE k)        = tAxE k
reduceE-typed (tMpE tp tq)    = tMpE tp tq
reduceE-typed (tCutE tp tq)   = tMpE tq tp
reduceE-typed (tImpIE tp A)   = tImpIE tp A

------------------------------------------------------------------------
-- 6. Cut-free predicate (Boolean)
------------------------------------------------------------------------

hasCutE : ProofE -> BoolE
hasCutE (pAxE _)    = falseE
hasCutE (pMpE p q)  = orE (hasCutE p) (hasCutE q)
hasCutE (pCutE _ _) = trueE
hasCutE (pImpI p)   = hasCutE p

normalE : ProofE -> BoolE
normalE p = notE (hasCutE p)

------------------------------------------------------------------------
-- 7. Full cut elimination (structural recursion)
------------------------------------------------------------------------

eliminateAllCutsE : ProofE -> ProofE
eliminateAllCutsE (pAxE k)    = pAxE k
eliminateAllCutsE (pMpE p q)  = pMpE (eliminateAllCutsE p) (eliminateAllCutsE q)
eliminateAllCutsE (pCutE p q) = pMpE (eliminateAllCutsE q) (eliminateAllCutsE p)
eliminateAllCutsE (pImpI p)   = pImpI (eliminateAllCutsE p)

------------------------------------------------------------------------
-- 8. eliminateAllCutsE produces cut-free proofs
------------------------------------------------------------------------

private
  merge-falseE : (a b : BoolE) -> Eq a falseE -> Eq b falseE ->
                 Eq (orE a b) falseE
  merge-falseE trueE  _ () _
  merge-falseE falseE _ _  e2 = e2

  elim-cutfreeE : (p : ProofE) -> Eq (hasCutE (eliminateAllCutsE p)) falseE
  elim-cutfreeE (pAxE k)    = refl
  elim-cutfreeE (pMpE p q)  =
    merge-falseE (hasCutE (eliminateAllCutsE p))
                 (hasCutE (eliminateAllCutsE q))
                 (elim-cutfreeE p) (elim-cutfreeE q)
  elim-cutfreeE (pCutE p q) =
    merge-falseE (hasCutE (eliminateAllCutsE q))
                 (hasCutE (eliminateAllCutsE p))
                 (elim-cutfreeE q) (elim-cutfreeE p)
  elim-cutfreeE (pImpI p)   = elim-cutfreeE p

------------------------------------------------------------------------
-- 9. Type preservation for eliminateAllCutsE
------------------------------------------------------------------------

elim-typedE : {p : ProofE} {A : FormE} ->
              TypesE p A -> TypesE (eliminateAllCutsE p) A
elim-typedE (tAxE k)       = tAxE k
elim-typedE (tMpE tp tq)   = tMpE (elim-typedE tp) (elim-typedE tq)
elim-typedE (tCutE tp tq)  = tMpE (elim-typedE tq) (elim-typedE tp)
elim-typedE (tImpIE tp A)  = tImpIE (elim-typedE tp) A

------------------------------------------------------------------------
-- 10. No cut-free proof proves fbotE
--
-- KEY DIFFERENCE from BTADynamic: cut-free proofs CAN prove implications
-- (via pImpI).  But fbotE is still unreachable because:
--   pAxE  : only atoms
--   pImpI : only implications (fimpE _ _), never fbotE
--   pMpE  : to prove fbotE, need p proving (fimpE A fbotE) and q proving A.
--           p must be cut-free. p cannot be pAxE (atoms only).
--           p could be pImpI p' (but then p' must prove fbotE -- circular).
--           p could be pMpE (same recursion on a strictly smaller proof).
--
-- Strategy: define "ends in bot" predicate on FormE.  A formula ends in bot
-- if it is fbotE or fimpE A B where B ends in bot.  Then prove: no cut-free
-- proof can prove any formula that ends in bot.  This subsumes both
-- cutfree-not-bot and cutfree-not-impbot in a single structural induction.
------------------------------------------------------------------------

private
  orE-left : (a b : BoolE) -> Eq (orE a b) falseE -> Eq a falseE
  orE-left trueE  _ ()
  orE-left falseE _ _ = refl

  -- "Ends in bot": the rightmost return type in an implication chain is fbotE
  data EndsBot : FormE -> Set where
    ebBot : EndsBot fbotE
    ebImp : (A : FormE) {B : FormE} -> EndsBot B -> EndsBot (fimpE A B)

  -- Key lemma: no cut-free ProofE proves any formula that ends in bot.
  -- By structural induction on the proof term.
  cutfree-not-endsbot : (p : ProofE) (F : FormE) ->
                         TypesE p F -> EndsBot F ->
                         Eq (hasCutE p) falseE -> EmptyE
  cutfree-not-endsbot (pAxE k) fbotE () _
  cutfree-not-endsbot (pAxE k) (fatomE _) _ () _
  cutfree-not-endsbot (pAxE k) (fimpE _ _) () _
  cutfree-not-endsbot (pMpE p q) F (tMpE {_} {_} {A} tp tq) eb hcf =
    cutfree-not-endsbot p (fimpE A F) tp (ebImp A eb)
      (orE-left (hasCutE p) (hasCutE q) hcf)
  cutfree-not-endsbot (pCutE _ _) _ _ _ ()
  cutfree-not-endsbot (pImpI p) (fimpE A B) (tImpIE tp _) (ebImp _ eb) hcf =
    cutfree-not-endsbot p B tp eb hcf

  -- Corollary: no cut-free proof proves fbotE
  cutfree-not-bot : (p : ProofE) ->
                     TypesE p fbotE -> Eq (hasCutE p) falseE -> EmptyE
  cutfree-not-bot p tp hcf = cutfree-not-endsbot p fbotE tp ebBot hcf

------------------------------------------------------------------------
-- 11. The Nelson chain: no ProofE proves fbotE (absolute consistency)
--
-- R1: eliminateAllCutsE removes all cuts  (elim-cutfreeE)
-- R2: eliminateAllCutsE preserves types   (elim-typedE)
-- R3: no cut-free proof proves fbotE      (cutfree-not-bot)
------------------------------------------------------------------------

conE : (p : ProofE) -> TypesE p fbotE -> EmptyE
conE p tp = cutfree-not-bot
  (eliminateAllCutsE p)
  (elim-typedE tp)
  (elim-cutfreeE p)

------------------------------------------------------------------------
-- 12. Demonstration: ProofE IS non-trivial (can prove implications)
------------------------------------------------------------------------

private
  -- ProofE can prove: fatomE 0 -> fatomE 0  (identity on atom 0)
  -- Proof: pImpI (pAxE 0) with type (tImpIE (tAxE 0) (fatomE 0))
  exampleImp : TypesE (pImpI (pAxE zero)) (fimpE (fatomE zero) (fatomE zero))
  exampleImp = tImpIE (tAxE zero) (fatomE zero)

  -- ProofE can prove: fatomE 1 -> (fatomE 0 -> fatomE 1)  (K combinator)
  exampleK : TypesE (pImpI (pImpI (pAxE (suc zero))))
                     (fimpE (fatomE (suc zero))
                            (fimpE (fatomE zero) (fatomE (suc zero))))
  exampleK = tImpIE (tImpIE (tAxE (suc zero)) (fatomE zero))
                     (fatomE (suc zero))

  -- ProofE can prove modus ponens on atoms via cut:
  -- Given pAxE 0 : fatomE 0 and pImpI(pAxE 1) : fimpE(fatomE 0)(fatomE 1),
  -- pCutE (pAxE 0) (pImpI (pAxE (suc zero))) proves fatomE (suc zero)
  -- ... but wait, pImpI(pAxE 1) proves fimpE _ (fatomE 1), not fimpE (fatomE 0) (fatomE 1).
  -- We need: pImpI(pAxE 1) with tImpIE (tAxE 1) (fatomE 0)
  exampleCut : TypesE (pCutE (pAxE zero) (pImpI (pAxE (suc zero))))
                       (fatomE (suc zero))
  exampleCut = tCutE (tAxE zero) (tImpIE (tAxE (suc zero)) (fatomE zero))

------------------------------------------------------------------------
-- 13. Self-referential obstruction analysis
--
-- WHY R3 FAILS WITH SELF-REFERENCE
-- =================================
--
-- Consider extending FormE with a proof predicate:
--   fPrf : Code -> Code -> FormE    (fPrf p c = "p is a proof of c")
--
-- And extending ProofE with checker axioms (as in BinaryTreeArith.agda):
--   pChkAx : ... -> ProofE   (axiom: checker accepts valid proofs)
--
-- In this extended system, a cut-free proof CAN prove fbotE:
--
--   pMpE (proof of fimpE (fPrf p enc(fbot)) fbotE)
--        (proof of fPrf p enc(fbot))
--
-- The first component is an instance of Con at proof-code p.
-- The second component asserts that p proves fbot in the system.
--
-- So R3 ("no cut-free proof proves fbotE") becomes:
--   "for all p, if normal(p), then NOT (TypesE p fbotE)"
-- which in the self-referential system is EQUIVALENT to Con:
--   "no proof-code p is accepted by the checker as proving fbot"
--
-- The Nelson chain then gives:
--   Con -> (no proof proves fbot) = Con -> Con
-- which is a tautology, not a genuine consistency proof.
--
-- THE EXACT OBSTRUCTION POINT:
-- R1 (cut elimination) is structural and always works.
-- R2 (type preservation) is structural and always works.
-- R3 (normal form analysis) requires analyzing what the AXIOMS can prove.
--    In a self-referential system, the axioms include checker rules for
--    the proof predicate. Showing these cannot derive fbot requires
--    knowing the system is consistent -- which is the very thing we
--    are trying to prove.
--
-- No amount of structural analysis bypasses this: the axioms themselves
-- could be inconsistent, and only a consistency assumption (or its
-- meta-theoretic equivalent) rules this out. This is the content of
-- Goedel's second incompleteness theorem.
--
-- SHARP CLASSIFICATION:
--   Case A (ProofE without self-reference): R3 holds by structural
--     induction. Nelson chain gives absolute consistency. But the system
--     is too weak for the result to reach Goedel II territory.
--   Case B (ProofE with self-reference): R3 is equivalent to Con.
--     Nelson chain gives Con -> Con. The Goedel II barrier is R3 itself.
------------------------------------------------------------------------
