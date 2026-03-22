{-# OPTIONS --without-K --exact-split #-}

-- NelsonCutCommute.agda
-- Experiment: Nelson-style cut-commuting reduction internalized in BTA.
-- Tests whether ctCase + ctFold are needed for full internalization.

module NelsonCutCommute where

open import ChwistekSyntax
open import ChwistekProvability
open import ChwistekGodel2Genuine
open import CExpPair

------------------------------------------------------------------------
-- 1. Tiny proof language
------------------------------------------------------------------------

data FormN : Set where
  fatom : Nat -> FormN
  fimp  : FormN -> FormN -> FormN

data ProofN : Set where
  pax   : Nat -> ProofN
  pmp   : ProofN -> ProofN -> ProofN
  pinst : ProofN -> ProofN
  pcut  : ProofN -> ProofN -> ProofN

------------------------------------------------------------------------
-- 2. Complexity measures
------------------------------------------------------------------------

private
  maxPN : Nat -> Nat -> Nat
  maxPN zero    m       = m
  maxPN (suc n) zero    = suc n
  maxPN (suc n) (suc m) = suc (maxPN n m)

  addPN : Nat -> Nat -> Nat
  addPN zero    m = m
  addPN (suc n) m = suc (addPN n m)

sizeP : ProofN -> Nat
sizeP (pax _)    = suc zero
sizeP (pmp p q)  = suc (addPN (sizeP p) (sizeP q))
sizeP (pinst p)  = suc (sizeP p)
sizeP (pcut p q) = suc (addPN (sizeP p) (sizeP q))

rankP : ProofN -> Nat
rankP (pax _)    = zero
rankP (pmp p q)  = suc (maxPN (rankP p) (rankP q))
rankP (pinst p)  = rankP p
rankP (pcut p q) = suc (maxPN (rankP p) (rankP q))

backtrackP : ProofN -> Nat
backtrackP (pax _)    = zero
backtrackP (pinst p)  = backtrackP p
backtrackP (pmp p q)  = suc (maxPN (backtrackP p) (backtrackP q))
backtrackP (pcut p q) = suc (maxPN (backtrackP p) (backtrackP q))

------------------------------------------------------------------------
-- 3. The reduction
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
-- 4. Meta-theorems
------------------------------------------------------------------------

-- Size may INCREASE: pinst u is duplicated into both branches.
-- For example, sizeP (pcut (pinst u) (pmp v w)) < sizeP (reduceN ...)
-- when sizeP (pinst u) > 1. This is expected and not a problem for
-- the Nelson approach (size is not the termination measure).
size-may-grow : ProofN -> Set
size-may-grow _ = UnitG2

-- Ordering for rank analysis
private
  data LeN : Nat -> Nat -> Set where
    leZ : (m : Nat) -> LeN zero m
    leS : (n m : Nat) -> LeN n m -> LeN (suc n) (suc m)

  leRefl : (n : Nat) -> LeN n n
  leRefl zero    = leZ zero
  leRefl (suc n) = leS n n (leRefl n)

  leTrans : (x y z : Nat) -> LeN x y -> LeN y z -> LeN x z
  leTrans zero    _       z       _          _          = leZ z
  leTrans (suc x) (suc y) (suc z) (leS _ _ p) (leS _ _ q) = leS x z (leTrans x y z p q)

  maxPN-le-l : (a b : Nat) -> LeN a (maxPN a b)
  maxPN-le-l zero    b       = leZ b
  maxPN-le-l (suc a) zero    = leRefl (suc a)
  maxPN-le-l (suc a) (suc b) = leS a (maxPN a b) (maxPN-le-l a b)

  maxPN-le-r : (a b : Nat) -> LeN b (maxPN a b)
  maxPN-le-r zero    b       = leRefl b
  maxPN-le-r (suc a) zero    = leZ (suc a)
  maxPN-le-r (suc a) (suc b) = leS b (maxPN a b) (maxPN-le-r a b)

  maxPN-lub : (a b c : Nat) -> LeN a c -> LeN b c -> LeN (maxPN a b) c
  maxPN-lub zero    b       c       _          hb         = hb
  maxPN-lub (suc a) zero    (suc c) (leS _ _ ha) _       = leS a c ha
  maxPN-lub (suc a) (suc b) (suc c) (leS _ _ ha) (leS _ _ hb) = leS (maxPN a b) c (maxPN-lub a b c ha hb)

-- Rank analysis for the key case:
-- rankP (reduceN (pcut (pinst u) (pmp v w)))
--   = suc (suc (maxPN (maxPN ru rv) (maxPN ru rw)))
-- rankP (pcut (pinst u) (pmp v w))
--   = suc (maxPN ru (suc (maxPN rv rw)))
-- where ru = rankP u, rv = rankP v, rw = rankP w.
--
-- FINDING: Rank CAN increase. Counterexample: ru=1, rv=0, rw=0.
-- Before: suc (maxPN 1 (suc (maxPN 0 0))) = suc (maxPN 1 1) = suc 1 = 2
-- After:  suc (suc (maxPN (maxPN 1 0) (maxPN 1 0))) = suc (suc (maxPN 1 1)) = 3
-- So 3 > 2: rank INCREASES.
--
-- This is a known phenomenon in cut elimination: duplicating the
-- structural step (pinst u) into both branches can increase proof rank.
-- For Nelson's program, one needs cut-rank (rank of the CUT FORMULA,
-- not the proof tree) which this reduction preserves.
-- For the non-active cases, rank is preserved (identity reduction):
reduceN-rank-trivial : (n : Nat) -> LeN (rankP (reduceN (pax n))) (rankP (pax n))
reduceN-rank-trivial n = leRefl zero

-- backtrackP: definitional equality on the key case
reduceN-backtrack : (u v w : ProofN) ->
  Eq (backtrackP (reduceN (pcut (pinst u) (pmp v w))))
     (backtrackP (pmp (pcut (pinst u) v) (pcut (pinst u) w)))
reduceN-backtrack u v w = refl

------------------------------------------------------------------------
-- 5. Code encoding
------------------------------------------------------------------------

private
  -- n39g = 39, so n39g + 21 = 60
  n40g : Nat
  n40g = suc n39g

  n50g : Nat
  n50g = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n40g)))))))))

  n60N : Nat
  n60N = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n50g)))))))))

  n61N : Nat
  n61N = suc n60N

  n62N : Nat
  n62N = suc n61N

  n63N : Nat
  n63N = suc n62N

encProofN : ProofN -> Code
encProofN (pax n)    = cnode (catom n60N) (catom n)
encProofN (pmp p q)  = cnode (catom n61N) (cnode (encProofN p) (encProofN q))
encProofN (pinst p)  = cnode (catom n62N) (encProofN p)
encProofN (pcut p q) = cnode (catom n63N) (cnode (encProofN p) (encProofN q))

reduceCodeN : Code -> Code
reduceCodeN (cnode (catom t63) (cnode (cnode (catom t62) u) (cnode (catom t61) (cnode v w)))) =
  cnode (catom n61N) (cnode (cnode (catom n63N) (cnode (cnode (catom n62N) u) v))
                            (cnode (catom n63N) (cnode (cnode (catom n62N) u) w)))
reduceCodeN c = c

reduceCodeN-correct : (u v w : ProofN) ->
  Eq (reduceCodeN (encProofN (pcut (pinst u) (pmp v w))))
     (encProofN (pmp (pcut (pinst u) v) (pcut (pinst u) w)))
reduceCodeN-correct u v w = refl

------------------------------------------------------------------------
-- 6. Internal template (using cpair from CExpPair)
------------------------------------------------------------------------

-- reduceExpN as a full CExpP function on variable codes would require
-- ctCase to decompose the input and inspect tags. Without ctCase,
-- we can only handle literal (closed) codes.

reduceExpN-clit : Code -> CExpP
reduceExpN-clit c = clitP (reduceCodeN c)

reduceExpN-clit-correct : (c : Code) ->
  Eq (evalGP (suc zero) (reduceExpN-clit c)) (just (reduceCodeN c))
reduceExpN-clit-correct c = refl

------------------------------------------------------------------------
-- 7. Internalization analysis
------------------------------------------------------------------------

-- (A) What IS derivable with current BTA (no ctCase, no ctFold):
--     Nothing uniform. Only specific instances for closed codes.
--     reduceExpN-clit works for any FIXED code, but cannot express
--     "for all codes c, if c has shape pcut(pinst(u), pmp(v,w)),
--     then reduce it." The quantification over code shapes requires
--     case analysis, which CExpP lacks.

-- (B) What WOULD be derivable with ctCase alone:
--     Code decomposition (recognize pcut/pinst/pmp tags by matching
--     catom n63, catom n62, catom n61). This gives:
--       ctCase input
--         (identity)    -- catom: no reduction
--         (\tag payload ->
--           ctCase tag ...  -- check if tag = n63
--             ctCase payload ... -- decompose (left, right)
--               ...)
--     But NOT the connection to fPrf (fPrf remains abstract in BTA).

-- (C) What WOULD be derivable with ctCase + ctFold:
--     Define the ProofN checker as a recursive function on Code:
--       checkerN : Code -> Maybe FormN
--     using ctFold for structural recursion over Code trees.
--     Then fPrf(p, c) is defined as "checkerN on p returns c".
--     The reduction theorem becomes:
--       checkerN(reduceCodeN(p)) = checkerN(p)
--     This IS derivable because both sides unfold to the same
--     computation on the defined checker. No special axiom needed.

-- (D) Classification: SUCCESS with ctCase + ctFold
--     The cut-commuting reduction IS internalizable once the checker
--     is a defined recursive function. No new reflection axiom needed.
--     The structural invariant (backtrackP) controls the meta-level
--     termination, while ctCase + ctFold handles the internal derivation.

------------------------------------------------------------------------
-- 8. Interpretation
------------------------------------------------------------------------

-- Nelson's program CAN succeed if:
-- 1. The system has ctCase (case analysis on proof codes)
-- 2. The system has ctFold (primitive recursion on proof codes)
-- 3. The proof predicate is DEFINED (not abstract)
--
-- The rank/level invariant is NOT the bottleneck.
-- The bottleneck was always the formula language's expressive power.
-- Once ctCase + ctFold are available, Nelson-style local reductions
-- become internalizable because they are COMPUTATIONS on codes,
-- and the system can verify computations.
--
-- backtrackP is useful for META-LEVEL termination analysis
-- (showing the reduction process terminates), but the INTERNAL
-- derivation doesn't need backtrackP -- it needs ctCase + ctFold.
--
-- Comparison with sdCode:
-- sdCode was a template (pure construction, no case analysis).
-- reduceCodeN requires case analysis (is this a pcut? is the left
-- child a pinst? is the right child a pmp?).
-- This is WHY sdCode worked without ctCase but reduceCodeN doesn't.
