{-# OPTIONS --without-K --exact-split #-}

-- StructuredCode.agda
-- Experiment: middle layer between raw Code and typed ProofN.
-- Tests whether a structural shape predicate on Code recovers
-- backtrackP preservation under cut-commuting reduction.

module StructuredCode where

open import ChwistekSyntax
open import ChwistekGodel2Genuine

------------------------------------------------------------------------
-- Tag constants: n60=pax, n61=pmp, n62=pinst, n63=pcut
------------------------------------------------------------------------

n60 : Nat
n60 = suc n39g

n61 : Nat
n61 = suc n60

n62 : Nat
n62 = suc n61

n63 : Nat
n63 = suc n62

------------------------------------------------------------------------
-- 1. Structured : Code -> Set
------------------------------------------------------------------------

-- Recognizes codes with valid proof-tree shape (tags only).
-- WEAKER than a checker: no formula well-typedness, no mp matching.

data Structured : Code -> Set where
  sAx   : (k : Nat) -> Structured (cnode (catom n60) (catom k))
  sMp   : {c1 c2 : Code} -> Structured c1 -> Structured c2 ->
           Structured (cnode (catom n61) (cnode c1 c2))
  sInst : {c : Code} -> Structured c ->
           Structured (cnode (catom n62) c)
  sCut  : {c1 c2 : Code} -> Structured c1 -> Structured c2 ->
           Structured (cnode (catom n63) (cnode c1 c2))

------------------------------------------------------------------------
-- 2. backtrackS : Structured c -> Nat
------------------------------------------------------------------------

private
  maxN : Nat -> Nat -> Nat
  maxN zero    m       = m
  maxN (suc n) zero    = suc n
  maxN (suc n) (suc m) = suc (maxN n m)

backtrackS : {c : Code} -> Structured c -> Nat
backtrackS (sAx _)      = zero
backtrackS (sInst s)    = backtrackS s
backtrackS (sMp s1 s2)  = suc (maxN (backtrackS s1) (backtrackS s2))
backtrackS (sCut s1 s2) = suc (maxN (backtrackS s1) (backtrackS s2))

-- This matches ProofN's backtrackP exactly (by construction).

------------------------------------------------------------------------
-- 3. Reduction on Structured proofs
------------------------------------------------------------------------

-- Direct structural reduction on Structured values.
-- pcut(pinst(u), pmp(v,w)) -> pmp(pcut(pinst(u),v), pcut(pinst(u),w))
-- All other shapes: identity (returned as-is).
--
-- Returns a dependent pair (Code, Structured) because the active
-- redex changes the underlying Code.

private
  data SigmaS (A : Set) (B : A -> Set) : Set where
    mkSigS : (x : A) -> B x -> SigmaS A B

  fstSS : {A : Set} {B : A -> Set} -> SigmaS A B -> A
  fstSS (mkSigS x _) = x

  sndSS : {A : Set} {B : A -> Set} -> (p : SigmaS A B) -> B (fstSS p)
  sndSS (mkSigS _ b) = b

ReducedS : {c : Code} -> Structured c -> SigmaS Code Structured
ReducedS (sCut (sInst su) (sMp sv sw)) =
  mkSigS _ (sMp (sCut (sInst su) sv) (sCut (sInst su) sw))
ReducedS (sCut (sInst su) (sAx k))     = mkSigS _ (sCut (sInst su) (sAx k))
ReducedS (sCut (sInst su) (sInst sq))  = mkSigS _ (sCut (sInst su) (sInst sq))
ReducedS (sCut (sInst su) (sCut sq sr)) =
  mkSigS _ (sCut (sInst su) (sCut sq sr))
ReducedS (sCut (sAx n) sq)     = mkSigS _ (sCut (sAx n) sq)
ReducedS (sCut (sMp sa sb) sq) = mkSigS _ (sCut (sMp sa sb) sq)
ReducedS (sCut (sCut sa sb) sq) = mkSigS _ (sCut (sCut sa sb) sq)
ReducedS (sAx k)     = mkSigS _ (sAx k)
ReducedS (sMp s1 s2) = mkSigS _ (sMp s1 s2)
ReducedS (sInst s)   = mkSigS _ (sInst s)

-- KEY: ReducedS always returns a Structured value, proving that
-- reduction preserves the shape predicate. No tag dispatch needed
-- because Structured already guarantees valid tags.

------------------------------------------------------------------------
-- 4. backtrackS of the reduced proof
------------------------------------------------------------------------

backtrackReduced : {c : Code} -> (s : Structured c) -> Nat
backtrackReduced s = backtrackS (sndSS (ReducedS s))

------------------------------------------------------------------------
-- 5. Concrete counterexample: backtrackS INCREASES
------------------------------------------------------------------------

-- u = pmp(pax(0), pax(1)), backtrackS u = 1
-- v = pax(0), w = pax(0), backtrackS v = backtrackS w = 0
-- Before: sCut(sInst(u), sMp(v,w)), backtrackS = 2
-- After:  sMp(sCut(sInst(u),v), sCut(sInst(u),w)), backtrackS = 3

private
  exU : Structured (cnode (catom n61)
          (cnode (cnode (catom n60) (catom zero))
                 (cnode (catom n60) (catom (suc zero)))))
  exU = sMp (sAx zero) (sAx (suc zero))

  exV : Structured (cnode (catom n60) (catom zero))
  exV = sAx zero

  exW : Structured (cnode (catom n60) (catom zero))
  exW = sAx zero

  exBefore : Structured _
  exBefore = sCut (sInst exU) (sMp exV exW)

  exAfter : Structured _
  exAfter = sndSS (ReducedS exBefore)

-- backtrackS exBefore = 2 (verified by refl)
bt-before-eq : Eq (backtrackS exBefore) (suc (suc zero))
bt-before-eq = refl

-- backtrackS exAfter = 3 (verified by refl)
bt-after-eq : Eq (backtrackS exAfter) (suc (suc (suc zero)))
bt-after-eq = refl

-- VERIFIED: backtrackS goes from 2 to 3 under cut-commuting reduction.

------------------------------------------------------------------------
-- 6. Non-active cases: backtrackS trivially preserved
------------------------------------------------------------------------

bt-ax : (k : Nat) ->
  Eq (backtrackReduced (sAx k)) (backtrackS (sAx k))
bt-ax k = refl

bt-mp : {c1 c2 : Code} ->
  (s1 : Structured c1) -> (s2 : Structured c2) ->
  Eq (backtrackReduced (sMp s1 s2)) (backtrackS (sMp s1 s2))
bt-mp s1 s2 = refl

bt-inst : {c : Code} -> (s : Structured c) ->
  Eq (backtrackReduced (sInst s)) (backtrackS (sInst s))
bt-inst s = refl

bt-cut-ax : {c : Code} -> (s : Structured c) -> (k : Nat) ->
  Eq (backtrackReduced (sCut (sAx k) s))
     (backtrackS (sCut (sAx k) s))
bt-cut-ax s k = refl

bt-cut-mp : {c1 c2 c3 : Code} ->
  (s1 : Structured c1) -> (s2 : Structured c2) ->
  (s3 : Structured c3) ->
  Eq (backtrackReduced (sCut (sMp s1 s2) s3))
     (backtrackS (sCut (sMp s1 s2) s3))
bt-cut-mp s1 s2 s3 = refl

bt-cut-cut : {c1 c2 c3 : Code} ->
  (s1 : Structured c1) -> (s2 : Structured c2) ->
  (s3 : Structured c3) ->
  Eq (backtrackReduced (sCut (sCut s1 s2) s3))
     (backtrackS (sCut (sCut s1 s2) s3))
bt-cut-cut s1 s2 s3 = refl

bt-cut-inst-ax : {c : Code} -> (s : Structured c) -> (k : Nat) ->
  Eq (backtrackReduced (sCut (sInst s) (sAx k)))
     (backtrackS (sCut (sInst s) (sAx k)))
bt-cut-inst-ax s k = refl

bt-cut-inst-inst : {c1 c2 : Code} ->
  (s1 : Structured c1) -> (s2 : Structured c2) ->
  Eq (backtrackReduced (sCut (sInst s1) (sInst s2)))
     (backtrackS (sCut (sInst s1) (sInst s2)))
bt-cut-inst-inst s1 s2 = refl

bt-cut-inst-cut : {c1 c2 c3 : Code} ->
  (s1 : Structured c1) -> (s2 : Structured c2) ->
  (s3 : Structured c3) ->
  Eq (backtrackReduced (sCut (sInst s1) (sCut s2 s3)))
     (backtrackS (sCut (sInst s1) (sCut s2 s3)))
bt-cut-inst-cut s1 s2 s3 = refl

------------------------------------------------------------------------
-- 7. THE VERDICT
------------------------------------------------------------------------

-- FINDING: backtrackS (= backtrackP on structured codes) is NOT
-- preserved by cut-commuting reduction even on well-shaped proof
-- codes. The reduction genuinely increases interaction depth.
--
-- Concrete counterexample (verified by refl):
--   u = pmp(pax(0), pax(1))  =>  backtrackS u = 1
--   v = pax(0), w = pax(0)   =>  backtrackS v = backtrackS w = 0
--   Before: sCut(sInst(u), sMp(v,w))  =>  backtrackS = 2
--   After:  sMp(sCut(sInst(u),v), sCut(sInst(u),w))  =>  backtrackS = 3
--
-- This means:
-- - The typed ProofN result (reduceN-backtrack = refl in
--   NelsonCutCommute) showed DEFINITIONAL equality of LHS/RHS
--   expressions, NOT that backtrackP is preserved as a value.
--   The same increase happens on ProofN:
--   backtrackP(pmp(pcut(pinst u,v), pcut(pinst u,w)))
--     = suc(max(suc(max(bu,bv)), suc(max(bu,bw))))
--   which CAN exceed suc(max(bu, suc(max(bv,bw)))).
-- - The "typed vs raw" distinction is NOT the explanation for
--   the increase. Structured codes exhibit the same behavior.
--
-- REVISED CONCLUSION:
-- - backtrackP is NOT an invariant of cut-commuting reduction.
-- - Neither rank NOR backtrackP is preserved by this reduction.
-- - For termination, a DIFFERENT measure is needed (e.g., counting
--   active cut-pmp redexes, or multiset ordering on cut ranks).
--
-- WHAT SURVIVES of Nelson:
-- - Local reduction IS structural (no checker needed).
-- - The DYNAMICS are well-defined without semantics.
-- - But NO structural measure (rank, level, backtrackP) is preserved
--   as a non-increasing invariant by the cut-commuting step.
-- - Termination analysis must come from elsewhere.
