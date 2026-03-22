{-# OPTIONS --without-K --exact-split #-}

-- NelsonReduction.agda
-- Nelson-style reduction on Code, controlled by backtrackP.
-- No proof checker. Explores: can proof dynamics exist without semantics?

module NelsonReduction where

open import ChwistekSyntax

------------------------------------------------------------------------
-- Local definitions
------------------------------------------------------------------------

private
  data Bool : Set where
    true  : Bool
    false : Bool

  eqNat : Nat -> Nat -> Bool
  eqNat zero    zero    = true
  eqNat zero    (suc _) = false
  eqNat (suc _) zero    = false
  eqNat (suc n) (suc m) = eqNat n m

  eqNat-refl : (n : Nat) -> Eq (eqNat n n) true
  eqNat-refl zero    = refl
  eqNat-refl (suc n) = eqNat-refl n

  maxN : Nat -> Nat -> Nat
  maxN zero    m       = m
  maxN (suc n) zero    = suc n
  maxN (suc n) (suc m) = suc (maxN n m)

------------------------------------------------------------------------
-- Tag constants: n60=pax, n61=pmp, n62=pinst, n63=pcut
------------------------------------------------------------------------

private
  n50 : Nat
  n50 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
        zero)))))))))))))))))))))))))))))))))))))))))))))))))

  n60 : Nat
  n60 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n50)))))))))

  n61 : Nat
  n61 = suc n60

  n62 : Nat
  n62 = suc n61

  n63 : Nat
  n63 = suc n62

------------------------------------------------------------------------
-- 1. backtrackP on Code (structural recursion, tag dispatch)
------------------------------------------------------------------------

private
  btPayload : Nat -> Code -> Nat
  btCode : Code -> Nat

  btBinary : Code -> Nat
  btBinary (cnode l r) = suc (maxN (btCode l) (btCode r))
  btBinary (catom _)   = zero

  btPayload tag payload = btH0 (eqNat tag n60) tag payload
    where
    btH0 : Bool -> Nat -> Code -> Nat
    btH0 true _ _ = zero
    btH0 false t2 p2 = btH1 (eqNat t2 n62) t2 p2
      where
      btH1 : Bool -> Nat -> Code -> Nat
      btH1 true _ p = btCode p
      btH1 false t3 p3 = btH2 (eqNat t3 n61) t3 p3
        where
        btH2 : Bool -> Nat -> Code -> Nat
        btH2 true _ p = btBinary p
        btH2 false t4 p4 = btH3 (eqNat t4 n63) p4
          where
          btH3 : Bool -> Code -> Nat
          btH3 true p = btBinary p
          btH3 false _ = zero

  btCode (catom _) = zero
  btCode (cnode (catom tag) payload) = btPayload tag payload
  btCode (cnode (cnode _ _) _) = zero

backtrackP : Code -> Nat
backtrackP = btCode

------------------------------------------------------------------------
-- 2. One-step reduction: reduceCode
------------------------------------------------------------------------

-- pcut(pinst(u), pmp(v, w)) -> pmp(pcut(pinst(u), v), pcut(pinst(u), w))
-- All other codes: identity.

private
  mkReduced : Code -> Code -> Code -> Code
  mkReduced u v w =
    cnode (catom n61)
      (cnode (cnode (catom n63) (cnode (cnode (catom n62) u) v))
             (cnode (catom n63) (cnode (cnode (catom n62) u) w)))

  tryPmp : Code -> Code -> Code -> Code
  tryPmpTag : Bool -> Code -> Code -> Code -> Code

  tryPmp orig u (cnode (catom rtag) rp) = tryPmpTag (eqNat rtag n61) orig u rp
  tryPmp orig _ (catom _) = orig
  tryPmp orig _ (cnode (cnode _ _) _) = orig

  tryPmpTag true _ u (cnode v w) = mkReduced u v w
  tryPmpTag true orig _ (catom _) = orig
  tryPmpTag false orig _ _ = orig

  tryPinst : Code -> Code -> Code -> Code
  tryPinstTag : Bool -> Code -> Code -> Code -> Code

  tryPinst orig (cnode (catom lt) lp) right =
    tryPinstTag (eqNat lt n62) orig lp right
  tryPinst orig (catom _) _ = orig
  tryPinst orig (cnode (cnode _ _) _) _ = orig

  tryPinstTag true _ u right =
    tryPmp (cnode (catom n63) (cnode (cnode (catom n62) u) right)) u right
  tryPinstTag false orig _ _ = orig

  tryCut : Code -> Code
  tryCutTag : Bool -> Code -> Nat -> Code -> Code

  tryCut (catom n) = catom n
  tryCut (cnode (catom tag) pl) =
    tryCutTag (eqNat tag n63) (cnode (catom tag) pl) tag pl
  tryCut (cnode (cnode a b) pl) = cnode (cnode a b) pl

  tryCutTag true orig _ (cnode left right) = tryPinst orig left right
  tryCutTag true orig _ (catom _) = orig
  tryCutTag false orig _ _ = orig

reduceCode : Code -> Code
reduceCode = tryCut

------------------------------------------------------------------------
-- 3. LeN (less-or-equal on Nat)
------------------------------------------------------------------------

data LeN : Nat -> Nat -> Set where
  leZ : {m : Nat} -> LeN zero m
  leS : {n m : Nat} -> LeN n m -> LeN (suc n) (suc m)

private
  leRefl : (n : Nat) -> LeN n n
  leRefl zero    = leZ
  leRefl (suc n) = leS (leRefl n)

  leTrans : {x y z : Nat} -> LeN x y -> LeN y z -> LeN x z
  leTrans leZ       _         = leZ
  leTrans (leS p)   (leS q)   = leS (leTrans p q)

  maxN-le-l : (a b : Nat) -> LeN a (maxN a b)
  maxN-le-l zero    b       = leZ
  maxN-le-l (suc a) zero    = leRefl (suc a)
  maxN-le-l (suc a) (suc b) = leS (maxN-le-l a b)

  maxN-le-r : (a b : Nat) -> LeN b (maxN a b)
  maxN-le-r zero    b       = leRefl b
  maxN-le-r (suc a) zero    = leZ
  maxN-le-r (suc a) (suc b) = leS (maxN-le-r a b)

  maxN-lub : {a b c : Nat} -> LeN a c -> LeN b c -> LeN (maxN a b) c
  maxN-lub {zero}  {b}     leZ       hb       = hb
  maxN-lub {suc a} {zero}  ha        leZ       = ha
  maxN-lub {suc a} {suc b} (leS ha)  (leS hb) = leS (maxN-lub ha hb)

------------------------------------------------------------------------
-- 4. backtrackP analysis
------------------------------------------------------------------------

-- Identity cases: reduceCode c = c, so backtrackP trivially preserved.
reduceCode-id-atom : (n : Nat) -> Eq (reduceCode (catom n)) (catom n)
reduceCode-id-atom n = refl

reduceCode-id-nested : (a b c : Code) ->
  Eq (reduceCode (cnode (cnode a b) c)) (cnode (cnode a b) c)
reduceCode-id-nested a b c = refl

-- Active case analysis (computed at meta-level):
--   Before: suc(max(btCode u, suc(max(btCode v, btCode w))))
--   After:  suc(suc(max(max(btCode u, btCode v), max(btCode u, btCode w))))
-- These differ when btCode u > max(btCode v, btCode w).
-- Example: u with btCode 2, v,w with btCode 0 => before=3, after=4.
-- So backtrackP can INCREASE under Code-level reduction.
-- (At the typed ProofN level it was preserved by refl -- the gap is
-- because the tag-dispatch encoding breaks direct structural correspondence.)

------------------------------------------------------------------------
-- 5. Bounded fragment BT_k
------------------------------------------------------------------------

BT : Nat -> Code -> Set
BT k c = LeN (backtrackP c) k

------------------------------------------------------------------------
-- 6. Iterated reduction
------------------------------------------------------------------------

iterReduce : Nat -> Code -> Code
iterReduce zero    c = c
iterReduce (suc n) c = iterReduce n (reduceCode c)

------------------------------------------------------------------------
-- 7. The Critical Question: Termination Without a Checker
------------------------------------------------------------------------

-- Can iterReduce eventually reach a normal form (reduceCode c = c)
-- WITHOUT a proof checker?
--
-- (1) backtrackP: NOT a termination measure (can increase at Code level).
-- (2) sizeP: NOT a termination measure (reduction duplicates pinst u).
-- (3) Active redex count: WOULD decrease (each step eliminates one
--     pcut(pinst,pmp) but new pcuts have simpler right children).
--     But counting active redexes requires recognizing proof structure
--     = defining a (partial) checker.
--
-- CONCLUSION: Termination requires semantic analysis of proof structure.

------------------------------------------------------------------------
-- 8. Separation Verdict
------------------------------------------------------------------------

-- Does backtrackP-controlled reduction collapse into checker semantics?
--
-- PARTIALLY. Nelson's program splits at the termination boundary:
--
-- (A) Reduction dynamics: STRUCTURAL
--     reduceCode is pure pattern matching on Code trees.
--     backtrackP is a structural measure. No semantics needed.
--
-- (B) Termination/confluence: SEMANTIC
--     Proving termination needs a decreasing measure on proof structure,
--     requiring recognition and counting of active redexes.
--     This is equivalent to defining a partial proof checker.
--
-- (C) Bounded iteration: STRUCTURAL
--     iterReduce n c applies reduceCode n times. No semantic content.
--
-- (D) Termination guarantee: SEMANTIC
--     Proving existence of n with iterReduce n c in normal form
--     needs active-redex analysis = checker-like reasoning.
--
-- ADDITIONAL OBSERVATION (Code vs ProofN):
-- At the typed ProofN level, backtrackP is exactly preserved (by refl).
-- At the untyped Code level, backtrackP can increase because tag dispatch
-- breaks direct structural correspondence. This gap is itself a form of
-- the semantic/structural divide: typed levels "know" tags are consistent.
