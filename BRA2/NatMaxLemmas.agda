{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.NatMaxLemmas -- elementary lemmas about  natMax  (the binary
-- max on Nat used as the rank/level combiner in DerivTBounded).
--
-- These are infrastructure for the eventual proof of  RankDecrement
-- (the bounded cut-elimination step).  In a rank-induction descent
-- through a bounded derivation, we repeatedly need to:
--   * conclude  natMax a b = 0  implies  a = 0  and  b = 0
--   * conclude  natMax a b = suc r  splits into the cases where the
--     max is realised by either side
--   * commute, associate, and idempotently absorb  natMax  arguments
--
-- The lemmas in this file are stated in terms of  natMax  as defined
-- in BRA2.DerivTBounded so the eventual proof can use them directly.

module BRA2.NatMaxLemmas where

open import BRA2.Base
open import BRA2.NatMax using (natMax)

------------------------------------------------------------------------
-- Decomposition of  natMax  at zero.
--
-- natMax a b = 0  iff  a = 0  and  b = 0 .

natMaxZero :
  (a b : Nat) ->
  Eq (natMax a b) zero ->
  Sigma (Eq a zero) (\ _ -> Eq b zero)
natMaxZero zero    zero    refl = mkSigma refl refl
natMaxZero (suc _) zero    ()
natMaxZero (suc _) (suc _) ()

------------------------------------------------------------------------
-- Idempotency:  natMax a a = a .

natMaxIdem : (a : Nat) -> Eq (natMax a a) a
natMaxIdem zero    = refl
natMaxIdem (suc a) = eqCong suc (natMaxIdem a)

------------------------------------------------------------------------
-- Right unit:  natMax a 0 = a .  (Left unit  natMax 0 a = a  is
-- definitional in the BRA2.DerivTBounded definition.)

natMaxRightZero : (a : Nat) -> Eq (natMax a zero) a
natMaxRightZero zero    = refl
natMaxRightZero (suc a) = refl

------------------------------------------------------------------------
-- Commutativity:  natMax a b = natMax b a .

natMaxComm : (a b : Nat) -> Eq (natMax a b) (natMax b a)
natMaxComm zero    zero    = refl
natMaxComm zero    (suc b) = refl
natMaxComm (suc a) zero    = refl
natMaxComm (suc a) (suc b) = eqCong suc (natMaxComm a b)

------------------------------------------------------------------------
-- Associativity:  natMax (natMax a b) c = natMax a (natMax b c) .

natMaxAssoc :
  (a b c : Nat) ->
  Eq (natMax (natMax a b) c) (natMax a (natMax b c))
natMaxAssoc zero    b       c       = refl
natMaxAssoc (suc a) zero    c       = refl
natMaxAssoc (suc a) (suc b) zero    = refl
natMaxAssoc (suc a) (suc b) (suc c) = eqCong suc (natMaxAssoc a b c)

------------------------------------------------------------------------
-- Bound by either side.  These are the key "rank does not decrease"
-- lemmas: each input's rank is bounded by the combined rank.
--
-- Stated as a propositional inequality  natLE : Nat -> Nat -> Set
-- (defined locally; the codebase otherwise uses Bool comparisons).

data NatLE : Nat -> Nat -> Set where
  leZero : (n : Nat) -> NatLE zero n
  leSuc  : {a b : Nat} -> NatLE a b -> NatLE (suc a) (suc b)

natLERefl : (a : Nat) -> NatLE a a
natLERefl zero    = leZero zero
natLERefl (suc a) = leSuc (natLERefl a)

natLETrans : {a b c : Nat} -> NatLE a b -> NatLE b c -> NatLE a c
natLETrans (leZero _)  q          = leZero _
natLETrans (leSuc p)   (leSuc q)  = leSuc (natLETrans p q)

natMaxLE_L : (a b : Nat) -> NatLE a (natMax a b)
natMaxLE_L zero    b       = leZero (natMax zero b)
natMaxLE_L (suc a) zero    = leSuc (natLERefl a)
natMaxLE_L (suc a) (suc b) = leSuc (natMaxLE_L a b)

natMaxLE_R : (a b : Nat) -> NatLE b (natMax a b)
natMaxLE_R a b =
  let pComm = natMaxComm b a
      pL    = natMaxLE_L b a
  in eqSubst (\ z -> NatLE b z) pComm pL

------------------------------------------------------------------------
-- Decomposition of  natMax = suc r .
--
-- If  natMax a b = suc r , then either  a = suc a'  or  b = suc b'
-- (or both).  This case-split is needed when descending through
-- binary combiners (mp, ruleTrans) in a rank-(suc r) derivation:
-- at least one premise contributes the rank.

data MaxSucEvidence (a b r : Nat) : Set where
  maxFromLeft  :
    (a' : Nat) -> Eq a (suc a') -> NatLE a' r -> NatLE b (suc r) ->
    MaxSucEvidence a b r
  maxFromRight :
    (b' : Nat) -> Eq b (suc b') -> NatLE b' r -> NatLE a (suc r) ->
    MaxSucEvidence a b r

natMaxSucDecompose :
  (a b r : Nat) ->
  Eq (natMax a b) (suc r) ->
  MaxSucEvidence a b r
natMaxSucDecompose zero zero _ ()
natMaxSucDecompose zero (suc b) r eq =
  maxFromRight b refl
    (eqSubst (\ z -> NatLE b z) (eqCong predNat eq) (natLERefl b))
    (leZero (suc r))
  where
    predNat : Nat -> Nat
    predNat zero    = zero
    predNat (suc n) = n
natMaxSucDecompose (suc a) zero r eq =
  maxFromLeft a refl
    (eqSubst (\ z -> NatLE a z) (eqCong predNat eq) (natLERefl a))
    (leZero (suc r))
  where
    predNat : Nat -> Nat
    predNat zero    = zero
    predNat (suc n) = n
natMaxSucDecompose (suc a) (suc b) zero eq =
  let pq = natMaxZero a b (eqCong predNat eq)
      pa = fst pq
      pb = snd pq
  in maxFromLeft a refl
       (eqSubst (\ z -> NatLE z zero) (eqSym pa) (leZero zero))
       (eqSubst (\ z -> NatLE (suc z) (suc zero)) (eqSym pb) (leSuc (leZero zero)))
  where
    predNat : Nat -> Nat
    predNat zero    = zero
    predNat (suc n) = n
natMaxSucDecompose (suc a) (suc b) (suc r) eq =
  liftEvidence (natMaxSucDecompose a b r (eqCong predNat eq))
  where
    predNat : Nat -> Nat
    predNat zero    = zero
    predNat (suc n) = n
    liftEvidence : MaxSucEvidence a b r ->
                   MaxSucEvidence (suc a) (suc b) (suc r)
    liftEvidence (maxFromLeft a' refl ihA ihB) =
      maxFromLeft (suc a') refl (leSuc ihA) (leSuc ihB)
    liftEvidence (maxFromRight b' refl ihB ihA) =
      maxFromRight (suc b') refl (leSuc ihB) (leSuc ihA)
