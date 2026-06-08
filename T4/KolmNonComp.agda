{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmNonComp -- non-computability of Kolmogorov complexity: THE CLASH CORE.
--
-- A total BRA function  Kf : Fun1  ( = a primitive-recursive, hence computable,
-- function )  cannot compute exact Kolmogorov complexity.  The Berry argument:
-- if it did, the program "search for the least x with Kf x > L and print it"
-- describes that x in  O(log L)  bits, while  Kf x > L  says its complexity
-- exceeds L -- impossible for large L.
--
-- This file isolates the MATHEMATICAL CORE -- the clash itself -- as a complete,
-- hole-free reduction:
--
--   nonComputable_clash :  Kf K-sound  ->  ( for some L : an incompressible-
--     above-L number bL that is nonetheless describable at level M <= L )
--     ->  Empty .
--
-- The remaining engineering ( producing such (bL, M) for large L from a runnable
-- bounded-search Berry program of size O(log L) -- bricks "berry program" +
-- "size O(log L)" + "exp beats linear" ) is the Chaitin-scale construction noted
-- in the headers; this core is what they feed.

module T4.KolmNonComp where

open import T4.Base
open import T4.EvalUCorrect  using ( evalN1 )
open import BRA3.RuleInst2    using ( NatLe )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltIrrefl )
open import T4.KolmCount     using ( Kle )
open import T4.KolmMono      using ( kle_mono ; ltLeTrans )

------------------------------------------------------------------------
-- "Kf is sound for K":  if x is describable within length L, then the value
-- Kf assigns it is <= L  ( Kf never over-estimates the complexity ).

KSound : Fun1 -> Set
KSound Kf = (L x : Nat) -> Kle L x -> NatLe (evalN1 Kf x) L

------------------------------------------------------------------------
-- THE CLASH.   bL is "incompressible above L"  (L < Kf bL)  yet describable
-- at some level  M <= L .  With Kf sound, that is contradictory.

nonComputable_clash :
  (Kf : Fun1) ->
  KSound Kf ->
  (L M bL : Nat) ->
  NatLe M L ->                 -- M <= L
  Lt L (evalN1 Kf bL) ->       -- Kf bL > L   (bL is incompressible above L)
  Kle M bL ->                  -- bL is describable within length M
  Empty
nonComputable_clash Kf kfSound L M bL leML ltLkf kleMbL =
  -- describable at M <= L  =>  describable at L  =>  Kf bL <= L  (soundness),
  -- contradicting  Kf bL > L .
  ltIrrefl (ltLeTrans ltLkf (kfSound L bL (kle_mono M L bL kleMbL leML)))
