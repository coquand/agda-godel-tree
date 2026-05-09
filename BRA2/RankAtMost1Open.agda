{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.RankAtMost1Open -- structural recursion skeleton for
-- DerivTBounded r l F (with r <= 1) into DerivT0 F, parametric in
-- the indBT and indBT2 elimination handlers.
--
-- T5-skeleton of the post-T3 plan in NEXT-SESSION-RANKDECREMENT.md.
--
-- Specification:
--
--   rankAtMost1ToOpen :
--     IndBTHandler ->
--     IndBT2Handler ->
--     {l F r} -> NatLE r 1 -> DerivTBounded r l F -> DerivT0 F
--
-- The handlers receive the indBT premises already lifted to DerivT0
-- (via rankZero, since at the topmost indBT in a rank-<=1 derivation,
-- the inner premises are necessarily at rank 0).  Their semantic
-- content is the ACTUAL indBT-elimination work; this module supplies
-- the structural-recursion bookkeeping around them.
--
-- Composition with T3:  for derivations whose conclusion is bot,
-- the bot-specific handler "return base directly" (since substEq is
-- identity on bot's closed equation) plus this skeleton gives a
-- fully-internal proof of  DerivTBounded 1 l bot -> DerivT0 bot
-- via the find-and-replace strategy.
--
-- Open: the indBT handlers themselves (semantic-soundness work).

module BRA2.RankAtMost1Open where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivTBounded using (DerivTBounded ; natMax)
open import BRA2.NatMaxLemmas
open import BRA2.RankDecrementSymTrans using (natMaxLE_split)
open import BRA2.BoundedReductionRankZero using (rankZero)

------------------------------------------------------------------------
-- NatLE n 0 implies n = 0.  Used to extract  natMax r1 r2 = 0  from
-- the rank constraint at indBT / indBT2 cases.

natLE_zero_eq : {n : Nat} -> NatLE n zero -> Eq n zero
natLE_zero_eq (leZero zero) = refl

------------------------------------------------------------------------
-- Handler signatures.
--
-- IndBTHandler : given indBT premises at DerivT0, produce DerivT0 of
-- the conclusion (atomic e).  This is the eliminator's actual
-- semantic content.

IndBTHandler : Set
IndBTHandler =
  (e : Equation) (v1 v2 : Nat) ->
  O.DerivT0 (atomic (substEq zero O e)) ->
  O.DerivT0 ((atomic (substEq zero (var v1) e))
             imp ((atomic (substEq zero (var v2) e))
                  imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
  O.DerivT0 (atomic e)

IndBT2Handler : Set
IndBT2Handler =
  (e : Equation) (v1 v2 v3 v4 : Nat) ->
  O.DerivT0 (atomic (substEq (suc zero) O (substEq zero O e))) ->
  O.DerivT0 ((atomic (substEq (suc zero) (var v3) (substEq zero O e)))
             imp ((atomic (substEq (suc zero) (var v4) (substEq zero O e)))
                  imp (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                                    (substEq zero O e))))) ->
  O.DerivT0 ((atomic (substEq (suc zero) O (substEq zero (var v1) e)))
             imp ((atomic (substEq (suc zero) O (substEq zero (var v2) e)))
                  imp (atomic (substEq (suc zero) O
                                                  (substEq zero (ap2 Pair (var v1) (var v2)) e))))) ->
  O.DerivT0 ((atomic (substEq (suc zero) (var v3) (substEq zero (var v1) e)))
             imp ((atomic (substEq (suc zero) (var v4) (substEq zero (var v2) e)))
                  imp (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                                    (substEq zero (ap2 Pair (var v1) (var v2)) e))))) ->
  O.DerivT0 (atomic e)

------------------------------------------------------------------------
-- The skeleton.

rankAtMost1ToOpen :
  IndBTHandler ->
  IndBT2Handler ->
  {l : Nat} {F : Formula} {r : Nat} ->
  NatLE r (suc zero) ->
  DerivTBounded r l F ->
  O.DerivT0 F

-- ----- atomic computation axioms (rank-polymorphic) -----
rankAtMost1ToOpen _ _ _ (B.axIB _ _ t)              = O.axI t
rankAtMost1ToOpen _ _ _ (B.axFstB _ _ a b)          = O.axFst a b
rankAtMost1ToOpen _ _ _ (B.axSndB _ _ a b)          = O.axSnd a b
rankAtMost1ToOpen _ _ _ (B.axFstLfB _ _)            = O.axFstLf
rankAtMost1ToOpen _ _ _ (B.axSndLfB _ _)            = O.axSndLf
rankAtMost1ToOpen _ _ _ (B.axConstB _ _ a b)        = O.axConst a b
rankAtMost1ToOpen _ _ _ (B.axCompB _ _ f g t)       = O.axComp f g t
rankAtMost1ToOpen _ _ _ (B.axComp2B _ _ h f g t)    = O.axComp2 h f g t
rankAtMost1ToOpen _ _ _ (B.axLiftB _ _ f a b)       = O.axLift f a b
rankAtMost1ToOpen _ _ _ (B.axPostB _ _ f h a b)     = O.axPost f h a b
rankAtMost1ToOpen _ _ _ (B.axFanB _ _ h1 h2 h a b)  = O.axFan h1 h2 h a b
rankAtMost1ToOpen _ _ _ (B.axZB _ _ x)              = O.axZ x
rankAtMost1ToOpen _ _ _ (B.axTreeRecLfB _ _ f s p)         = O.axTreeRecLf f s p
rankAtMost1ToOpen _ _ _ (B.axTreeRecNdB _ _ f s p a b)     = O.axTreeRecNd f s p a b
rankAtMost1ToOpen _ _ _ (B.axIfLfLB _ _ a b)        = O.axIfLfL a b
rankAtMost1ToOpen _ _ _ (B.axIfLfNB _ _ x y a b)    = O.axIfLfN x y a b
rankAtMost1ToOpen _ _ _ (B.axIfLfLLB _ _)           = O.axIfLfLL
rankAtMost1ToOpen _ _ _ (B.axIfLfNLB _ _ x y)       = O.axIfLfNL x y
rankAtMost1ToOpen _ _ _ (B.axTreeEqLLB _ _)         = O.axTreeEqLL
rankAtMost1ToOpen _ _ _ (B.axTreeEqLNB _ _ a b)     = O.axTreeEqLN a b
rankAtMost1ToOpen _ _ _ (B.axTreeEqNLB _ _ a b)     = O.axTreeEqNL a b
rankAtMost1ToOpen _ _ _ (B.axTreeEqNNB _ _ a1 a2 b1 b2) = O.axTreeEqNN a1 a2 b1 b2
rankAtMost1ToOpen _ _ _ (B.axGoodsteinB _ _ a b)    = O.axGoodstein a b
rankAtMost1ToOpen _ _ _ (B.axReflB _ _ t)           = O.axRefl t

-- ----- equational structural rules -----
rankAtMost1ToOpen h1 h2 le (B.ruleSymB d) =
  O.ruleSym (rankAtMost1ToOpen h1 h2 le d)
rankAtMost1ToOpen h1 h2 le (B.ruleTransB {r1} {_} {r2} d1 d2) =
  let lePair = natMaxLE_split {r1} {r2} le
  in O.ruleTrans (rankAtMost1ToOpen h1 h2 (fst lePair) d1)
                  (rankAtMost1ToOpen h1 h2 (snd lePair) d2)
rankAtMost1ToOpen h1 h2 le (B.cong1B f d) =
  O.cong1 f (rankAtMost1ToOpen h1 h2 le d)
rankAtMost1ToOpen h1 h2 le (B.congLB g x d) =
  O.congL g x (rankAtMost1ToOpen h1 h2 le d)
rankAtMost1ToOpen h1 h2 le (B.congRB g x d) =
  O.congR g x (rankAtMost1ToOpen h1 h2 le d)

-- ----- equational implication axioms (rank-polymorphic) -----
rankAtMost1ToOpen _ _ _ (B.axEqTransB _ _ a b c)    = O.axEqTrans a b c
rankAtMost1ToOpen _ _ _ (B.axEqCong1B _ _ f a b)    = O.axEqCong1 f a b
rankAtMost1ToOpen _ _ _ (B.axEqCongLB _ _ g a b c)  = O.axEqCongL g a b c
rankAtMost1ToOpen _ _ _ (B.axEqCongRB _ _ g a b c)  = O.axEqCongR g a b c

-- ----- propositional axioms (rank-polymorphic) -----
rankAtMost1ToOpen _ _ _ (B.axKB _ _ P Q)            = O.axK P Q
rankAtMost1ToOpen _ _ _ (B.axSB _ _ P Q R)          = O.axS P Q R
rankAtMost1ToOpen _ _ _ (B.axNegB _ _ P Q)          = O.axNeg P Q

-- ----- rules of inference -----
rankAtMost1ToOpen h1 h2 le (B.mpB {r1} {_} {r2} d1 d2) =
  let lePair = natMaxLE_split {r1} {r2} le
  in O.mp (rankAtMost1ToOpen h1 h2 (fst lePair) d1)
          (rankAtMost1ToOpen h1 h2 (snd lePair) d2)
rankAtMost1ToOpen h1 h2 le (B.ruleInstB x t d) =
  O.ruleInst x t (rankAtMost1ToOpen h1 h2 le d)

-- ----- indBT cases: extract that inner ranks are zero, lift to
-- ----- DerivT0, dispatch to handler -----
rankAtMost1ToOpen handleIndBT _ (leSuc le')
                  (B.indBTB {r1} {l1} {r2} {l2} e v1 v2 base step) =
  let -- le' : NatLE (natMax r1 r2) zero  =>  natMax r1 r2 = 0  =>  r1 = r2 = 0.
      maxEqZ : Eq (natMax r1 r2) zero
      maxEqZ = natLE_zero_eq le'
      pair      = natMaxZero r1 r2 maxEqZ
      r1Eq0   = fst pair
      r2Eq0   = snd pair
      -- transport base, step to rank zero:
      baseAt0 : DerivTBounded zero l1 (atomic (substEq zero O e))
      baseAt0 = eqSubst (\ rk -> DerivTBounded rk l1 (atomic (substEq zero O e)))
                          r1Eq0 base
      stepAt0 : DerivTBounded zero l2
                   ((atomic (substEq zero (var v1) e))
                    imp ((atomic (substEq zero (var v2) e))
                         imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e))))
      stepAt0 = eqSubst (\ rk -> DerivTBounded rk l2 _) r2Eq0 step
      -- lift to DerivT0 and dispatch.
  in handleIndBT e v1 v2 (rankZero baseAt0) (rankZero stepAt0)

rankAtMost1ToOpen _ handleIndBT2 (leSuc le')
                  (B.indBT2B {r1} {l1} {r2} {l2} {r3} {l3} {r4} {l4}
                              e v1 v2 v3 v4 b1 b2 b3 b4) =
  let -- le' : NatLE (natMax (natMax r1 r2) (natMax r3 r4)) zero
      eqOuter : Eq (natMax (natMax r1 r2) (natMax r3 r4)) zero
      eqOuter = natLE_zero_eq le'
      pairOuter = natMaxZero (natMax r1 r2) (natMax r3 r4) eqOuter
      eq12 = fst pairOuter   -- natMax r1 r2 = 0
      eq34 = snd pairOuter   -- natMax r3 r4 = 0
      pair12 = natMaxZero r1 r2 eq12
      pair34 = natMaxZero r3 r4 eq34
      r1Eq0 = fst pair12
      r2Eq0 = snd pair12
      r3Eq0 = fst pair34
      r4Eq0 = snd pair34
      b1At0  = eqSubst (\ rk -> DerivTBounded rk l1 _) r1Eq0 b1
      b2At0  = eqSubst (\ rk -> DerivTBounded rk l2 _) r2Eq0 b2
      b3At0  = eqSubst (\ rk -> DerivTBounded rk l3 _) r3Eq0 b3
      b4At0  = eqSubst (\ rk -> DerivTBounded rk l4 _) r4Eq0 b4
  in handleIndBT2 e v1 v2 v3 v4
       (rankZero b1At0) (rankZero b2At0) (rankZero b3At0) (rankZero b4At0)

------------------------------------------------------------------------
-- Specialisation: input rank exactly 1.

rankAt1ToOpen :
  IndBTHandler ->
  IndBT2Handler ->
  {l : Nat} {F : Formula} ->
  DerivTBounded (suc zero) l F ->
  O.DerivT0 F
rankAt1ToOpen h1 h2 d = rankAtMost1ToOpen h1 h2 (natLERefl (suc zero)) d
