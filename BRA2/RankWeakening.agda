{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.RankWeakening -- monotonicity of  DerivTBounded  in the rank
-- index.
--
-- weakenRank :
--   {l : Nat} {F : Formula} {r : Nat} (r' : Nat) ->
--   NatLE r r' ->
--   DerivTBounded r l F ->
--   DerivTBounded r' l F
--
-- "If F is provable at rank r, it is provable at any rank r' >= r."
-- The level index  l  is preserved.
--
-- Proof structure:
--   * Atomic axioms (rank-polymorphic, r is a constructor argument):
--     re-construct at rank  r' .
--   * Unary structural rules (ruleSymB, cong*, ruleInstB):
--     rank is preserved by the constructor; recurse on the inner
--     derivation with the same  NatLE  bound.
--   * Binary combiners (ruleTransB, mpB, natMax-on-rank):
--     split  NatLE (natMax r1 r2) r'  via  natMaxLE_split  into
--     NatLE r1 r' and NatLE r2 r' ; weaken each side to  r' ;
--     re-pack via the binary constructor; collapse  natMax r' r' = r'
--     via  natMaxIdem .
--   * indBT* (output rank suc (natMax ...)): pattern-match on the
--     NatLE bound to expose  r' = suc r''  with  le' : natMax ... ≤ r'' ;
--     weaken inner premises to  r'' ; re-pack via indBTB / indBT2B.
--
-- This module is foundational for the EXACT-rank formulation of
-- BoundedReduction.RankDecrement (where each ruleTransB / mpB case
-- weakens the non-rank-carrying side from  r2 ≤ suc r  to  r ).

module BRA2.RankWeakening where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivTBounded as B
open import BRA2.DerivTBounded using (DerivTBounded ; natMax)
open import BRA2.NatMaxLemmas
open import BRA2.RankDecrementSymTrans using (natMaxLE_split)

------------------------------------------------------------------------
-- The main lemma.

weakenRank :
  {l : Nat} {F : Formula} {r : Nat} (r' : Nat) ->
  NatLE r r' ->
  DerivTBounded r l F ->
  DerivTBounded r' l F

-- Atomic computation axioms (rank-polymorphic).
weakenRank r' _ (B.axIB _ l t)              = B.axIB r' l t
weakenRank r' _ (B.axFstB _ l a b)          = B.axFstB r' l a b
weakenRank r' _ (B.axSndB _ l a b)          = B.axSndB r' l a b
weakenRank r' _ (B.axFstLfB _ l)            = B.axFstLfB r' l
weakenRank r' _ (B.axSndLfB _ l)            = B.axSndLfB r' l
weakenRank r' _ (B.axConstB _ l a b)        = B.axConstB r' l a b
weakenRank r' _ (B.axCompB _ l f g t)       = B.axCompB r' l f g t
weakenRank r' _ (B.axComp2B _ l h f g t)    = B.axComp2B r' l h f g t
weakenRank r' _ (B.axLiftB _ l f a b)       = B.axLiftB r' l f a b
weakenRank r' _ (B.axPostB _ l f h a b)     = B.axPostB r' l f h a b
weakenRank r' _ (B.axFanB _ l h1 h2 h a b)  = B.axFanB r' l h1 h2 h a b
weakenRank r' _ (B.axZB _ l x)              = B.axZB r' l x
weakenRank r' _ (B.axTreeRecLfB _ l f s p)         = B.axTreeRecLfB r' l f s p
weakenRank r' _ (B.axTreeRecNdB _ l f s p a b)     = B.axTreeRecNdB r' l f s p a b
weakenRank r' _ (B.axIfLfLB _ l a b)        = B.axIfLfLB r' l a b
weakenRank r' _ (B.axIfLfNB _ l x y a b)    = B.axIfLfNB r' l x y a b
weakenRank r' _ (B.axIfLfLLB _ l)           = B.axIfLfLLB r' l
weakenRank r' _ (B.axIfLfNLB _ l x y)       = B.axIfLfNLB r' l x y
weakenRank r' _ (B.axTreeEqLLB _ l)         = B.axTreeEqLLB r' l
weakenRank r' _ (B.axTreeEqLNB _ l a b)     = B.axTreeEqLNB r' l a b
weakenRank r' _ (B.axTreeEqNLB _ l a b)     = B.axTreeEqNLB r' l a b
weakenRank r' _ (B.axTreeEqNNB _ l a1 a2 b1 b2) = B.axTreeEqNNB r' l a1 a2 b1 b2
weakenRank r' _ (B.axGoodsteinB _ l a b)    = B.axGoodsteinB r' l a b
weakenRank r' _ (B.axReflB _ l t)           = B.axReflB r' l t

-- Equational structural rules (rank preserved; recurse).
weakenRank r' le (B.ruleSymB d)             = B.ruleSymB (weakenRank r' le d)
weakenRank r' le (B.cong1B f d)             = B.cong1B f (weakenRank r' le d)
weakenRank r' le (B.congLB g x d)           = B.congLB g x (weakenRank r' le d)
weakenRank r' le (B.congRB g x d)           = B.congRB g x (weakenRank r' le d)
weakenRank r' le (B.ruleInstB x t d)        = B.ruleInstB x t (weakenRank r' le d)

-- ruleTransB: rank is natMax r1 r2.  Split NatLE through natMax,
-- weaken each side to r', collapse natMax r' r' = r'.
weakenRank r' le (B.ruleTransB {r1} {l1} {r2} {l2} {t} {u} {v} d1 d2) =
  let lePair = natMaxLE_split {r1} {r2} le
      le1 = fst lePair
      le2 = snd lePair
      d1' = weakenRank r' le1 d1
      d2' = weakenRank r' le2 d2
      combined : DerivTBounded (natMax r' r') (natMax l1 l2) (atomic (eqn t v))
      combined = B.ruleTransB d1' d2'
      eqRR = natMaxIdem r'
  in eqSubst (\ rr -> DerivTBounded rr (natMax l1 l2) (atomic (eqn t v)))
              eqRR combined

-- Equational implication axioms (rank-polymorphic).
weakenRank r' _ (B.axEqTransB _ l a b c)    = B.axEqTransB r' l a b c
weakenRank r' _ (B.axEqCong1B _ l f a b)    = B.axEqCong1B r' l f a b
weakenRank r' _ (B.axEqCongLB _ l g a b c)  = B.axEqCongLB r' l g a b c
weakenRank r' _ (B.axEqCongRB _ l g a b c)  = B.axEqCongRB r' l g a b c

-- Propositional axioms (rank-polymorphic).
weakenRank r' _ (B.axKB _ l P Q)            = B.axKB r' l P Q
weakenRank r' _ (B.axSB _ l P Q R)          = B.axSB r' l P Q R
weakenRank r' _ (B.axNegB _ l P Q)          = B.axNegB r' l P Q

-- mpB: rank is natMax r1 r2 (level increments by 1 outside).
weakenRank r' le (B.mpB {r1} {l1} {r2} {l2} {P} {Q} d1 d2) =
  let lePair = natMaxLE_split {r1} {r2} le
      le1 = fst lePair
      le2 = snd lePair
      d1' = weakenRank r' le1 d1
      d2' = weakenRank r' le2 d2
      combined : DerivTBounded (natMax r' r') (suc (natMax l1 l2)) Q
      combined = B.mpB d1' d2'
      eqRR = natMaxIdem r'
  in eqSubst (\ rr -> DerivTBounded rr (suc (natMax l1 l2)) Q) eqRR combined

-- indBTB: output rank is suc (natMax r1 r2).  Pattern-match on the
-- NatLE bound to expose r' = suc r''; weaken inner premises to r'';
-- re-pack and collapse via natMaxIdem.
weakenRank (suc r'') (leSuc le') (B.indBTB {r1} {l1} {r2} {l2} e v1 v2 base step) =
  let lePair = natMaxLE_split {r1} {r2} le'
      le1 = fst lePair
      le2 = snd lePair
      base' = weakenRank r'' le1 base
      step' = weakenRank r'' le2 step
      combined : DerivTBounded (suc (natMax r'' r'')) (natMax l1 l2) (atomic e)
      combined = B.indBTB e v1 v2 base' step'
      eqRR = natMaxIdem r''
  in eqSubst (\ rr -> DerivTBounded (suc rr) (natMax l1 l2) (atomic e))
              eqRR combined

-- indBT2B: output rank suc (natMax (natMax r1 r2) (natMax r3 r4)).
-- Same trick: pattern-match (suc r'') (leSuc le'); split
-- twice through natMax; weaken all four premises; re-pack and
-- collapse  natMax r'' r'' = r''  twice via natMaxIdem.
weakenRank (suc r'') (leSuc le') (B.indBT2B {r1} {l1} {r2} {l2} {r3} {l3} {r4} {l4}
                                              e v1 v2 v3 v4 b1 b2 b3 b4) =
  let outerPair = natMaxLE_split {natMax r1 r2} {natMax r3 r4} le'
      leOuterL = fst outerPair        -- NatLE (natMax r1 r2) r''
      leOuterR = snd outerPair        -- NatLE (natMax r3 r4) r''
      pair12   = natMaxLE_split {r1} {r2} leOuterL
      pair34   = natMaxLE_split {r3} {r4} leOuterR
      le1 = fst pair12
      le2 = snd pair12
      le3 = fst pair34
      le4 = snd pair34
      b1' = weakenRank r'' le1 b1
      b2' = weakenRank r'' le2 b2
      b3' = weakenRank r'' le3 b3
      b4' = weakenRank r'' le4 b4
      lvl = natMax (natMax l1 l2) (natMax l3 l4)
      combined : DerivTBounded
                   (suc (natMax (natMax r'' r'') (natMax r'' r''))) lvl (atomic e)
      combined = B.indBT2B e v1 v2 v3 v4 b1' b2' b3' b4'
      eqIdem = natMaxIdem r''
      -- Reduce inner-left natMax r'' r'' -> r''.
      step1 : DerivTBounded (suc (natMax r'' (natMax r'' r''))) lvl (atomic e)
      step1 = eqSubst (\ rr -> DerivTBounded (suc (natMax rr (natMax r'' r''))) lvl (atomic e))
                       eqIdem combined
      -- Reduce inner-right natMax r'' r'' -> r''.
      step2 : DerivTBounded (suc (natMax r'' r'')) lvl (atomic e)
      step2 = eqSubst (\ rr -> DerivTBounded (suc (natMax r'' rr)) lvl (atomic e))
                       eqIdem step1
      -- Reduce outer natMax r'' r'' -> r''.
  in eqSubst (\ rr -> DerivTBounded (suc rr) lvl (atomic e)) eqIdem step2
