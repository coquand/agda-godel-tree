{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.BoundedReductionRankZero -- the rank-0 base case of the
-- bounded cut-elimination programme.
--
-- Lemma:  rankZero : forall {l P}, DerivTBounded 0 l P -> DerivT0 P .
--
-- "If a bounded threshold derivation uses no induction (rank 0), then
--  it is already in the open fragment."
--
-- This is the natural BASE CASE of the eventual rank-induction proof
-- of  BoundedReductionTheorem .  The inductive step --- pushing one
-- layer of  indBT  /  indBT2  through the rest of the proof tree ---
-- is the genuine technical heart of Step 3 and remains open.
--
-- This file lands in support of BRA2/BOUNDED-REFLECTION-PLAN.md
-- Section 3, Step 3 (Q5: "what is the right base case (r=0, l=0)?").
--
-- Implementation note.  Agda's unifier is stuck on  natMax  in the
-- output indices of  mpB  /  ruleTransB  /  indBT*B , so we cannot
-- write  rankZero  by direct pattern matching against
-- DerivTBounded zero l P .  We work around this by carrying an
-- explicit  Eq r zero  witness and decomposing it via  natMaxZero
-- in the binary-combiner cases.

module BRA2.BoundedReductionRankZero where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0      as O
import BRA2.DerivTBounded as B

------------------------------------------------------------------------
-- natMax decomposition lemma:  natMax a b = 0  iff  a = 0  and  b = 0 .

natMaxZero : (a b : Nat) ->
             Eq (B.natMax a b) zero ->
             Sigma (Eq a zero) (\ _ -> Eq b zero)
natMaxZero zero    zero    refl = mkSigma refl refl
natMaxZero (suc _) zero    ()
natMaxZero (suc _) (suc _) ()

------------------------------------------------------------------------
-- rankZeroAux : carry an explicit  Eq r zero  witness and structurally
-- recurse.  All atomic axioms and unary structural rules are direct
-- maps; the binary combiners use natMaxZero to derive r1 = 0 and r2 = 0
-- from the output rank constraint; indBT* are dismissed via the absurd
-- pattern  ()  because their output ranks are  suc _ , incompatible
-- with  Eq r zero .

rankZeroAux :
  {r l : Nat} {P : Formula} ->
  B.DerivTBounded r l P ->
  Eq r zero ->
  O.DerivT0 P

rankZeroAux (B.axIB _ _ t)              _ = O.axI t
rankZeroAux (B.axFstB _ _ a b)          _ = O.axFst a b
rankZeroAux (B.axSndB _ _ a b)          _ = O.axSnd a b
rankZeroAux (B.axFstLfB _ _)            _ = O.axFstLf
rankZeroAux (B.axSndLfB _ _)            _ = O.axSndLf
rankZeroAux (B.axConstB _ _ a b)        _ = O.axConst a b
rankZeroAux (B.axCompB _ _ f g t)       _ = O.axComp f g t
rankZeroAux (B.axComp2B _ _ h f g t)    _ = O.axComp2 h f g t
rankZeroAux (B.axLiftB _ _ f a b)       _ = O.axLift f a b
rankZeroAux (B.axPostB _ _ f h a b)     _ = O.axPost f h a b
rankZeroAux (B.axFanB _ _ h1 h2 h a b)  _ = O.axFan h1 h2 h a b
rankZeroAux (B.axZB _ _ x)              _ = O.axZ x
rankZeroAux (B.axTreeRecLfB _ _ f s p)         _ = O.axTreeRecLf f s p
rankZeroAux (B.axTreeRecNdB _ _ f s p a b)     _ = O.axTreeRecNd f s p a b
rankZeroAux (B.axIfLfLB _ _ a b)        _ = O.axIfLfL a b
rankZeroAux (B.axIfLfNB _ _ x y a b)    _ = O.axIfLfN x y a b
rankZeroAux (B.axIfLfLLB _ _)           _ = O.axIfLfLL
rankZeroAux (B.axIfLfNLB _ _ x y)       _ = O.axIfLfNL x y
rankZeroAux (B.axTreeEqLLB _ _)         _ = O.axTreeEqLL
rankZeroAux (B.axTreeEqLNB _ _ a b)     _ = O.axTreeEqLN a b
rankZeroAux (B.axTreeEqNLB _ _ a b)     _ = O.axTreeEqNL a b
rankZeroAux (B.axTreeEqNNB _ _ a1 a2 b1 b2) _ = O.axTreeEqNN a1 a2 b1 b2
rankZeroAux (B.axGoodsteinB _ _ a b)    _ = O.axGoodstein a b
rankZeroAux (B.axReflB _ _ t)           _ = O.axRefl t
rankZeroAux (B.ruleSymB d)              eq = O.ruleSym (rankZeroAux d eq)
rankZeroAux (B.ruleTransB {r1} {_} {r2} {_} d1 d2) eq =
  let p = natMaxZero r1 r2 eq in
  O.ruleTrans (rankZeroAux d1 (fst p)) (rankZeroAux d2 (snd p))
rankZeroAux (B.cong1B f d)              eq = O.cong1 f (rankZeroAux d eq)
rankZeroAux (B.congLB g x d)            eq = O.congL g x (rankZeroAux d eq)
rankZeroAux (B.congRB g x d)            eq = O.congR g x (rankZeroAux d eq)
rankZeroAux (B.axEqTransB _ _ a b c)    _ = O.axEqTrans a b c
rankZeroAux (B.axEqCong1B _ _ f a b)    _ = O.axEqCong1 f a b
rankZeroAux (B.axEqCongLB _ _ g a b c)  _ = O.axEqCongL g a b c
rankZeroAux (B.axEqCongRB _ _ g a b c)  _ = O.axEqCongR g a b c
rankZeroAux (B.axKB _ _ P Q)            _ = O.axK P Q
rankZeroAux (B.axSB _ _ P Q R)          _ = O.axS P Q R
rankZeroAux (B.axNegB _ _ P Q)          _ = O.axNeg P Q
rankZeroAux (B.mpB {r1} {_} {r2} {_} d1 d2) eq =
  let p = natMaxZero r1 r2 eq in
  O.mp (rankZeroAux d1 (fst p)) (rankZeroAux d2 (snd p))
rankZeroAux (B.ruleInstB x t d)         eq = O.ruleInst x t (rankZeroAux d eq)
rankZeroAux (B.indBTB _ _ _ _ _)        ()
rankZeroAux (B.indBT2B _ _ _ _ _ _ _ _ _) ()

------------------------------------------------------------------------
-- The advertised rank-0 lemma.

rankZero :
  {l : Nat} {P : Formula} ->
  B.DerivTBounded zero l P ->
  O.DerivT0 P
rankZero d = rankZeroAux d refl
