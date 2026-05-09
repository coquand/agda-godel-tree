{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.BoundedReductionAtomicAbsurd -- "atomic axioms cannot conclude bot".
--
-- T1 of BRA2/NEXT-SESSION-RANKDECREMENT.md.  Discharges the
-- *uniformly absurd* part of the eventual structural recursion over
--
--    DerivTBounded (suc r) l bot
--
-- where  bot = atomic (eqn O (ap2 Pair O O)) .
--
-- Of the 40 constructors of  DerivTBounded , 34 produce output
-- formulas whose top-level shape is incompatible with  bot .  We
-- expose four uniform absurdity lemmas that cover all of them:
--
--   (a) lhsAp1NotBot : axIB, axFstB, axSndB, axFstLfB, axSndLfB,
--       axCompB, axComp2B, axZB  (8 atomic computation axioms with
--       ap1 _ _  on the LHS), plus  cong1B .   Total: 9 cases.
--
--   (b) lhsAp2NotBot : axConstB, axLiftB, axPostB, axFanB,
--       axTreeRecLfB, axTreeRecNdB, axIfLfLB, axIfLfNB,
--       axIfLfLLB, axIfLfNLB, axTreeEqLLB, axTreeEqLNB,
--       axTreeEqNLB, axTreeEqNNB, axGoodsteinB  (15 atomic
--       computation axioms with  ap2 _ _ _  on the LHS), plus
--       congLB / congRB .   Total: 17 cases.
--
--   (c) reflEqnNotBot : axReflB t .  Output  atomic (eqn t t) ;
--       splitting on  t  yields four absurd cases via Term/Formula
--       no-confusion ( O = ap2 Pair O O  is impossible).
--
--   (d) impNotBot : the four axEq* axioms (axEqTransB, axEqCong1B,
--       axEqCongLB, axEqCongRB) and the three propositional axioms
--       (axKB, axSB, axNegB).  Output is  imp -shaped, but  bot  is
--       atomic .
--
-- Together these dismiss 9 + 17 + 1 + 7 = 34 cases.  Of the
-- remaining six constructors, five are generated normally as
-- structural recursion cases:
--
--   ruleSymB, ruleTransB, mpB, indBTB, indBT2B.
--
-- One ( ruleInstB ) cannot be analysed by Agda's pattern matcher
-- against  bot  directly because its output  substF x t P  is a
-- function expression; the rank-decrement proof handles this by
-- generalising the recursion target (or by external case-split on
-- the substituted formula).
--
-- Each lemma below is one  ()  pattern: Agda's pattern-matcher
-- dismisses them via Term/Formula no-confusion automatically.

module BRA2.BoundedReductionAtomicAbsurd where

open import BRA2.Base
open import BRA2.Term using (Term ; O ; var ; ap1 ; ap2 ; Fun1 ; Fun2 ; Equation ; eqn)
open import BRA2.Formula using (Formula ; atomic ; not_ ; _imp_)
open import BRA2.DerivTBounded using (bot)

------------------------------------------------------------------------
-- (a) Output equation has  ap1  on the LHS:  eqn (ap1 f a) r .

lhsAp1NotBot :
  (f : Fun1) (a r : Term) ->
  Eq (atomic (eqn (ap1 f a) r)) bot -> Empty
lhsAp1NotBot _ _ _ ()

------------------------------------------------------------------------
-- (b) Output equation has  ap2  on the LHS:  eqn (ap2 g a b) r .

lhsAp2NotBot :
  (g : Fun2) (a b r : Term) ->
  Eq (atomic (eqn (ap2 g a b) r)) bot -> Empty
lhsAp2NotBot _ _ _ _ ()

------------------------------------------------------------------------
-- (c) Diagonal equation  eqn t t  cannot be bot.
--
-- For  bot = eqn O (ap2 Pair O O) , equality forces  t = O AND
-- t = ap2 Pair O O , giving  O = ap2 Pair O O  -- absurd.

reflEqnNotBot :
  (t : Term) ->
  Eq (atomic (eqn t t)) bot -> Empty
reflEqnNotBot O           ()
reflEqnNotBot (var _)     ()
reflEqnNotBot (ap1 _ _)   ()
reflEqnNotBot (ap2 _ _ _) ()

------------------------------------------------------------------------
-- (d) Output formula has shape  P imp Q :  bot is atomic.

impNotBot :
  (P Q : Formula) ->
  Eq (P imp Q) bot -> Empty
impNotBot _ _ ()
