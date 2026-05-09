{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.RankDecrementBotIndBT
-- T3 of BRA2/NEXT-SESSION-RANKDECREMENT.md: smallest proof-of-concept
-- of indBT-elimination, specialised to rank 1 -> rank 0 with the
-- conclusion bot.
--
-- The headline lemma is
--
--    indBTBotElim :
--      DerivTBounded 0 l1 (atomic (substEq 0 O bot's-eqn)) ->
--      DerivTBounded 0 l2 (induction step over bot's-eqn) ->
--      DerivT0 bot
--
-- whose proof is one line:  rankZero base .  This works because
-- bot's equation is closed:
--
--   bot's-eqn = eqn O (ap2 Pair O O)
--
-- so  substEq 0 O bot's-eqn  reduces to  bot's-eqn  by computation,
-- which makes  base  a rank-0 proof of  bot  -- liftable to DerivT0
-- via BRA2.BoundedReductionRankZero.rankZero .
--
-- The indBT2 analogue follows the same pattern with two layers of
-- substitution on a closed equation.
--
-- Why this is the "smallest proof-of-concept of indBT-elimination":
-- it shows that the topmost indBT layer can be uniformly eliminated
-- when the conclusion is bot, without semantic-soundness machinery.
-- The genuine difficulty (cases (b) and (c) of the next-session
-- doc, where  e  has a free variable instantiated by an outer
-- ruleInst chain, or where indBT appears strictly inside the proof
-- tree under structural rules) remains open.

module BRA2.RankDecrementBotIndBT where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.BoundedReductionRankZero using (rankZero)
open import BRA2.DerivT0 using (bot)

------------------------------------------------------------------------
-- The closed equation that defines  bot .
--
-- bot = atomic (eqn trueT falseT)  with  trueT = O ,  falseT = ap2 Pair O O ,
-- so  bot = atomic botEqn  by definitional unfolding.

botEqn : Equation
botEqn = eqn O (ap2 Pair O O)

bot_eq_atomicBotEqn : Eq bot (atomic botEqn)
bot_eq_atomicBotEqn = refl

------------------------------------------------------------------------
-- substEq is the identity on closed equations.
--
-- substEq 0 O botEqn computes to botEqn itself, because all of
-- botEqn 's term-positions are  O  or  ap2 Pair O O  - both contain
-- no  var n , so  subst x r  is the identity on each sub-term.
-- Verified definitionally by  refl .

botEqn_substInert :
  (x : Nat) (t : Term) -> Eq (substEq x t botEqn) botEqn
botEqn_substInert _ _ = refl

------------------------------------------------------------------------
-- (T3.A) indBT-elimination, conclusion bot.
--
-- Input ranks  r1 , r2  must both be  zero  for the indBT output rank
-- to be  1 = suc (natMax 0 0) .  We take the explicit rank-zero ranks
-- to keep the lemma standalone (independent of natMaxZero accounting).
--
-- After  e := botEqn  is forced by output unification with bot, the
-- base case's type  atomic (substEq 0 O e) reduces to  atomic botEqn
-- = bot .  rankZero lifts to DerivT0.

indBTBotElim :
  {l1 l2 : Nat} (v1 v2 : Nat) ->
  -- base case: substEq 0 O botEqn = botEqn, so input type IS bot.
  B.DerivTBounded zero l1 (atomic (substEq zero O botEqn)) ->
  -- step case: irrelevant for bot-conclusion proof; argument supplied
  -- for type compatibility with B.indBTB.
  B.DerivTBounded zero l2
    ((atomic (substEq zero (var v1) botEqn))
     imp ((atomic (substEq zero (var v2) botEqn))
          imp (atomic (substEq zero (ap2 Pair (var v1) (var v2)) botEqn)))) ->
  O.DerivT0 bot
indBTBotElim _ _ base _ = rankZero base

------------------------------------------------------------------------
-- (T3.B) indBT2-elimination, conclusion bot.
--
-- The indBT2 base case  baseLL  is at type
--   atomic (substEq 1 O (substEq 0 O e))
-- which, on the closed botEqn, reduces twice to botEqn.  Same trick:
-- baseLL IS at rank-0 proving bot, lift via rankZero.

indBT2BotElim :
  {l1 l2 l3 l4 : Nat} (v1 v2 v3 v4 : Nat) ->
  B.DerivTBounded zero l1
    (atomic (substEq (suc zero) O (substEq zero O botEqn))) ->
  B.DerivTBounded zero l2
    ((atomic (substEq (suc zero) (var v3) (substEq zero O botEqn)))
     imp ((atomic (substEq (suc zero) (var v4) (substEq zero O botEqn)))
          imp (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                            (substEq zero O botEqn))))) ->
  B.DerivTBounded zero l3
    ((atomic (substEq (suc zero) O (substEq zero (var v1) botEqn)))
     imp ((atomic (substEq (suc zero) O (substEq zero (var v2) botEqn)))
          imp (atomic (substEq (suc zero) O
                                          (substEq zero (ap2 Pair (var v1) (var v2)) botEqn))))) ->
  B.DerivTBounded zero l4
    ((atomic (substEq (suc zero) (var v3) (substEq zero (var v1) botEqn)))
     imp ((atomic (substEq (suc zero) (var v4) (substEq zero (var v2) botEqn)))
          imp (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                            (substEq zero (ap2 Pair (var v1) (var v2)) botEqn))))) ->
  O.DerivT0 bot
indBT2BotElim _ _ _ _ baseLL _ _ _ = rankZero baseLL
