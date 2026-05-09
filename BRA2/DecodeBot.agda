{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DecodeBot
--
-- Reflection-threshold experiment.  Goal:
--
--   decode_bot :
--     (y : Term) -> IsValue y ->
--     Deriv (atomic (eqn (ap1 thmT y) (reify (codeFormula bot)))) ->
--     Deriv bot
--
-- This file delivers the reusable infrastructure piece -- the
-- "ineqLemma" framework, which converts any Deriv of a closed false
-- equation between value-shape Terms into Deriv bot.  ineqLemma is
-- the structural ingredient decode_bot would use in every leaf
-- (non-recursive-rule) case.
--
-- The main theorem decode_bot is NOT delivered.  See
-- BRA2/DECODE-BOT-REPORT.md for the diagnostic on why: the BRA2.Thm.ThmT
-- module wraps thmT in an abstract block (lines 137-10583), so thmT is
-- opaque outside the WithDispatch namespace.  The exported dispatch
-- lemmas (thmTDispAxI, thmTDispMp, ...) only give reductions for
-- inputs of the form  ap2 Pair (natCode (suc tag)) payT  at a known
-- tag.  No reduction is exported for  thmT O  or for  thmT (ap2 Pair a b)
-- when  a  is not a recognized tag.  decode_bot's value-base case
-- (y = O) and unrecognized-tag cases consequently cannot be discharged
-- without either embedding decode_bot inside the abstract block or
-- exporting additional thmT-evaluation lemmas.

module BRA2.DecodeBot where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.SubT using (treeEqRed)
open import BRA2.Th14SubTPushthrough using (treeEqRefl)
open import BRA2.GoedelII using (bot)

import BRA2.Thm.ThmT
open BRA2.Thm.ThmT using (thmT ; thmT_O_eval ; thmT_pairO_eval)

----------------------------------------------------------------------
-- The "false equation -> Deriv bot" bridge.
--
-- ineqLemma packages the standard projection-via-TreeEq trick:
-- if t and u are value-shape Terms with treeEq t u = false (a
-- decidable, meta-level fact), then any Deriv of  t = u  collapses
-- to a Deriv of  bot = atomic (eqn O falseT) .
--
-- Construction:
--   1.  congR TreeEq t h               :  TreeEq t t = TreeEq t u
--   2.  treeEqRed t t                  :  TreeEq t t = boolCase (treeEq t t) O falseT
--                                       = O                                   (treeEqRefl t)
--   3.  treeEqRed t u                  :  TreeEq t u = boolCase (treeEq t u) O falseT
--                                       = falseT                              (neq)
--   4.  Chain ruleSym/ruleTrans yields :  O = falseT .

ineqLemma :
  (t u : Term) (vt : IsValue t) (vu : IsValue u) ->
  Eq (treeEq t u) false ->
  Deriv (atomic (eqn t u)) ->
  Deriv bot
ineqLemma t u vt vu neq h =
  let
    -- Step 1: TreeEq t t = TreeEq t u .
    s1 : Deriv (atomic (eqn (ap2 TreeEq t t) (ap2 TreeEq t u)))
    s1 = congR TreeEq t h

    -- Step 2: TreeEq t t = boolCase (treeEq t t) O falseT .
    s2raw : Deriv (atomic (eqn (ap2 TreeEq t t)
                                (boolCase (treeEq t t) O falseT)))
    s2raw = treeEqRed t vt t vt

    -- Reduce the meta-level boolCase by Eq.subst on  treeEq t t = true .
    s2 : Deriv (atomic (eqn (ap2 TreeEq t t) O))
    s2 = eqSubst
           (\ b -> Deriv (atomic (eqn (ap2 TreeEq t t)
                                       (boolCase b O falseT))))
           (treeEqRefl t vt)
           s2raw

    -- Step 3: TreeEq t u = boolCase (treeEq t u) O falseT
    --                    = falseT                       (since neq)
    s3raw : Deriv (atomic (eqn (ap2 TreeEq t u)
                                (boolCase (treeEq t u) O falseT)))
    s3raw = treeEqRed t vt u vu

    s3 : Deriv (atomic (eqn (ap2 TreeEq t u) falseT))
    s3 = eqSubst
           (\ b -> Deriv (atomic (eqn (ap2 TreeEq t u)
                                       (boolCase b O falseT))))
           neq
           s3raw

    -- Step 4: chain.
    chain1 : Deriv (atomic (eqn O (ap2 TreeEq t u)))
    chain1 = ruleTrans (ruleSym s2) s1
  in ruleTrans chain1 s3

----------------------------------------------------------------------
-- Sanity check: the codeFormula of bot is value-shape, and
-- meta-level treeEq distinguishes O from it (proof: refl).
-- These are the two static facts decode_bot's y=O case would need.

codeBot : Term
codeBot = reify (codeFormula bot)

codeBot_isValue : IsValue codeBot
codeBot_isValue = codeFormula_isValue bot

treeEq_O_codeBot_false : Eq (treeEq O codeBot) false
treeEq_O_codeBot_false = refl

----------------------------------------------------------------------
-- The y = O case of decode_bot.
--
-- thmT(O) reduces to O via thmT_O_eval (which lives inside the
-- BRA2.Thm.ThmT abstract block, applying axRecLf at the underlying
-- Rec primitive).  The hypothesis  thmT O = codeFormula bot  then
-- collapses via ineqLemma to Deriv bot.

decode_bot_O :
  Deriv (atomic (eqn (ap1 thmT O) (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_O h =
  let
    -- Replace  thmT O  by  O  using thmT_O_eval.
    h' : Deriv (atomic (eqn O codeBot))
    h' = ruleTrans (ruleSym thmT_O_eval) h
  in ineqLemma O codeBot valO codeBot_isValue treeEq_O_codeBot_false h'

----------------------------------------------------------------------
-- The y = Pair O b case of decode_bot.
--
-- thmT(Pair O b) reduces to O via thmT_pairO_eval (cascade falls
-- through all 42 levels and lands at fbBody = O).  Then ineqLemma
-- between O and codeFormula bot.

decode_bot_pairO :
  (b : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 Pair O b)) (reify (codeFormula bot)))) ->
  Deriv bot
decode_bot_pairO b h =
  let
    h' : Deriv (atomic (eqn O codeBot))
    h' = ruleTrans (ruleSym (thmT_pairO_eval b)) h
  in ineqLemma O codeBot valO codeBot_isValue treeEq_O_codeBot_false h'
