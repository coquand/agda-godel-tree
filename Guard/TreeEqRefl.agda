{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.TreeEqRefl -- reflection of TreeEq into propositional equality.
--
-- Phase B of Guard/GOODSTEIN-PLAN.md.
--
-- Given  Deriv hyp (TreeEq a b = O) , derive  Deriv hyp (a = b) .
--
-- In Goodstein's PRA (Rose 1961 [1]) reflection is a derived theorem:
-- the characteristic equation  eq(a,b)*a = eq(a,b)*b  together with
-- "eq(a,b) = 0" implies  a = b  by substitution + the IfLf-L axiom.
--
-- Our tree analogue uses the new  axGoodstein  axiom (Guard.Step):
--
--   axGoodstein a b :
--     Deriv hyp (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
--                    (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))) .
--
-- Given  treeEqHyp : Deriv hyp (ap2 TreeEq a b = O) , the derivation is
--
--     a
--   = IfLf O            (Pair a O)    (by  ruleSym (axIfLfL a O))
--   = IfLf (TreeEq a b) (Pair a O)    (by  ruleSym (congL IfLf _ treeEqHyp))
--   = IfLf (TreeEq a b) (Pair b O)    (by  axGoodstein a b)
--   = IfLf O            (Pair b O)    (by  congL IfLf _ treeEqHyp)
--   = b                                (by  axIfLfL b O)
--
-- Polymorphic in  hyp .  No postulates, no holes.

module Guard.TreeEqRefl where

open import Guard.Base
open import Guard.Term
open import Guard.Step

------------------------------------------------------------------------
-- treeEqRefl: Goodstein-style reflection principle for TreeEq.

treeEqRefl : {a b : Term} {hyp : Equation} ->
             Deriv hyp (eqn (ap2 TreeEq a b) O) ->
             Deriv hyp (eqn a b)
treeEqRefl {a} {b} {hyp} treeEqHyp =
  ruleTrans
    (ruleSym (axIfLfL a O))
    (ruleTrans
      (ruleSym (congL IfLf (ap2 Pair a O) treeEqHyp))
      (ruleTrans
        (axGoodstein a b)
        (ruleTrans
          (congL IfLf (ap2 Pair b O) treeEqHyp)
          (axIfLfL b O))))
