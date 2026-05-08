{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm11
--
-- Gödel's First Incompleteness Theorem in BRA:  from a derivation of
-- the Gödel sentence  G , derive the inconsistency formula  0 = 1 .
--
-- This file composes:
--   * BRA2.Thm11Diagonal.Diagonal  (supplies G and the diagonal property)
--   * BRA2.Thm11Abstract.Godel     (the six-line axExFalso skeleton)
--
-- Output:  thm11 : Deriv G -> Deriv (atomic (eqn trueT falseT))
-- (i.e.  Deriv G  ->  Deriv 0 = 1 ).

module BRA2.Thm11 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
import BRA2.Thm11Abstract
import BRA2.Thm11Diagonal

module Thm11
  (th : Fun1)
  (thClosed :
     (x : Nat) (r : Term) -> Eq (substF1 x r th) th)
  (codeF1Th_noVar :
     (x : Nat) (repl : Tree) ->
     Eq (codedSubst repl (code (var x)) (codeF1 th)) (codeF1 th))
  (encode :
     (P : Formula) -> Deriv P ->
     Sigma Term (\ y ->
       Sigma (IsValue y) (\ _ ->
         Deriv (atomic (eqn (ap1 th (reify y))
                            (reify (codeFormula P)))))))
  where

  open BRA2.Thm11Diagonal.Diagonal th thClosed codeF1Th_noVar
    using (F_pre ; j ; G ; diagonal)

  open BRA2.Thm11Abstract.Godel th G encode diagonal
    using (bot ; thm11)

  -- Re-export the headline theorem.
  thm11-exported : Deriv G -> Deriv bot
  thm11-exported = thm11
