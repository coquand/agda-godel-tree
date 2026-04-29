{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12Abstract
--
-- Theorem 12 (guard15.pdf p.16) parameterised over Thm 11's encode
-- function.  In the symmetric reading of codeFTeq (= reify of
-- codeFormula of the atomic eqn), Thm 12 collapses to ONE uniform
-- one-line proof per arity: encode applied to axRefl.
--
-- Compare to the original 15-per-primitive-contract design (now
-- superseded): the symmetric reading + concrete encode dissolves the
-- per-primitive case-split entirely.
--
-- Output:  thm12sing : (f : Fun1) (x : Term) ->
--                      Sigma Tree (\ d -> Deriv (atomic (eqn
--                        (ap1 th (reify d))
--                        (codeFTeq (ap1 f x) (ap1 f x)))))
--          thm12bin : analogous for Fun2.
-- These plug directly into  BRA.Thm13Abstract  if a Thm 12-based
-- approach to Thm 13 is desired (though Thm 13 with concrete encode
-- bypasses Thm 12 entirely; see BRA.Thm13Abstract).

module BRA.Thm12Abstract where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm14CodeFTeq using (codeFTeq)

module Thm12
  (th : Fun1)

  (encode : (P : Formula) -> Deriv P ->
            Sigma Tree (\ y ->
              Deriv (atomic (eqn (ap1 th (reify y))
                                 (reify (codeFormula P))))))
  where

  ----------------------------------------------------------------------
  -- Thm 12 (singulary).  Uniform across all Fun1.

  thm12sing :
    (f : Fun1) (x : Term) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap1 f x) (ap1 f x)))))
  thm12sing f x =
    encode (atomic (eqn (ap1 f x) (ap1 f x))) (axRefl (ap1 f x))

  ----------------------------------------------------------------------
  -- Thm 12 (binary).  Uniform across all Fun2.

  thm12bin :
    (g : Fun2) (x v : Term) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap2 g x v) (ap2 g x v)))))
  thm12bin g x v =
    encode (atomic (eqn (ap2 g x v) (ap2 g x v))) (axRefl (ap2 g x v))
