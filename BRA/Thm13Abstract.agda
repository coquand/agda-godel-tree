{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm13Abstract
--
-- Theorem 13 (guard15.pdf p.16) parameterised over an  encode
-- function (Thm 11's forward-encoding spec).  In the symmetric
-- reading of  codeFTeq  (= reify of codeFormula of the atomic eqn),
-- Thm 13 collapses to a one-line use of  encode  on the hypothesis
-- derivation.
--
-- Why:  codeFTeq alpha beta = reify (codeFormula (atomic (eqn alpha
-- beta))) ; this is exactly what encode produces given a Deriv of
-- the corresponding formula.  So given  H : Deriv (atomic (eqn (f x)
-- y)) , the witness tree and derivation are just  encode (...) H .
--
-- Output specialisations (consumed by  BRA.Thm14Abstract.Thm14.GodelII ):
--   thm13_th  : Thm 13 at f := th, value := i.
--   thm13_sub : Thm 13 at g := sub, second arg fixed to i, value := i.
-- Both produce a Sigma Tree (existential witness via encode).

module BRA.Thm13Abstract where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Sub using (sub)
open import BRA.Thm14CodeFTeq using (codeFTeq)

module Thm13
  (th : Fun1)

  -- The Goedel-numeral i = reify j , supplied externally.
  (i : Term)

  -- Thm 11's forward encoder.
  (encode : (P : Formula) -> Deriv P ->
            Sigma Tree (\ y ->
              Deriv (atomic (eqn (ap1 th (reify y))
                                 (reify (codeFormula P))))))
  where

  ----------------------------------------------------------------------
  -- Generic Thm 13 (singulary).  One-line use of  encode .

  thm13sing :
    (f : Fun1) (x y : Term) ->
    (H : Deriv (atomic (eqn (ap1 f x) y))) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap1 f x) y))))
  thm13sing f x y H = encode (atomic (eqn (ap1 f x) y)) H

  ----------------------------------------------------------------------
  -- Generic Thm 13 (binary, second arg fixed).

  thm13bin :
    (g : Fun2) (x v y : Term) ->
    (H : Deriv (atomic (eqn (ap2 g x v) y))) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap2 g x v) y))))
  thm13bin g x v y H = encode (atomic (eqn (ap2 g x v) y)) H

  ----------------------------------------------------------------------
  -- Specialisations consumed by  BRA.Thm14Abstract.Thm14.GodelII .

  -- f := th , y := i .
  thm13_th :
    (x : Term) ->
    (H : Deriv (atomic (eqn (ap1 th x) i))) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap1 th x) i))))
  thm13_th x H = thm13sing th x i H

  -- g := sub , v := i , y := i .
  thm13_sub :
    (x : Term) ->
    (H : Deriv (atomic (eqn (ap2 sub x i) i))) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap2 sub x i) i))))
  thm13_sub x H = thm13bin sub x i i H
