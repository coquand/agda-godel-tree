{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm11Abstract
--
-- Goedel I from an abstract forward-only spec of the provability
-- predicate.  Reverse direction is NOT used.
--
-- Parameters of the nested module  Godel  :
--
--   * th        : Fun1              -- the provability functor
--   * G         : Formula           -- the Goedel sentence
--   * encode    : forward direction, internalised.  Every derivation
--                 Deriv P is witnessed by some tree y such that BRA
--                 proves  ap1 th (reify y)  =  reify (codeFormula P) .
--   * diagonal  : Goedel's fixed-point property, already ruleInst-ed
--                 at each y.  Deriv G entails that for every y,
--                 not (ap1 th (reify y) = reify (codeFormula G))
--                 is derivable.
--
-- The  diagonal  parameter is what a  sub -based (Ex 24 [8])
-- fixed-point construction composed with ruleInst + subDef + a
-- coding-commutes-with-substitution lemma would supply externally.
-- That construction does not use the reverse direction either; we
-- factor it out so that this file stays focused on the pure logical
-- skeleton of Thm 11.
--
-- Output:  thm11 : Deriv G -> Deriv (atomic (eqn trueT falseT))
--          i.e.  Deriv G -> Deriv (0 = 1).

module BRA2.Thm11Abstract where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv

module Godel
  (th : Fun1)
  (G  : Formula)
  (encode : (P : Formula) -> Deriv P ->
            Sigma Term (\ y ->
              Sigma (IsValue y) (\ _ ->
                Deriv (atomic (eqn (ap1 th (reify y))
                                   (reify (codeFormula P)))))))
  (diagonal : (y : Tree) -> Deriv G ->
              Deriv (not (atomic (eqn (ap1 th (reify y))
                                      (reify (codeFormula G))))))
  where

  ------------------------------------------------------------------
  -- The inconsistency formula  0 = 1 .

  bot : Formula
  bot = atomic (eqn trueT falseT)

  ------------------------------------------------------------------
  -- The positive equation  ap1 th (reify y) = reify (codeFormula G) ,
  -- parameterised by y.  Both  encode G  and  diagonal y  land here
  -- (modulo  not ).

  PG : Tree -> Formula
  PG y = atomic (eqn (ap1 th (reify y)) (reify (codeFormula G)))

  ------------------------------------------------------------------
  -- Thm 11: from a derivation of the Goedel sentence G we extract a
  -- derivation of 0 = 1.
  --
  -- Structure:
  --   1. encode pf          gives y_d and  E1 : Deriv (PG y_d) .
  --   2. diagonal y_d pf    gives         NEG : Deriv (not (PG y_d)) .
  --   3. axExFalso + two mp collapse E1 and NEG to  Deriv bot .
  --
  -- The reverse direction of the encoding spec is not consulted.

  thm11 : Deriv G -> Deriv bot
  thm11 pf =
    let
      enc = encode G pf

      y_d : Tree
      y_d = fst enc

      E1 : Deriv (PG y_d)
      E1 = snd (snd enc)

      NEG : Deriv (not (PG y_d))
      NEG = diagonal y_d pf

      axEf : Deriv ((PG y_d) imp ((not (PG y_d)) imp bot))
      axEf = axExFalso (PG y_d) bot
    in
      mp (mp axEf E1) NEG
