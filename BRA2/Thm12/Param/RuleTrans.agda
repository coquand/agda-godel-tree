{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Param.RuleTrans
--
-- Parametric-Term encoding constructor and dispatch lemma for ruleTrans.
-- Composes two sub-encodings y1T, y2T (Term-level) into the encoding of
-- ruleTrans applied to them.  Used by Theorem 12 recursive cases to
-- chain sub-equations.

module BRA2.Thm12.Param.RuleTrans where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.ThmT
  using ( thmT ; tagCode_ruleTrans ; thmTDispRuleTrans_param )

------------------------------------------------------------------------
-- Term-level encoder.

parEncRuleTrans : Term -> Term -> Term
parEncRuleTrans y1T y2T =
  ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)

------------------------------------------------------------------------
-- Parametric dispatch.  Given thmT-images of y1T, y2T (Pair u1 u2 and
-- Pair u3 u4) plus a Fst-shape proof on y1T, produces thmT image of the
-- combined ruleTrans encoding as Pair u1 u4.

parDispRuleTrans : (y1T y2T : Term) (u1 u2 u3 u4 : Term)
  (y1' x' : Term) ->
  Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
  Deriv (atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncRuleTrans y1T y2T))
                     (ap2 Pair u1 u4)))
parDispRuleTrans y1T y2T u1 u2 u3 u4 y1' x' shape d1 d2 =
  thmTDispRuleTrans_param y1T y2T u1 u2 u3 u4 y1' x' shape d1 d2
