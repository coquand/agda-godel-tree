{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.CorOfPair -- the analog of Guard's `"sx" = "sx"` equation for Pair.
--
-- Guard's equation (page 16 of guard15.pdf, line before Theorem 12):
--    "sx" = "sx"   meaning   3J("s", num(x))+1 = num(s(x))
-- expressing that the encoding of  s applied to num(x)  coincides with
-- the numeral of  s(x) .  This is what makes the underlining notation
-- consistent.
--
-- For our tree-based BRA where Pair plays the role of s, the analog is:
--   cor (ap2 Pair x y) = mkAp2T (reify (codeF2 Pair)) (cor x) (cor y)
-- Both sides are BRA-derivable equal at any x, y (free or closed) via
-- cor's defining equations (axRecNd O stepCor + stepCorRed).
--
-- This file also derives the bridge for axFst:
--   cor (ap1 Fst (ap2 Pair x y)) = cor x
-- via axFst x y + cong1 cor.
--
-- Both lemmas are SEMANTIC bridges used in Theorem 12 for Fst (Pair case):
-- they relate the post-substitution form (with cor x, cor y at variable
-- positions) to codeFTeq1Asym Fst (Pair x y).
--
-- No postulates, no holes.

module BRA.CorOfPair where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor ; stepCor ; stepCorRed)
open import BRA.Thm14CodeFTeqAsym using (mkAp2T)

------------------------------------------------------------------------
-- The "Pair" analog of Guard's "sx = sx" equation.
--
--   ap1 cor (ap2 Pair x y)  =  mkAp2T (codeF2 Pair) (cor x) (cor y)
--
-- For closed canonical x, y this gives the encoding of "Pair x y" as a
-- numeral.  For free x, y the equation holds schematically — both sides
-- have stuck cor x, cor y at the same positions, and the equation acts
-- as a structural unfolding of cor at the Pair-shape.

corOfPair : (x y : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap2 Pair x y))
                     (mkAp2T (reify (codeF2 Pair)) (ap1 cor x) (ap1 cor y))))
corOfPair x y =
  let
    orig : Term
    orig = ap2 Pair x y

    recs : Term
    recs = ap2 Pair (ap1 cor x) (ap1 cor y)

    -- Step 1: axRecNd unfolds cor at the Pair-input.
    s1 : Deriv (atomic (eqn (ap1 cor (ap2 Pair x y))
                             (ap2 stepCor orig recs)))
    s1 = axRecNd O stepCor x y

    -- Step 2: stepCorRed reduces stepCor at (orig, recs).
    --   ap2 stepCor orig recs
    --     = ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs)
    --     = mkAp2T (reify (codeF2 Pair)) (cor x) (cor y)
    -- (mkAp2T's expansion = ap2 Pair tagAp2T (ap2 Pair fCodeT (ap2 Pair aCodeT bCodeT)),
    --  which agrees with stepCor's output structure.)
    s2 : Deriv (atomic (eqn (ap2 stepCor orig recs)
                             (mkAp2T (reify (codeF2 Pair)) (ap1 cor x) (ap1 cor y))))
    s2 = stepCorRed orig recs

  in ruleTrans s1 s2

------------------------------------------------------------------------
-- The axFst-bridge:  cor (ap1 Fst (ap2 Pair x y)) = cor x.
--
-- This is the analog of "cor (Fst (Pair x y)) = cor x", obtained from
-- axFst x y + cong1 cor.

corOfFstPair : (x y : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair x y))) (ap1 cor x)))
corOfFstPair x y =
  cong1 cor (axFst x y)

------------------------------------------------------------------------
-- The axSnd-bridge (analogous):  cor (ap1 Snd (ap2 Pair x y)) = cor y.

corOfSndPair : (x y : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap1 Snd (ap2 Pair x y))) (ap1 cor y)))
corOfSndPair x y =
  cong1 cor (axSnd x y)
