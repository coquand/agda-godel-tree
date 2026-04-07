{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Nelson.SubstTForO where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.SubstTFor

------------------------------------------------------------------------
-- substTFor applied to O (= reify lf = reify (code O))
-- By axRecLf: ap1 (Rec O stepSubst) O = O
-- This is the base case of Rec, so it's just axRecLf.

substTForO : {hyp : Equation} ->
  Deriv hyp (eqn (ap1 substTFor O) O)
substTForO = axRecLf O stepSubst
