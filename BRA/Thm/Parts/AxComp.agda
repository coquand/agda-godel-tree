{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxComp
--
-- Proof-code vocabulary for the combinator defining equation
--   axComp : Deriv (ap1 (Comp f g) t  =  ap1 f (ap1 g t)) .

module BRA.Thm.Parts.AxComp where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxComp)

encAxComp : Fun1 -> Fun1 -> Term -> Tree
encAxComp f g t = nd (natCode tagAxComp)
                     (nd (codeF1 f)
                         (nd (codeF1 g) (code t)))

outAxComp : Fun1 -> Fun1 -> Term -> Tree
outAxComp f g t = codeFormula (atomic (eqn (ap1 (Comp f g) t)
                                           (ap1 f (ap1 g t))))
