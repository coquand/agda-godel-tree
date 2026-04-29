{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.Parts.AxComp2
--
-- Proof-code vocabulary for
--   axComp2 : Deriv (ap1 (Comp2 h f g) t  =  ap2 h (ap1 f t) (ap1 g t)) .

module BRA.Thm.Parts.AxComp2 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Thm.Tag using (tagAxComp2)

encAxComp2 : Fun2 -> Fun1 -> Fun1 -> Term -> Tree
encAxComp2 h f g t = nd (natCode tagAxComp2)
                        (nd (codeF2 h)
                            (nd (codeF1 f)
                                (nd (codeF1 g) (code t))))

outAxComp2 : Fun2 -> Fun1 -> Fun1 -> Term -> Tree
outAxComp2 h f g t =
  codeFormula (atomic (eqn (ap1 (Comp2 h f g) t)
                           (ap2 h (ap1 f t) (ap1 g t))))
