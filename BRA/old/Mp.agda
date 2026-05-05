{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Mp -- our tree-based analog of Guard's modus ponens functor
-- (Exercise 24 [1], guard15.pdf p.14):
--
--     mpF("P", "P ⊃ Q")  =  "Q" .
--
-- Named  mpF  (not  mp ) to avoid clash with the DerivF  mp  rule
-- constructor (modus ponens as an inference rule).  Conceptually
-- parallel: one at the proof-relation level, one at the tree level.
--
-- In our tree encoding of formulas (BRA.Formula),
--     codeFormula (P imp Q)  =  nd tagImp (nd (codeFormula P) (codeFormula Q))
-- so
--     reify (codeFormula (P imp Q))
--       =  ap2 Pair (reify tagImp) (ap2 Pair (reify (codeFormula P))
--                                             (reify (codeFormula Q)))
-- and extracting  reify (codeFormula Q)  is two applications of  Snd
-- to the second argument.  No new primitives; pure combinator.

module BRA.Mp where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

------------------------------------------------------------------------
-- mpF : Fun2.
--
-- Post Snd Pair (a, b)  =  Snd (Pair a b)  =  b           (axPost + axSnd)
-- Post (Comp Snd Snd) (Post Snd Pair) (a, b)
--   =  Comp Snd Snd (Post Snd Pair (a, b))                (axPost)
--   =  Snd (Snd b)                                        (axComp + axSnd)
--
-- So mpF ignores the first argument and applies Snd twice to the
-- second.  Applied to  (reify (codeFormula P), reify (codeFormula
-- (P imp Q)))  the result is  reify (codeFormula Q) .

mpF : Fun2
mpF = Post (Comp Snd Snd) (Post Snd Pair)

------------------------------------------------------------------------
-- Defining equation: mpF("P", "P ⊃ Q") = "Q".

mpFDef : (P Q : Formula) ->
  Deriv (atomic (eqn (ap2 mpF (reify (codeFormula P))
                              (reify (codeFormula (P imp Q))))
                      (reify (codeFormula Q))))
mpFDef P Q =
  let pT   = reify (codeFormula P)
      qT   = reify (codeFormula Q)
      impT = reify (codeFormula (P imp Q))
      -- impT = ap2 Pair (reify tagImp) (ap2 Pair pT qT)  definitionally.
      -- Step 1: unfold mpF = Post (Comp Snd Snd) (Post Snd Pair).
      --   ap2 mpF pT impT = ap1 (Comp Snd Snd) (ap2 (Post Snd Pair) pT impT)
      s1 : Deriv (atomic (eqn (ap2 mpF pT impT)
                              (ap1 (Comp Snd Snd) (ap2 (Post Snd Pair) pT impT))))
      s1 = axPost (Comp Snd Snd) (Post Snd Pair) pT impT
      -- Step 2: ap2 (Post Snd Pair) pT impT = ap1 Snd (ap2 Pair pT impT).
      s2 : Deriv (atomic (eqn (ap2 (Post Snd Pair) pT impT)
                              (ap1 Snd (ap2 Pair pT impT))))
      s2 = axPost Snd Pair pT impT
      -- Step 3: ap1 Snd (ap2 Pair pT impT) = impT.
      s3 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair pT impT)) impT))
      s3 = axSnd pT impT
      -- Combine: ap2 (Post Snd Pair) pT impT = impT.
      s23 : Deriv (atomic (eqn (ap2 (Post Snd Pair) pT impT) impT))
      s23 = ruleTrans s2 s3
      -- Step 4: cong1 (Comp Snd Snd) over s23.
      s4 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap2 (Post Snd Pair) pT impT))
                              (ap1 (Comp Snd Snd) impT)))
      s4 = cong1 (Comp Snd Snd) s23
      -- Step 5: unfold Comp: ap1 (Comp Snd Snd) impT = ap1 Snd (ap1 Snd impT).
      s5 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) impT)
                              (ap1 Snd (ap1 Snd impT))))
      s5 = axComp Snd Snd impT
      -- Step 6: impT reduces: ap1 Snd impT = ap2 Pair pT qT.
      --   impT = ap2 Pair (reify tagImp) (ap2 Pair pT qT).
      s6 : Deriv (atomic (eqn (ap1 Snd impT) (ap2 Pair pT qT)))
      s6 = axSnd (reify tagImp) (ap2 Pair pT qT)
      -- Step 7: cong1 Snd over s6 and then axSnd.
      s7a : Deriv (atomic (eqn (ap1 Snd (ap1 Snd impT))
                               (ap1 Snd (ap2 Pair pT qT))))
      s7a = cong1 Snd s6
      s7b : Deriv (atomic (eqn (ap1 Snd (ap2 Pair pT qT)) qT))
      s7b = axSnd pT qT
      s7 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd impT)) qT))
      s7 = ruleTrans s7a s7b
  in ruleTrans s1 (ruleTrans s4 (ruleTrans s5 s7))
