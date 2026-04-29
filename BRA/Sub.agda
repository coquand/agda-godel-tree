{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Sub -- our tree-based analog of Guard's substitute-by-numeral
-- functor (Exercise 24 [8], guard15.pdf p.14):
--
--     sub(z, "P")  =  "S^{x_0}_{z} P"
--
-- That is: given a numeral z and a coded formula codeP, sub
-- substitutes the (Goedel code of the) numeral z for the variable
-- x_0 in P.
--
-- In our tree setting, z is a numeral = reify zTree for some Tree
-- zTree.  The substitution data fed to subT is
--
--     ap2 Pair (reify (code (var 0))) (ap1 cor z)
--   = ap2 Pair (reify (code (var 0))) (reify (code (reify zTree)))
--
-- by corOfReify.  Then subT carries out the substitution.
--
-- Spec (built):
--   ap2 sub (reify zTree) (reify codeP)
--     = reify (codedSubst (code (reify zTree)) (code (var 0)) codeP).

module BRA.Sub where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.StepReduce
open import BRA.Cor
open import BRA.SubT

------------------------------------------------------------------------
-- Constant: code of var 0 reified.

varCode0T : Term
varCode0T = reify (code (var zero))

------------------------------------------------------------------------
-- sub : Fun2.
--
-- Outer Fan dispatches:
--   leftHalf  a b = ap2 Pair varCode0T (ap1 cor a)   -- subst data
--   rightHalf a b = b                                 -- target
--   combiner = subT
--
-- leftHalf  combinator: Fan (Lift (KT varCode0T)) (Lift cor) Pair
-- rightHalf combinator: Post Snd Pair
--   (axPost + axSnd give  Post Snd Pair a b = Snd (Pair a b) = b.)

leftSub : Fun2
leftSub = Fan (Lift (KT varCode0T)) (Lift cor) Pair

rightSub : Fun2
rightSub = Post Snd Pair

sub : Fun2
sub = Fan leftSub rightSub subT

------------------------------------------------------------------------
-- Defining equation.

subDef : (zTree codeP : Tree) ->
  Deriv (atomic (eqn (ap2 sub (reify zTree) (reify codeP))
                      (reify (codedSubst (code (reify zTree))
                                          (code (var zero))
                                          codeP))))
subDef zTree codeP =
  let z : Term
      z = reify zTree

      codePT : Term
      codePT = reify codeP

      lhsApp : Term
      lhsApp = ap2 leftSub z codePT

      rhsApp : Term
      rhsApp = ap2 rightSub z codePT

      -- Step 1: sub = Fan leftSub rightSub subT, axFan unfolds.
      s1 : Deriv (atomic (eqn (ap2 sub z codePT) (ap2 subT lhsApp rhsApp)))
      s1 = axFan leftSub rightSub subT z codePT

      -- Step 2: reduce lhsApp to ap2 Pair varCode0T (ap1 cor z).
      lhsR1 : Deriv (atomic (eqn lhsApp
                                  (ap2 Pair (ap2 (Lift (KT varCode0T)) z codePT)
                                            (ap2 (Lift cor) z codePT))))
      lhsR1 = axFan (Lift (KT varCode0T)) (Lift cor) Pair z codePT

      lhsR2a : Deriv (atomic (eqn (ap2 (Lift (KT varCode0T)) z codePT) varCode0T))
      lhsR2a = constF2Red (code (var zero)) z codePT

      lhsR2b : Deriv (atomic (eqn (ap2 (Lift cor) z codePT) (ap1 cor z)))
      lhsR2b = axLift cor z codePT

      lhsCorTerm : Term
      lhsCorTerm = ap2 Pair varCode0T (ap1 cor z)

      lhsR : Deriv (atomic (eqn lhsApp lhsCorTerm))
      lhsR = ruleTrans lhsR1
              (ruleTrans (congL Pair (ap2 (Lift cor) z codePT) lhsR2a)
                         (congR Pair varCode0T lhsR2b))

      -- Step 3: reduce rhsApp to codePT.
      rhsR : Deriv (atomic (eqn rhsApp codePT))
      rhsR = ruleTrans (axPost Snd Pair z codePT) (axSnd z codePT)

      -- Step 4: by corOfReify, ap1 cor z = reify (code (reify zTree)).
      corCode : Tree
      corCode = code (reify zTree)

      corR : Deriv (atomic (eqn (ap1 cor z) (reify corCode)))
      corR = corOfReify zTree

      -- Step 5: assemble the subT call into the form subTDef expects.
      lhsFinal : Term
      lhsFinal = ap2 Pair varCode0T (reify corCode)

      lhsToFinal : Deriv (atomic (eqn lhsApp lhsFinal))
      lhsToFinal = ruleTrans lhsR (congR Pair varCode0T corR)

      s2 : Deriv (atomic (eqn (ap2 subT lhsApp rhsApp)
                              (ap2 subT lhsFinal codePT)))
      s2 = ruleTrans (congL subT rhsApp lhsToFinal)
                     (congR subT lhsFinal rhsR)

      -- Step 6: subTDef at n=0, codeA=corCode, codeB=codeP.
      --   varCode0T is reify (code (var zero)) definitionally,
      --   so lhsFinal = ap2 Pair (reify (code (var zero))) (reify corCode).
      s3 : Deriv (atomic (eqn (ap2 subT lhsFinal codePT)
                              (reify (codedSubst corCode
                                                  (code (var zero))
                                                  codeP))))
      s3 = subTDef zero corCode codeP

  in ruleTrans s1 (ruleTrans s2 s3)
