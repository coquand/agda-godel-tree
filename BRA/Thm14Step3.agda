{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14Step3
--
-- Implementation of the Thm 14 step 3 substrate (Guard p.16-17 lines
-- 1-3) for the BRA Goedel II tower.
--
-- Step 3 (uniform meta-arrow):  given a derivation
--    H : Deriv (atomic (eqn (ap1 th x) cG))      -- "x is a code for G"
-- produce a witness  d : Tree  and a derivation
--    Deriv (atomic (eqn (ap1 th (reify d))
--                       (codeFTeq (ap1 th x) (ap2 sub i i)))).
--
-- Mechanism (Guard p.17, lines 1-3):
--   (1)  th(Dth(x)) = "th(x) = j"      [Th 13, applied to H]
--   (2)  th(Dsub(i,i)) = "sub(i,i) = j" [Th 13, applied to subDef + cc]
--   (3)  combine via internalised eq-trans to reach
--        th(g(x)) = "th(x) = sub(i,i)" .
--
-- Our  Sigma-form  realisation does the meta-level eq-trans directly
-- on the input derivations, then encodes the resulting equation:
--   1.  sub i i = cG          [subDef j j  +  cc]
--   2.  th x  = sub i i       [ruleSym + ruleTrans on  H , (1)]
--   3.  encode  on (2)        [Sigma Tree witness; codeFTeq's symmetric
--                              definition makes the goal type
--                              definitionally equal to encode's output]
--
-- Pre-flight verification (mandated by NEXT-SESSION-GODELII-STEPS.md)
-- confirmed Guard's chain has hypothesis  th(x) = j  in every step,
-- with  i = num(code F_pre)  and  j = num(code G) .  This step is
-- the "easy" half of the chain (no BRA-substitution-rule
-- internalisation needed).  See  BRA/THM14-OBSTRUCTIONS.md  for the
-- harder steps 4-5 + closure obstructions discovered in pre-flight.

module BRA.Thm14Step3 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Sub using (sub ; subDef)
open import BRA.Thm14CodeFTeq using (codeFTeq)

import BRA.Thm11Diagonal

module Step3
  (th : Fun1)
  (thClosed :
     (x : Nat) (r : Term) -> Eq (substF1 x r th) th)
  (codeF1Th_noVar :
     (x : Nat) (repl : Tree) ->
     Eq (codedSubst repl (code (var x)) (codeF1 th)) (codeF1 th))
  (encode :
     (P : Formula) -> Deriv P ->
     Sigma Tree (\ y ->
       Deriv (atomic (eqn (ap1 th (reify y))
                          (reify (codeFormula P))))))
  where

  -- Reuse Thm11Diagonal's  j , G , and  cc  (= coding-substitution
  -- lemma).  cc lives inside Thm11Diagonal's  abstract  block but is
  -- still in scope -- only its body is opaque, which is exactly what
  -- the "small files / fast typecheck" methodological principle wants.

  open BRA.Thm11Diagonal.Diagonal th thClosed codeF1Th_noVar
    using (j ; G ; cc)

  i : Term
  i = reify j

  cG : Term
  cG = reify (codeFormula G)

  PrAtX : Term -> Formula
  PrAtX x = atomic (eqn (ap1 th x) cG)

  ----------------------------------------------------------------------
  -- Reusable lemma:  ap2 sub i i = cG  inside BRA.
  --
  -- Same calculation as Thm11Diagonal.diagonal's local  sub_to_G ,
  -- factored out for reuse by step 3 (and downstream step 4 / step 5
  -- once those are implementable -- see BRA/THM14-OBSTRUCTIONS.md).

  subIIeqcG : Deriv (atomic (eqn (ap2 sub i i) cG))
  subIIeqcG =
    let sub_red :
          Deriv (atomic (eqn (ap2 sub i i)
                             (reify (codedSubst (code i)
                                                (code (var zero))
                                                j))))
        sub_red = subDef j j

    in eqSubst
         (\ T -> Deriv (atomic (eqn (ap2 sub i i) (reify T))))
         cc
         sub_red

  ----------------------------------------------------------------------
  -- Step 3 substrate.

  step3 :
    (x : Term) ->
    Deriv (PrAtX x) ->
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                         (codeFTeq (ap1 th x) (ap2 sub i i)))))
  step3 x H =
    let cGeqSubII : Deriv (atomic (eqn cG (ap2 sub i i)))
        cGeqSubII = ruleSym subIIeqcG

        thxEqSubII : Deriv (atomic (eqn (ap1 th x) (ap2 sub i i)))
        thxEqSubII = ruleTrans H cGeqSubII

    in encode (atomic (eqn (ap1 th x) (ap2 sub i i))) thxEqSubII
