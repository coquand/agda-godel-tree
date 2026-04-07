{-# OPTIONS --safe --without-K --exact-split #-}

-- ComplementEqn.agda
--
-- The complement function e on equation codes (Rose p.133).
--
-- Given an equation code nd(code A)(code B) = reify of "A = B",
-- e produces the code of "TreeEq(A, B) = falseT", i.e., "A ≠ B".
--
-- e : Fun1 — a functor in the system, so thFunTFor can track it.
--
-- Also defines the Rose-style consistency statement:
--   conR = TreeEq(thFunTFor(x), e(thFunTFor(z))) = falseT
-- ("no theorem is the complement of another theorem")

module Guard.ComplementEqn where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTFor using (thFunTFor)

------------------------------------------------------------------------
-- Tree-level truth values (shared convention).

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

------------------------------------------------------------------------
-- Constants needed for the complement function.

private
  -- reify tagAp2
  tagAp2T : Term
  tagAp2T = reify tagAp2

  -- reify (codeF2 TreeEq)
  treeeqCT : Term
  treeeqCT = reify (codeF2 TreeEq)

  -- code of falseT = code (ap2 Pair O O) = nd tagAp2 (nd (codeF2 Pair) (nd (nd lf lf) (nd lf lf)))
  codeFalse : Tree
  codeFalse = code falseT

  -- reify of the above
  falseCT : Term
  falseCT = reify codeFalse

------------------------------------------------------------------------
-- The complement function e : Fun1.
--
-- e(t) = Pair(Pair(tagAp2T, Pair(treeeqCT, t)), falseCT)
--
-- When t = reify(codeEqn(eqn A B)) = Pair(reify(code A), reify(code B)):
--   e(t) = Pair(reify(nd tagAp2 (nd (codeF2 TreeEq) (nd (code A) (code B)))),
--               reify(code falseT))
--        = reify(nd (code (ap2 TreeEq A B)) (code falseT))
--        = reify(codeEqn(eqn (ap2 TreeEq A B) falseT))
--
-- So e maps the code of "A = B" to the code of "TreeEq(A,B) = falseT" (= "A ≠ B").

eF : Fun1
eF = Comp2 Pair
       (Comp2 Pair (KT tagAp2T) (Comp2 Pair (KT treeeqCT) I))
       (KT falseCT)

------------------------------------------------------------------------
-- Reduction lemma: eF applied to t reduces correctly.

eFRed : (t : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap1 eF t)
                  (ap2 Pair (ap2 Pair tagAp2T (ap2 Pair treeeqCT t)) falseCT))
eFRed t =
  let inner = Comp2 Pair (KT treeeqCT) I
      outer = Comp2 Pair (KT tagAp2T) inner
  in ruleTrans (axComp2 Pair outer (KT falseCT) t)
     (ruleTrans (congR Pair (ap1 outer t) (axKT falseCT t))
     (congL Pair falseCT
       (ruleTrans (axComp2 Pair (KT tagAp2T) inner t)
       (ruleTrans (congL Pair (ap1 inner t) (axKT tagAp2T t))
                  (congR Pair tagAp2T
                    (ruleTrans (axComp2 Pair (KT treeeqCT) I t)
                    (ruleTrans (congL Pair (ap1 I t) (axKT treeeqCT t))
                               (congR Pair treeeqCT (axI t)))))))))

------------------------------------------------------------------------
-- Meta-level correctness: e maps equation codes to complement codes.

eCorrect : (A B : Term) ->
  Eq (codeEqn (eqn (ap2 TreeEq A B) falseT))
     (nd (nd tagAp2 (nd (codeF2 TreeEq) (nd (code A) (code B)))) codeFalse)
eCorrect A B = refl

------------------------------------------------------------------------
-- Rose-style consistency statement (Theorem 13 as hypothesis).
--
-- conR: for all x, z: TreeEq(thFunTFor(x), e(thFunTFor(z))) = falseT
-- i.e., no theorem code equals the complement of another theorem code.
--
-- This is stronger than "no proof of trueT = falseT" but is the
-- hypothesis Rose uses for Theorems 16-18.
--
-- Two free variables: var 0 = x (proof index), var 1 = z (proof index).

conR : Equation
conR = eqn (ap2 TreeEq (ap1 thFunTFor (var zero))
                        (ap1 eF (ap1 thFunTFor (var (suc zero)))))
           falseT
