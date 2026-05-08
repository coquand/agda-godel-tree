{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm13 -- Guard 1963, Theorem 13 (guard15.pdf p.16).
--
--   For every singulary f and any  hyp : f(x) = y ,
--     th(Df(x)) = "f x_ = y"   is provable.
--   Analogously for binary functors.
--
-- Guard's proof is one line from Theorem 12:
--   th(Df(x)) = "f x_ = f(x)"  by Thm 12
--             = "f x_ = y"     by  hyp .
--
-- Mirror in this codebase:  rewrite the second slot of the codeFTeq
-- Pair from  cor (f x)  to  cor y  via  cong1 cor hyp + congR Pair _ .
-- The whole module is two clauses, total ~10 lines of dispatch logic.

module BRA2.Thm13 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor

open import BRA2.Thm.ThmT using (thmT)
open import BRA2.Thm12
  using (Thm12_F1_Result ; Thm12_F2_Result ; codeFTeq1 ; codeFTeq2)
       public

------------------------------------------------------------------------
-- Theorem 13 conclusion forms.
--
-- Like  codeFTeq[12]  but with the right-hand slot replaced by  cor y
-- (where  y  is the hypothesised value of  f x  /  g x v ).

codeFTeq1Hyp : Fun1 -> Term -> Term -> Term
codeFTeq1Hyp f x y =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
    (ap1 cor y)

codeFTeq2Hyp : Fun2 -> Term -> Term -> Term -> Term
codeFTeq2Hyp g x v y =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 g))
                        (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor y)

------------------------------------------------------------------------
-- Theorem 13.

thm13_F1 : (f : Fun1) (r12 : Thm12_F1_Result f) (x y : Term) ->
  Deriv (atomic (eqn (ap1 f x) y)) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 (Thm12_F1_Result.Df r12) x))
                     (codeFTeq1Hyp f x y)))
thm13_F1 f r12 x y hyp =
  let lhs_part : Term
      lhs_part = ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 f)) (ap1 cor x))
      cor_hyp : Deriv (atomic (eqn (ap1 cor (ap1 f x)) (ap1 cor y)))
      cor_hyp = cong1 cor hyp
      bridge : Deriv (atomic (eqn (codeFTeq1 f x) (codeFTeq1Hyp f x y)))
      bridge = congR Pair lhs_part cor_hyp
  in ruleTrans (Thm12_F1_Result.proof r12 x) bridge

thm13_F2 : (g : Fun2) (r12 : Thm12_F2_Result g) (x v y : Term) ->
  Deriv (atomic (eqn (ap2 g x v) y)) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 (Thm12_F2_Result.Dg r12) x v))
                     (codeFTeq2Hyp g x v y)))
thm13_F2 g r12 x v y hyp =
  let lhs_part : Term
      lhs_part = ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair (ap1 cor x) (ap1 cor v)))
      cor_hyp : Deriv (atomic (eqn (ap1 cor (ap2 g x v)) (ap1 cor y)))
      cor_hyp = cong1 cor hyp
      bridge : Deriv (atomic (eqn (codeFTeq2 g x v) (codeFTeq2Hyp g x v y)))
      bridge = congR Pair lhs_part cor_hyp
  in ruleTrans (Thm12_F2_Result.proof r12 x v) bridge
