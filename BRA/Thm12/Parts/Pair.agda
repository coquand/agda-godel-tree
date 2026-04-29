{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.Pair
--
-- Theorem 12 case for g = Pair : Fun2 (the canonical pairing functor).
--
-- Goal: build  D2_Pair : Fun2  such that
--     ap1 thmT (ap2 D2_Pair x v)  =  codeFTeq2_Pair x v.
--
-- Strategy: the LHS-encoded slot of  codeFTeq2_Pair  is
--   Pair tagAp2 (Pair codeF2Pair (Pair (cor x) (cor v))) ,
-- which equals  cor (Pair x v)  by  axRecNd O stepCor + stepCorRed
-- (BRA.Cor).  So both LHS and RHS of the encoded equation reduce to the
-- SAME term  cor (Pair x v).  Thus the underlying BRA equation is
-- axRefl-trivial: axRefl (cor (Pair x v)).
--
-- Concretely:
--   1.  D2_Pair = Fan (Lift (KT tagCode_axRefl)) (Post cor Pair) Pair.
--       ap2 D2_Pair x v  reduces to  Pair tagCode_axRefl (cor (Pair x v))
--       =  parEncAxRefl (cor (Pair x v)).
--   2.  parDispAxRefl  reduces  thmT  to  Pair (cor (Pair x v)) (cor (Pair x v)).
--   3.  Bridge LHS via  cor (Pair x v) = Pair tagAp2 (Pair codeF2Pair (Pair (cor x) (cor v)))
--       (provable from  axRecNd O stepCor x v + stepCorRed ).

module BRA.Thm12.Parts.Pair where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxRefl)
open import BRA.Thm.ThmT using (thmT ; tagCode_axRefl)
open import BRA.Thm12.Param.AxRefl
  using (parDispAxRefl ; parEncAxRefl ; parOutAxRefl)

------------------------------------------------------------------------
-- D2_Pair : Fun2 .
--
-- ap2 D2_Pair x v = Pair tagCode_axRefl (cor (Pair x v))
--                 = parEncAxRefl (cor (Pair x v)).
--
-- Built using  Post cor Pair : ap2 (Post cor Pair) x v = cor (Pair x v) .

D2_Pair : Fun2
D2_Pair = Fan (Lift (KT tagCode_axRefl)) (Post cor Pair) Pair

------------------------------------------------------------------------
-- The asymmetric encoded equation.

codeFTeq2_Pair : Term -> Term -> Term
codeFTeq2_Pair x v =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair (ap1 cor x) (ap1 cor v))))
    (ap1 cor (ap2 Pair x v))

------------------------------------------------------------------------
-- Combinator reduction:  ap2 D2_Pair x v = parEncAxRefl (cor (Pair x v)) .

D2_Pair_reduce : (x v : Term) ->
  Deriv (atomic (eqn (ap2 D2_Pair x v)
                     (parEncAxRefl (ap1 cor (ap2 Pair x v)))))
D2_Pair_reduce x v =
  let s1 : Deriv (atomic (eqn (ap2 D2_Pair x v)
              (ap2 Pair (ap2 (Lift (KT tagCode_axRefl)) x v)
                        (ap2 (Post cor Pair) x v))))
      s1 = axFan (Lift (KT tagCode_axRefl)) (Post cor Pair) Pair x v

      s2a : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axRefl)) x v)
                                (ap1 (KT tagCode_axRefl) x)))
      s2a = axLift (KT tagCode_axRefl) x v
      s2b : Deriv (atomic (eqn (ap1 (KT tagCode_axRefl) x) tagCode_axRefl))
      s2b = axKT (natCode tagAxRefl) x
      s2  : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_axRefl)) x v)
                                tagCode_axRefl))
      s2  = ruleTrans s2a s2b

      s3 : Deriv (atomic (eqn (ap2 (Post cor Pair) x v) (ap1 cor (ap2 Pair x v))))
      s3 = axPost cor Pair x v
  in ruleTrans s1
       (ruleTrans (congL Pair (ap2 (Post cor Pair) x v) s2)
                  (congR Pair tagCode_axRefl s3))

------------------------------------------------------------------------
-- corPairUnfold : cor (Pair x v) = Pair tagAp2 (Pair codeF2Pair (Pair (cor x) (cor v))) .
--
-- Proof: axRecNd O stepCor x v  (cor = Rec O stepCor)  composed with
--        stepCorRed (Pair x v) (Pair (cor x) (cor v)).

private
  pairCodeF2T : Term
  pairCodeF2T = reify (codeF2 Pair)

  tagAp2T : Term
  tagAp2T = reify tagAp2

corPairUnfold : (x v : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap2 Pair x v))
                     (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T
                                                  (ap2 Pair (ap1 cor x) (ap1 cor v))))))
corPairUnfold x v =
  let recs : Term
      recs = ap2 Pair (ap1 cor x) (ap1 cor v)

      orig : Term
      orig = ap2 Pair x v

      s1 : Deriv (atomic (eqn (ap1 cor orig)
                              (ap2 stepCor orig recs)))
      s1 = axRecNd O stepCor x v

      s2 : Deriv (atomic (eqn (ap2 stepCor orig recs)
                              (ap2 Pair tagAp2T (ap2 Pair pairCodeF2T recs))))
      s2 = stepCorRed orig recs
  in ruleTrans s1 s2

------------------------------------------------------------------------
-- Bridge:  parOutAxRefl (cor (Pair x v)) = codeFTeq2_Pair x v .
--
-- parOutAxRefl t = Pair t t.  We need to rewrite the LEFT slot from
-- cor(Pair x v) to its unfolded form via corPairUnfold; right slot stays.

bridgePair : (x v : Term) ->
  Deriv (atomic (eqn (parOutAxRefl (ap1 cor (ap2 Pair x v)))
                     (codeFTeq2_Pair x v)))
bridgePair x v =
  congL Pair (ap1 cor (ap2 Pair x v)) (corPairUnfold x v)

------------------------------------------------------------------------
-- D_correct2_Pair .

D_correct2_Pair : (x v : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D2_Pair x v)) (codeFTeq2_Pair x v)))
D_correct2_Pair x v =
  let r_red = D2_Pair_reduce x v

      r_thmT : Deriv (atomic (eqn (ap1 thmT (ap2 D2_Pair x v))
                                   (ap1 thmT (parEncAxRefl (ap1 cor (ap2 Pair x v))))))
      r_thmT = cong1 thmT r_red

      r_disp = parDispAxRefl (ap1 cor (ap2 Pair x v))

      r_bridge = bridgePair x v
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)
