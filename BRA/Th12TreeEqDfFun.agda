{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12TreeEqDfFun
--
-- Wrapped Fun2 form of D_TreeEq for use as the chain Df functor in
-- the universal Theorem 12 for TreeEq.
--
--   Df_F2_TreeEq = Fan (Lift (KT tagCode_ruleTrans)) D_TreeEq Pair
--
-- The outer Fan + Lift + KT construction makes ap2 Df_F2_TreeEq x v
-- BRA-reduce to  Pair tagCode_ruleTrans (ap2 D_TreeEq x v)  for any
-- (x, v).  This gives Fst projection access at variable inputs (the
-- Pair head is tagCode_ruleTrans = a reified natCode = a Pair tree),
-- which is required for chain-Df shape proofs in basePP_imp.
--
-- This is the same structural trick used by Df_F1_Rec_zs (Th12RecUniv)
-- and Df_F2_RecP_s (Th12RecPUniv).  See BRA/NEXT-SESSION-TREEEQ-PHASE4-FINDINGS.md.
--
-- No postulates, no holes.

module BRA.Th12TreeEqDfFun where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagRuleTrans)
open import BRA.Thm.ThmT using (thmT ; tagCode_ruleTrans)

import BRA.Thm12.Parts.TreeEq
open import BRA.Th12TreeEqNNFun using (D_TreeEq_NN_fun ; D_TreeEq_NN_closed)
module CB = BRA.Thm12.Parts.TreeEq.ConstructionBase D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB using (D_TreeEq ; D_TreeEq_closed)

------------------------------------------------------------------------
-- Step A: Df_F2_TreeEq with tagCode_ruleTrans outer wrapper.

Df_F2_TreeEq : Fun2
Df_F2_TreeEq = Fan (Lift (KT tagCode_ruleTrans)) D_TreeEq Pair

------------------------------------------------------------------------
-- Step B: outer reduction.
--   ap2 Df_F2_TreeEq x v  =BRA  Pair tagCode_ruleTrans (ap2 D_TreeEq x v)
-- via axFan + axLift + axKT.

Df_F2_TreeEq_reduce_outer : (x v : Term) ->
  Deriv (atomic (eqn (ap2 Df_F2_TreeEq x v)
                     (ap2 Pair tagCode_ruleTrans (ap2 D_TreeEq x v))))
Df_F2_TreeEq_reduce_outer x v =
  let
    s_fan : Deriv (atomic (eqn (ap2 Df_F2_TreeEq x v)
                                (ap2 Pair (ap2 (Lift (KT tagCode_ruleTrans)) x v)
                                          (ap2 D_TreeEq x v))))
    s_fan = axFan (Lift (KT tagCode_ruleTrans)) D_TreeEq Pair x v

    s_lift : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) x v)
                                 (ap1 (KT tagCode_ruleTrans) x)))
    s_lift = axLift (KT tagCode_ruleTrans) x v

    s_kt : Deriv (atomic (eqn (ap1 (KT tagCode_ruleTrans) x)
                               tagCode_ruleTrans))
    s_kt = axKT (natCode tagRuleTrans) x

    s_outerL : Deriv (atomic (eqn (ap2 (Lift (KT tagCode_ruleTrans)) x v)
                                   tagCode_ruleTrans))
    s_outerL = ruleTrans s_lift s_kt
  in ruleTrans s_fan
       (congL Pair (ap2 D_TreeEq x v) s_outerL)

------------------------------------------------------------------------
-- Step C: shape proof at any input.
--   Fst (ap2 Df_F2_TreeEq x v)  =BRA  tagCode_ruleTrans
-- via cong1 Fst on the outer reduction + axFst on the resulting Pair.

shape_at : (x v : Term) ->
  Deriv (atomic (eqn (ap1 Fst (ap2 Df_F2_TreeEq x v)) tagCode_ruleTrans))
shape_at x v =
  let
    reduce : Deriv (atomic (eqn (ap2 Df_F2_TreeEq x v)
                                 (ap2 Pair tagCode_ruleTrans (ap2 D_TreeEq x v))))
    reduce = Df_F2_TreeEq_reduce_outer x v

    cong_Fst : Deriv (atomic (eqn (ap1 Fst (ap2 Df_F2_TreeEq x v))
                                   (ap1 Fst (ap2 Pair tagCode_ruleTrans (ap2 D_TreeEq x v)))))
    cong_Fst = cong1 Fst reduce

    fst_proj : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagCode_ruleTrans (ap2 D_TreeEq x v)))
                                   tagCode_ruleTrans))
    fst_proj = axFst tagCode_ruleTrans (ap2 D_TreeEq x v)
  in ruleTrans cong_Fst fst_proj

------------------------------------------------------------------------
-- Step D: closure under substitution.
--   Df_F2_TreeEq is a closed Fun2 (depends only on D_TreeEq, which is
-- itself closed under D_TreeEq_closed).  So substF2 on any (x, r)
-- returns it unchanged.

Df_F2_TreeEq_closed : (x : Nat) (r : Term) ->
  Eq (substF2 x r Df_F2_TreeEq) Df_F2_TreeEq
Df_F2_TreeEq_closed x r =
  eqCong (\ DT -> Fan (Lift (KT tagCode_ruleTrans)) DT Pair)
         {x = substF2 x r D_TreeEq} {y = D_TreeEq}
         (D_TreeEq_closed x r)
