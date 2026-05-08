{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th12TreeEqNNReduce -- BRA reduction proof for the new
-- D_TreeEq_NN_fun at NN input.
--
-- Proves:
--   D_TreeEq_NN_fun_at_NN v1 v2 v3 v4 :
--     ap2 D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4) =BRA
--       Pair tagCode_ruleTrans (Pair y1T_target y2T_target)
--   where
--     y1T_target = parEncAxTreeEqNN (cor v1)(cor v2)(cor v3)(cor v4)
--     y2T_target = ap2 D_IfLf (ap2 TreeEq v1 v3)
--                             (ap2 Pair (ap2 TreeEq v2 v4)(ap2 Pair O O))
--
-- Strategy: peel each Fan + Lift + Post + Comp + KT layer using its
-- defining axiom, composing with ruleTrans / cong.  No postulates.

module BRA2.Th12TreeEqNNReduce where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxTreeEqNN ; tagRuleTrans)
open import BRA2.Thm.ThmT using (tagCode_axTreeEqNN ; tagCode_ruleTrans)
open import BRA2.Thm12.Parts.IfLf using (D_IfLf)
open import BRA2.Thm12.Param.AxTreeEqNN using (parEncAxTreeEqNN)
open import BRA2.Th12TreeEqNNFun

------------------------------------------------------------------------
-- Helper reductions for the building blocks at any (orig, recs) input.

sndProj_eval : (x v : Term) ->
  Deriv (atomic (eqn (ap2 sndProj x v) v))
sndProj_eval x v = ruleTrans (axPost Snd Pair x v) (axSnd x v)

ev1_eval : (v1 v2 v : Term) ->
  Deriv (atomic (eqn (ap2 ev1 (ap2 Pair v1 v2) v) v1))
ev1_eval v1 v2 v =
  ruleTrans (axLift Fst (ap2 Pair v1 v2) v) (axFst v1 v2)

ev2_eval : (v1 v2 v : Term) ->
  Deriv (atomic (eqn (ap2 ev2 (ap2 Pair v1 v2) v) v2))
ev2_eval v1 v2 v =
  ruleTrans (axLift Snd (ap2 Pair v1 v2) v) (axSnd v1 v2)

ev3_eval : (x v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 ev3 x (ap2 Pair v3 v4)) v3))
ev3_eval x v3 v4 =
  let v = ap2 Pair v3 v4
      s1 = axPost Fst sndProj x v
      s2 = cong1 Fst (sndProj_eval x v)
      s3 = axFst v3 v4
  in ruleTrans s1 (ruleTrans s2 s3)

ev4_eval : (x v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 ev4 x (ap2 Pair v3 v4)) v4))
ev4_eval x v3 v4 =
  let v = ap2 Pair v3 v4
      s1 = axPost Snd sndProj x v
      s2 = cong1 Snd (sndProj_eval x v)
      s3 = axSnd v3 v4
  in ruleTrans s1 (ruleTrans s2 s3)

ecv1_eval : (v1 v2 v : Term) ->
  Deriv (atomic (eqn (ap2 ecv1 (ap2 Pair v1 v2) v) (ap1 cor v1)))
ecv1_eval v1 v2 v =
  let s1 = axLift (Comp cor Fst) (ap2 Pair v1 v2) v
      s2 = axComp cor Fst (ap2 Pair v1 v2)
      s3 = cong1 cor (axFst v1 v2)
  in ruleTrans s1 (ruleTrans s2 s3)

ecv2_eval : (v1 v2 v : Term) ->
  Deriv (atomic (eqn (ap2 ecv2 (ap2 Pair v1 v2) v) (ap1 cor v2)))
ecv2_eval v1 v2 v =
  let s1 = axLift (Comp cor Snd) (ap2 Pair v1 v2) v
      s2 = axComp cor Snd (ap2 Pair v1 v2)
      s3 = cong1 cor (axSnd v1 v2)
  in ruleTrans s1 (ruleTrans s2 s3)

ecv3_eval : (x v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 ecv3 x (ap2 Pair v3 v4)) (ap1 cor v3)))
ecv3_eval x v3 v4 =
  let v = ap2 Pair v3 v4
      s1 = axPost (Comp cor Fst) sndProj x v
      s2 = cong1 (Comp cor Fst) (sndProj_eval x v)
      s3 = axComp cor Fst v
      s4 = cong1 cor (axFst v3 v4)
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

ecv4_eval : (x v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 ecv4 x (ap2 Pair v3 v4)) (ap1 cor v4)))
ecv4_eval x v3 v4 =
  let v = ap2 Pair v3 v4
      s1 = axPost (Comp cor Snd) sndProj x v
      s2 = cong1 (Comp cor Snd) (sndProj_eval x v)
      s3 = axComp cor Snd v
      s4 = cong1 cor (axSnd v3 v4)
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- y1Generator at NN: produces parEncAxTreeEqNN(cor v1)(cor v2)(cor v3)(cor v4).

innerPair34_eval_NN : (x v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 innerPair34 x (ap2 Pair v3 v4))
                     (ap2 Pair (ap1 cor v3) (ap1 cor v4))))
innerPair34_eval_NN x v3 v4 =
  let v = ap2 Pair v3 v4
      s_fan = axFan ecv3 ecv4 Pair x v
      s_e3  = ecv3_eval x v3 v4
      s_e4  = ecv4_eval x v3 v4
      s1 = congL Pair (ap2 ecv4 x v) s_e3
      s2 = congR Pair (ap1 cor v3) s_e4
  in ruleTrans s_fan (ruleTrans s1 s2)

innerPair234_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 innerPair234 (ap2 Pair v1 v2) (ap2 Pair v3 v4))
                     (ap2 Pair (ap1 cor v2)
                               (ap2 Pair (ap1 cor v3) (ap1 cor v4)))))
innerPair234_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan ecv2 innerPair34 Pair x v
      s_e2  = ecv2_eval v1 v2 v
      s_p34 = innerPair34_eval_NN x v3 v4
      s1 = congL Pair (ap2 innerPair34 x v) s_e2
      s2 = congR Pair (ap1 cor v2) s_p34
  in ruleTrans s_fan (ruleTrans s1 s2)

innerPair1234_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 innerPair1234 (ap2 Pair v1 v2) (ap2 Pair v3 v4))
                     (ap2 Pair (ap1 cor v1)
                               (ap2 Pair (ap1 cor v2)
                                         (ap2 Pair (ap1 cor v3) (ap1 cor v4))))))
innerPair1234_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan ecv1 innerPair234 Pair x v
      s_e1  = ecv1_eval v1 v2 v
      s_p234 = innerPair234_eval_NN v1 v2 v3 v4
      s1 = congL Pair (ap2 innerPair234 x v) s_e1
      s2 = congR Pair (ap1 cor v1) s_p234
  in ruleTrans s_fan (ruleTrans s1 s2)

KT_tagAxTreeEqNN_eval : (x v : Term) ->
  Deriv (atomic (eqn (ap2 KT_tagAxTreeEqNN x v) tagCode_axTreeEqNN))
KT_tagAxTreeEqNN_eval x v =
  ruleTrans (axLift (KT tagCode_axTreeEqNN) x v)
            (axKT (natCode tagAxTreeEqNN) (natCode_isValue tagAxTreeEqNN) x)

y1Generator_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 y1Generator (ap2 Pair v1 v2) (ap2 Pair v3 v4))
                     (parEncAxTreeEqNN (ap1 cor v1)(ap1 cor v2)
                                       (ap1 cor v3)(ap1 cor v4))))
y1Generator_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan KT_tagAxTreeEqNN innerPair1234 Pair x v
      s_kt  = KT_tagAxTreeEqNN_eval x v
      s_inner = innerPair1234_eval_NN v1 v2 v3 v4
      s1 = congL Pair (ap2 innerPair1234 x v) s_kt
      s2 = congR Pair tagCode_axTreeEqNN s_inner
  in ruleTrans s_fan (ruleTrans s1 s2)

------------------------------------------------------------------------
-- y2Generator at NN: produces D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O)).

TreeEq_v1v3_gen_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 TreeEq_v1v3_gen (ap2 Pair v1 v2)(ap2 Pair v3 v4))
                     (ap2 TreeEq v1 v3)))
TreeEq_v1v3_gen_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan ev1 ev3 TreeEq x v
      s_e1  = ev1_eval v1 v2 v
      s_e3  = ev3_eval x v3 v4
      s1 = congL TreeEq (ap2 ev3 x v) s_e1
      s2 = congR TreeEq v1 s_e3
  in ruleTrans s_fan (ruleTrans s1 s2)

TreeEq_v2v4_gen_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 TreeEq_v2v4_gen (ap2 Pair v1 v2)(ap2 Pair v3 v4))
                     (ap2 TreeEq v2 v4)))
TreeEq_v2v4_gen_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan ev2 ev4 TreeEq x v
      s_e2  = ev2_eval v1 v2 v
      s_e4  = ev4_eval x v3 v4
      s1 = congL TreeEq (ap2 ev4 x v) s_e2
      s2 = congR TreeEq v2 s_e4
  in ruleTrans s_fan (ruleTrans s1 s2)

KT_pairOO_eval : (x v : Term) ->
  Deriv (atomic (eqn (ap2 KT_pairOO x v) pairOO))
KT_pairOO_eval x v =
  ruleTrans (axLift (KT pairOO) x v)
            (axKT (nd lf lf) (valNd lf lf valO valO) x)

innerPair_TreeEqv2v4_pairOO_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 innerPair_TreeEqv2v4_pairOO
                          (ap2 Pair v1 v2)(ap2 Pair v3 v4))
                     (ap2 Pair (ap2 TreeEq v2 v4) pairOO)))
innerPair_TreeEqv2v4_pairOO_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan TreeEq_v2v4_gen KT_pairOO Pair x v
      s_t24 = TreeEq_v2v4_gen_eval_NN v1 v2 v3 v4
      s_kt  = KT_pairOO_eval x v
      s1 = congL Pair (ap2 KT_pairOO x v) s_t24
      s2 = congR Pair (ap2 TreeEq v2 v4) s_kt
  in ruleTrans s_fan (ruleTrans s1 s2)

y2Generator_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 y2Generator (ap2 Pair v1 v2)(ap2 Pair v3 v4))
                     (ap2 D_IfLf (ap2 TreeEq v1 v3)
                                 (ap2 Pair (ap2 TreeEq v2 v4) pairOO))))
y2Generator_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan TreeEq_v1v3_gen innerPair_TreeEqv2v4_pairOO D_IfLf x v
      s_t13 = TreeEq_v1v3_gen_eval_NN v1 v2 v3 v4
      s_inner = innerPair_TreeEqv2v4_pairOO_eval_NN v1 v2 v3 v4
      s1 = congL D_IfLf (ap2 innerPair_TreeEqv2v4_pairOO x v) s_t13
      s2 = congR D_IfLf (ap2 TreeEq v1 v3) s_inner
  in ruleTrans s_fan (ruleTrans s1 s2)

------------------------------------------------------------------------
-- inner_dispatch at NN: assembles Pair y1T y2T.

y1T_target : Term -> Term -> Term -> Term -> Term
y1T_target v1 v2 v3 v4 =
  parEncAxTreeEqNN (ap1 cor v1)(ap1 cor v2)(ap1 cor v3)(ap1 cor v4)

y2T_target : Term -> Term -> Term -> Term -> Term
y2T_target v1 v2 v3 v4 =
  ap2 D_IfLf (ap2 TreeEq v1 v3)
             (ap2 Pair (ap2 TreeEq v2 v4) pairOO)

inner_dispatch_eval_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 inner_dispatch (ap2 Pair v1 v2)(ap2 Pair v3 v4))
                     (ap2 Pair (y1T_target v1 v2 v3 v4)
                               (y2T_target v1 v2 v3 v4))))
inner_dispatch_eval_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan y1Generator y2Generator Pair x v
      s_y1  = y1Generator_eval_NN v1 v2 v3 v4
      s_y2  = y2Generator_eval_NN v1 v2 v3 v4
      s1 = congL Pair (ap2 y2Generator x v) s_y1
      s2 = congR Pair (y1T_target v1 v2 v3 v4) s_y2
  in ruleTrans s_fan (ruleTrans s1 s2)

------------------------------------------------------------------------
-- Outer wrapper: D_TreeEq_NN_fun at NN.

KT_tagRuleTrans_eval : (x v : Term) ->
  Deriv (atomic (eqn (ap2 KT_tagRuleTrans x v) tagCode_ruleTrans))
KT_tagRuleTrans_eval x v =
  ruleTrans (axLift (KT tagCode_ruleTrans) x v)
            (axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) x)

D_TreeEq_NN_fun_at_NN : (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap2 D_TreeEq_NN_fun (ap2 Pair v1 v2)(ap2 Pair v3 v4))
                     (ap2 Pair tagCode_ruleTrans
                               (ap2 Pair (y1T_target v1 v2 v3 v4)
                                         (y2T_target v1 v2 v3 v4)))))
D_TreeEq_NN_fun_at_NN v1 v2 v3 v4 =
  let x = ap2 Pair v1 v2
      v = ap2 Pair v3 v4
      s_fan = axFan KT_tagRuleTrans inner_dispatch Pair x v
      s_kt  = KT_tagRuleTrans_eval x v
      s_inner = inner_dispatch_eval_NN v1 v2 v3 v4
      s1 = congL Pair (ap2 inner_dispatch x v) s_kt
      s2 = congR Pair tagCode_ruleTrans s_inner
  in ruleTrans s_fan (ruleTrans s1 s2)
