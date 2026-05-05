{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecCloseSNNReduce -- BRA reduction of D_Rec_NN_fun_chain at Pair input.
--
-- Proves at any (v1 v2 : Term):
--   D_Rec_NN_fun_chain_at_Pair v1 v2 :
--     ap1 D_Rec_NN_fun_chain (ap2 Pair v1 v2) =BRA
--       Pair tagCode_ruleTrans (Pair y1T_target y2T_target)
-- where
--   y1T_target v1 v2 = parEncAxRecNd zT sT (cor v1) (cor v2)
--   y2T_target v1 v2 = ap2 Df_F2_s (Pair v1 v2)
--                                  (Pair (ap1 recF v1) (ap1 recF v2))
--
-- Strategy: peel the Comp2 Pair (KT _) (...) layers via axComp2 + axKT,
-- then descend into y1_emitter and y2_emitter (Comp2 Df_F2_s I recPair),
-- composing with ruleTrans / cong.

module BRA.Th12RecCloseSNNReduce where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxRecNd ; tagRuleTrans)
open import BRA.Thm.ThmT using (tagCode_axRecNd ; tagCode_ruleTrans)
open import BRA.Thm12.Param.AxRecNd using (parEncAxRecNd)

import BRA.Th12RecCloseSNNFun

module Th12RecCloseSNNReduce_Case
  (z : Term)
  (s : Fun2)
  (z_closed : (n : Nat) (r : Term) -> Eq (subst n r z) z)
  (s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r s) s)
  (Df_F2_s : Fun2)
  (Df_F2_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Df_F2_s) Df_F2_s)
  where

  open BRA.Th12RecCloseSNNFun.Th12RecCloseSNNFun_Case
    z s z_closed s_closed Df_F2_s Df_F2_s_closed
    public

  ----------------------------------------------------------------------
  -- Targets (matching the chain's runtime emission at Pair input).

  y1T_target : Term -> Term -> Term
  y1T_target v1 v2 = parEncAxRecNd zT sT (ap1 cor v1) (ap1 cor v2)

  y2T_target : Term -> Term -> Term
  y2T_target v1 v2 =
    ap2 Df_F2_s (ap2 Pair v1 v2)
                (ap2 Pair (ap1 recF v1) (ap1 recF v2))

  ----------------------------------------------------------------------
  -- Reductions of the leaf Fun1's at Pair input.

  cFst_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 cFst (ap2 Pair v1 v2)) (ap1 cor v1)))
  cFst_at_Pair v1 v2 =
    ruleTrans (axComp cor Fst (ap2 Pair v1 v2))
              (cong1 cor (axFst v1 v2))

  cSnd_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 cSnd (ap2 Pair v1 v2)) (ap1 cor v2)))
  cSnd_at_Pair v1 v2 =
    ruleTrans (axComp cor Snd (ap2 Pair v1 v2))
              (cong1 cor (axSnd v1 v2))

  recFst_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 recFst (ap2 Pair v1 v2)) (ap1 recF v1)))
  recFst_at_Pair v1 v2 =
    ruleTrans (axComp recF Fst (ap2 Pair v1 v2))
              (cong1 recF (axFst v1 v2))

  recSnd_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 recSnd (ap2 Pair v1 v2)) (ap1 recF v2)))
  recSnd_at_Pair v1 v2 =
    ruleTrans (axComp recF Snd (ap2 Pair v1 v2))
              (cong1 recF (axSnd v1 v2))

  recPair_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 recPair (ap2 Pair v1 v2))
                       (ap2 Pair (ap1 recF v1) (ap1 recF v2))))
  recPair_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair recFst recSnd x
        s2 = recFst_at_Pair v1 v2
        s3 = recSnd_at_Pair v1 v2
        s4 = congL Pair (ap1 recSnd x) s2
        s5 = congR Pair (ap1 recF v1) s3
    in ruleTrans s1 (ruleTrans s4 s5)

  ----------------------------------------------------------------------
  -- y2_emitter at Pair input.

  y2_emitter_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 y2_emitter (ap2 Pair v1 v2)) (y2T_target v1 v2)))
  y2_emitter_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Df_F2_s I recPair x
        s2 : Deriv (atomic (eqn (ap1 I x) x))
        s2 = axI x
        s3 : Deriv (atomic (eqn (ap2 Df_F2_s (ap1 I x) (ap1 recPair x))
                                (ap2 Df_F2_s x (ap1 recPair x))))
        s3 = congL Df_F2_s (ap1 recPair x) s2
        s4 : Deriv (atomic (eqn (ap2 Df_F2_s x (ap1 recPair x))
                                (y2T_target v1 v2)))
        s4 = congR Df_F2_s x (recPair_at_Pair v1 v2)
    in ruleTrans s1 (ruleTrans s3 s4)

  ----------------------------------------------------------------------
  -- y1_emitter at Pair input.

  KT_eval : (T : Tree) (x : Term) ->
    Deriv (atomic (eqn (ap1 (KT (reify T)) x) (reify T)))
  KT_eval T x = axKT T x

  inner_aT_bT_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 inner_aT_bT (ap2 Pair v1 v2))
                       (ap2 Pair (ap1 cor v1) (ap1 cor v2))))
  inner_aT_bT_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair cFst cSnd x
        s2 = cFst_at_Pair v1 v2
        s3 = cSnd_at_Pair v1 v2
        s4 = congL Pair (ap1 cSnd x) s2
        s5 = congR Pair (ap1 cor v1) s3
    in ruleTrans s1 (ruleTrans s4 s5)

  inner_sT_ab_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 inner_sT_ab (ap2 Pair v1 v2))
                       (ap2 Pair sT (ap2 Pair (ap1 cor v1) (ap1 cor v2)))))
  inner_sT_ab_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair (KT sT) inner_aT_bT x
        s2 = KT_eval (codeF2 s) x
        s3 = inner_aT_bT_at_Pair v1 v2
        s4 = congL Pair (ap1 inner_aT_bT x) s2
        s5 = congR Pair sT s3
    in ruleTrans s1 (ruleTrans s4 s5)

  inner_zT_sT_ab_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 inner_zT_sT_ab (ap2 Pair v1 v2))
                       (ap2 Pair zT
                          (ap2 Pair sT
                             (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
  inner_zT_sT_ab_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair (KT zT) inner_sT_ab x
        s2 = KT_eval (code z) x
        s3 = inner_sT_ab_at_Pair v1 v2
        s4 = congL Pair (ap1 inner_sT_ab x) s2
        s5 = congR Pair zT s3
    in ruleTrans s1 (ruleTrans s4 s5)

  y1_emitter_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 y1_emitter (ap2 Pair v1 v2)) (y1T_target v1 v2)))
  y1_emitter_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair (KT tagCode_axRecNd) inner_zT_sT_ab x
        s2 = KT_eval (natCode tagAxRecNd) x
        s3 = inner_zT_sT_ab_at_Pair v1 v2
        s4 = congL Pair (ap1 inner_zT_sT_ab x) s2
        s5 = congR Pair tagCode_axRecNd s3
    in ruleTrans s1 (ruleTrans s4 s5)

  ----------------------------------------------------------------------
  -- inner_dispatch at Pair input.

  inner_dispatch_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 inner_dispatch (ap2 Pair v1 v2))
                       (ap2 Pair (y1T_target v1 v2) (y2T_target v1 v2))))
  inner_dispatch_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair y1_emitter y2_emitter x
        s2 = y1_emitter_at_Pair v1 v2
        s3 = y2_emitter_at_Pair v1 v2
        s4 = congL Pair (ap1 y2_emitter x) s2
        s5 = congR Pair (y1T_target v1 v2) s3
    in ruleTrans s1 (ruleTrans s4 s5)

  ----------------------------------------------------------------------
  -- Outer wrapper: D_Rec_NN_fun_chain at Pair input.

  D_Rec_NN_fun_chain_at_Pair : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 D_Rec_NN_fun_chain (ap2 Pair v1 v2))
                       (ap2 Pair tagCode_ruleTrans
                          (ap2 Pair (y1T_target v1 v2) (y2T_target v1 v2)))))
  D_Rec_NN_fun_chain_at_Pair v1 v2 =
    let x = ap2 Pair v1 v2
        s1 = axComp2 Pair (KT tagCode_ruleTrans) inner_dispatch x
        s2 = KT_eval (natCode tagRuleTrans) x
        s3 = inner_dispatch_at_Pair v1 v2
        s4 = congL Pair (ap1 inner_dispatch x) s2
        s5 = congR Pair tagCode_ruleTrans s3
    in ruleTrans s1 (ruleTrans s4 s5)
