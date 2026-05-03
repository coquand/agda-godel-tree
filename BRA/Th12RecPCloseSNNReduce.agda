{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecPCloseSNNReduce -- BRA reduction of D_RecP_NN_fun_chain at (p, Pair v1 v2).
--
-- Proves at any (p v1 v2 : Term):
--   D_RecP_NN_fun_chain_at_Pair p v1 v2 :
--     ap2 D_RecP_NN_fun_chain p (ap2 Pair v1 v2) =BRA
--       Pair tagCode_ruleTrans (Pair y1T_target y2T_target)
-- where
--   y1T_target = parEncAxRecPNd sT (cor p) (cor v1) (cor v2)
--   y2T_target = ap2 Df_F2_s (Pair p (Pair v1 v2))
--                            (Pair ((RecP s) p v1) ((RecP s) p v2))

module BRA.Th12RecPCloseSNNReduce where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxRecPNd ; tagRuleTrans)
open import BRA.Thm.ThmT using (tagCode_axRecPNd ; tagCode_ruleTrans)

import BRA.Th12RecPCloseSNNFun

module Th12RecPCloseSNNReduce_Case
  (s : Fun2)
  (s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r s) s)
  (Df_F2_s : Fun2)
  (Df_F2_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Df_F2_s) Df_F2_s)
  where

  open BRA.Th12RecPCloseSNNFun.Th12RecPCloseSNNFun_Case s s_closed Df_F2_s Df_F2_s_closed
    public

  ----------------------------------------------------------------------
  -- Targets at (p, Pair v1 v2).

  parEncAxRecPNd_target : Term -> Term -> Term -> Term
  parEncAxRecPNd_target p v1 v2 =
    ap2 Pair tagCode_axRecPNd
      (ap2 Pair sT
        (ap2 Pair (ap1 cor p)
          (ap2 Pair (ap1 cor v1) (ap1 cor v2))))

  y1T_target : Term -> Term -> Term -> Term
  y1T_target p v1 v2 = parEncAxRecPNd_target p v1 v2

  y2T_target : Term -> Term -> Term -> Term
  y2T_target p v1 v2 =
    ap2 Df_F2_s (ap2 Pair p (ap2 Pair v1 v2))
                (ap2 Pair (ap2 recPF p v1) (ap2 recPF p v2))

  ----------------------------------------------------------------------
  -- Helper reductions.

  pickX_eval : (p x : Term) ->
    Deriv (atomic (eqn (ap2 pickX p x) x))
  pickX_eval p x = ruleTrans (axPost Snd Pair p x) (axSnd p x)

  fstX_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 fstX p (ap2 Pair v1 v2)) v1))
  fstX_eval p v1 v2 =
    let s1 = axPost Fst pickX p (ap2 Pair v1 v2)
        s2 = cong1 Fst (pickX_eval p (ap2 Pair v1 v2))
        s3 = axFst v1 v2
    in ruleTrans s1 (ruleTrans s2 s3)

  sndX_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 sndX p (ap2 Pair v1 v2)) v2))
  sndX_eval p v1 v2 =
    let s1 = axPost Snd pickX p (ap2 Pair v1 v2)
        s2 = cong1 Snd (pickX_eval p (ap2 Pair v1 v2))
        s3 = axSnd v1 v2
    in ruleTrans s1 (ruleTrans s2 s3)

  cP_eval : (p x : Term) ->
    Deriv (atomic (eqn (ap2 cP p x) (ap1 cor p)))
  cP_eval p x = axLift cor p x

  cFstX_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 cFstX p (ap2 Pair v1 v2)) (ap1 cor v1)))
  cFstX_eval p v1 v2 =
    let s1 = axPost cor fstX p (ap2 Pair v1 v2)
        s2 = cong1 cor (fstX_eval p v1 v2)
    in ruleTrans s1 s2

  cSndX_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 cSndX p (ap2 Pair v1 v2)) (ap1 cor v2)))
  cSndX_eval p v1 v2 =
    let s1 = axPost cor sndX p (ap2 Pair v1 v2)
        s2 = cong1 cor (sndX_eval p v1 v2)
    in ruleTrans s1 s2

  Lift_I_eval : (p x : Term) ->
    Deriv (atomic (eqn (ap2 (Lift I) p x) p))
  Lift_I_eval p x = ruleTrans (axLift I p x) (axI p)

  KT_eval : (T : Tree) (x : Term) ->
    Deriv (atomic (eqn (ap1 (KT (reify T)) x) (reify T)))
  KT_eval T x = axKT T x

  Lift_KT_eval : (T : Tree) (p x : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (KT (reify T))) p x) (reify T)))
  Lift_KT_eval T p x = ruleTrans (axLift (KT (reify T)) p x) (KT_eval T p)

  ----------------------------------------------------------------------
  -- recP_first / recP_second / recP_pair at (p, Pair v1 v2).

  recP_first_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 recP_first p (ap2 Pair v1 v2)) (ap2 recPF p v1)))
  recP_first_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan (Lift I) fstX recPF p x
        s_li  = Lift_I_eval p x
        s_fx  = fstX_eval p v1 v2
        s1 = congL recPF (ap2 fstX p x) s_li
        s2 = congR recPF p s_fx
    in ruleTrans s_fan (ruleTrans s1 s2)

  recP_second_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 recP_second p (ap2 Pair v1 v2)) (ap2 recPF p v2)))
  recP_second_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan (Lift I) sndX recPF p x
        s_li  = Lift_I_eval p x
        s_sx  = sndX_eval p v1 v2
        s1 = congL recPF (ap2 sndX p x) s_li
        s2 = congR recPF p s_sx
    in ruleTrans s_fan (ruleTrans s1 s2)

  recP_pair_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 recP_pair p (ap2 Pair v1 v2))
                       (ap2 Pair (ap2 recPF p v1) (ap2 recPF p v2))))
  recP_pair_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan recP_first recP_second Pair p x
        s_r1  = recP_first_eval p v1 v2
        s_r2  = recP_second_eval p v1 v2
        s1 = congL Pair (ap2 recP_second p x) s_r1
        s2 = congR Pair (ap2 recPF p v1) s_r2
    in ruleTrans s_fan (ruleTrans s1 s2)

  ----------------------------------------------------------------------
  -- y2_emitter at (p, Pair v1 v2).

  y2_emitter_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 y2_emitter p (ap2 Pair v1 v2)) (y2T_target p v1 v2)))
  y2_emitter_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan Pair recP_pair Df_F2_s p x
        -- ap2 Pair p x evaluates to ap2 Pair p x trivially (axPair-style; just refl).
        -- Actually we need a proof that ap2 Pair p x = Pair p x (the Term form).
        -- These are syntactically the same.
        s_pair : Deriv (atomic (eqn (ap2 Pair p x) (ap2 Pair p x)))
        s_pair = axRefl (ap2 Pair p x)
        s_rp  = recP_pair_eval p v1 v2
        s1 = congL Df_F2_s (ap2 recP_pair p x) s_pair
        s2 = congR Df_F2_s (ap2 Pair p x) s_rp
    in ruleTrans s_fan (ruleTrans s1 s2)

  ----------------------------------------------------------------------
  -- y1_emitter at (p, Pair v1 v2).

  inner_aT_bT_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 inner_aT_bT p (ap2 Pair v1 v2))
                       (ap2 Pair (ap1 cor v1) (ap1 cor v2))))
  inner_aT_bT_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan cFstX cSndX Pair p x
        s_c1  = cFstX_eval p v1 v2
        s_c2  = cSndX_eval p v1 v2
        s1 = congL Pair (ap2 cSndX p x) s_c1
        s2 = congR Pair (ap1 cor v1) s_c2
    in ruleTrans s_fan (ruleTrans s1 s2)

  inner_pT_ab_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 inner_pT_ab p (ap2 Pair v1 v2))
                       (ap2 Pair (ap1 cor p)
                          (ap2 Pair (ap1 cor v1) (ap1 cor v2)))))
  inner_pT_ab_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan cP inner_aT_bT Pair p x
        s_cp  = cP_eval p x
        s_inner = inner_aT_bT_eval p v1 v2
        s1 = congL Pair (ap2 inner_aT_bT p x) s_cp
        s2 = congR Pair (ap1 cor p) s_inner
    in ruleTrans s_fan (ruleTrans s1 s2)

  inner_sT_pT_ab_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 inner_sT_pT_ab p (ap2 Pair v1 v2))
                       (ap2 Pair sT
                          (ap2 Pair (ap1 cor p)
                             (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
  inner_sT_pT_ab_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan (Lift (KT sT)) inner_pT_ab Pair p x
        s_kt  = Lift_KT_eval (codeF2 s) p x
        s_inner = inner_pT_ab_eval p v1 v2
        s1 = congL Pair (ap2 inner_pT_ab p x) s_kt
        s2 = congR Pair sT s_inner
    in ruleTrans s_fan (ruleTrans s1 s2)

  y1_emitter_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 y1_emitter p (ap2 Pair v1 v2)) (y1T_target p v1 v2)))
  y1_emitter_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan (Lift (KT tagCode_axRecPNd)) inner_sT_pT_ab Pair p x
        s_kt  = Lift_KT_eval (natCode tagAxRecPNd) p x
        s_inner = inner_sT_pT_ab_eval p v1 v2
        s1 = congL Pair (ap2 inner_sT_pT_ab p x) s_kt
        s2 = congR Pair tagCode_axRecPNd s_inner
    in ruleTrans s_fan (ruleTrans s1 s2)

  ----------------------------------------------------------------------
  -- inner_dispatch at (p, Pair v1 v2).

  inner_dispatch_eval : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 inner_dispatch p (ap2 Pair v1 v2))
                       (ap2 Pair (y1T_target p v1 v2) (y2T_target p v1 v2))))
  inner_dispatch_eval p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan y1_emitter y2_emitter Pair p x
        s_y1  = y1_emitter_eval p v1 v2
        s_y2  = y2_emitter_eval p v1 v2
        s1 = congL Pair (ap2 y2_emitter p x) s_y1
        s2 = congR Pair (y1T_target p v1 v2) s_y2
    in ruleTrans s_fan (ruleTrans s1 s2)

  ----------------------------------------------------------------------
  -- Outer wrapper.

  D_RecP_NN_fun_chain_at_Pair : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 D_RecP_NN_fun_chain p (ap2 Pair v1 v2))
                       (ap2 Pair tagCode_ruleTrans
                          (ap2 Pair (y1T_target p v1 v2) (y2T_target p v1 v2)))))
  D_RecP_NN_fun_chain_at_Pair p v1 v2 =
    let x = ap2 Pair v1 v2
        s_fan = axFan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair p x
        s_kt  = Lift_KT_eval (natCode tagRuleTrans) p x
        s_inner = inner_dispatch_eval p v1 v2
        s1 = congL Pair (ap2 inner_dispatch p x) s_kt
        s2 = congR Pair tagCode_ruleTrans s_inner
    in ruleTrans s_fan (ruleTrans s1 s2)
