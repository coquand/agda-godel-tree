{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecCloseSNNFun -- chain Fun1 at Pair input for Th12 of Rec(z, s),
-- parametric in (z, s, Df_F2_s).  Mirrors BRA.Th12TreeEqNNFun.
--
-- For Rec(z, s) at Pair input (a, b):
--   axRecNd: (Rec z s) (Pair a b) = s (Pair a b) (Pair (Rec z s a) (Rec z s b))
--
-- The chain at Pair input emits:
--   Pair tagCode_ruleTrans (Pair y1T y2T)
-- where:
--   y1T = parEncAxRecNd zT sT (cor a) (cor b)
--       = encoded axRecNd payload at cor-wrapped args
--   y2T = ap2 Df_F2_s (Pair a b) (Pair (Rec z s a) (Rec z s b))
--       = Df_F2_s applied at the post-axRecNd args
--
-- The chain dispatches via thmTDispRuleTrans_param to give
--   Pair u1 u4
-- where:
--   u1 = encoded LHS of axRecNd = encoded (Rec z s)(Pair a b)
--   u4 = cor(s (Pair a b)(Pair rec_a rec_b))
--      = cor((Rec z s)(Pair a b))   [via cong1 cor (ruleSym axRecNd)]
--
-- Bridges (cor on encoded Pair, ruleSym axRecNd) live in the BasePP file.
--
-- This file defines the chain Fun1 + closure only.

module BRA.Th12RecCloseSNNFun where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.ReifyClosed using (reifyClosed)
open import BRA.Thm.Tag using (tagAxRecNd ; tagRuleTrans)
open import BRA.Thm.ThmT using (tagCode_axRecNd ; tagCode_ruleTrans)

------------------------------------------------------------------------
-- Module parameters.
--
-- We're parametric in:
--   * z : Term (the lf-value of the Rec).  Closure assumed.
--   * s : Fun2 (the step Fun2).  Closure assumed.
--   * Df_F2_s : Fun2 (the Th12 chain Fun2 for s, recursively obtained).
--   * Df_F2_s_closed : closure of Df_F2_s.

module Th12RecCloseSNNFun_Case
  (z : Term)
  (s : Fun2)
  (z_closed : (n : Nat) (r : Term) -> Eq (subst n r z) z)
  (s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r s) s)
  (Df_F2_s : Fun2)
  (Df_F2_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Df_F2_s) Df_F2_s)
  where

  ----------------------------------------------------------------------
  -- Encoded constants.

  zT : Term
  zT = reify (code z)

  sT : Term
  sT = reify (codeF2 s)

  recF : Fun1
  recF = Rec z s

  ----------------------------------------------------------------------
  -- Fun1 building blocks.

  -- Plain extractors (Fun1 from input x = Pair v1 v2).
  --   ap1 fst1 (Pair v1 v2) = v1
  --   ap1 snd1 (Pair v1 v2) = v2

  -- Cor-wrapped extractors:
  --   ap1 cFst (Pair v1 v2) = cor v1
  --   ap1 cSnd (Pair v1 v2) = cor v2
  cFst : Fun1
  cFst = Comp cor Fst

  cSnd : Fun1
  cSnd = Comp cor Snd

  -- Recursive applications:
  --   ap1 recFst (Pair v1 v2) = ap1 recF v1 = recF v1
  --   ap1 recSnd (Pair v1 v2) = ap1 recF v2 = recF v2
  recFst : Fun1
  recFst = Comp recF Fst

  recSnd : Fun1
  recSnd = Comp recF Snd

  -- Recursive Pair: ap1 recPair x = Pair (recF v1) (recF v2)
  recPair : Fun1
  recPair = Comp2 Pair recFst recSnd

  ----------------------------------------------------------------------
  -- y2 emitter:
  --   ap1 y2_emitter (Pair v1 v2) = ap2 Df_F2_s (Pair v1 v2) (Pair rec_v1 rec_v2)
  --
  -- y2_emitter = Comp2 Df_F2_s I recPair
  --   ap1 (Comp2 Df_F2_s I recPair) x = ap2 Df_F2_s (ap1 I x) (ap1 recPair x)
  --                                    = ap2 Df_F2_s x (Pair (recF (Fst x))(recF (Snd x)))

  y2_emitter : Fun1
  y2_emitter = Comp2 Df_F2_s I recPair

  ----------------------------------------------------------------------
  -- y1 emitter: builds parEncAxRecNd zT sT (cor v1) (cor v2) at runtime.
  --
  -- parEncAxRecNd zT sT aT bT = Pair tagCode_axRecNd (Pair zT (Pair sT (Pair aT bT)))
  --
  -- We build this as a depth-4 Pair via Comp2 Pair (KT _) (...).

  -- Inner: Pair (cor v1) (cor v2)
  inner_aT_bT : Fun1
  inner_aT_bT = Comp2 Pair cFst cSnd

  -- Pair sT (Pair (cor v1)(cor v2))
  inner_sT_ab : Fun1
  inner_sT_ab = Comp2 Pair (KT sT) inner_aT_bT

  -- Pair zT (Pair sT (Pair ab))
  inner_zT_sT_ab : Fun1
  inner_zT_sT_ab = Comp2 Pair (KT zT) inner_sT_ab

  -- y1_emitter : ap1 _ x = parEncAxRecNd zT sT (cor v1)(cor v2)
  y1_emitter : Fun1
  y1_emitter = Comp2 Pair (KT tagCode_axRecNd) inner_zT_sT_ab

  ----------------------------------------------------------------------
  -- Inner dispatch: combines y1 and y2 with Pair.

  inner_dispatch : Fun1
  inner_dispatch = Comp2 Pair y1_emitter y2_emitter

  ----------------------------------------------------------------------
  -- D_Rec_NN_fun_chain : outer wrapper with tagCode_ruleTrans head.
  --
  -- ap1 D_Rec_NN_fun_chain (Pair v1 v2) =BRA
  --   Pair tagCode_ruleTrans (Pair y1T y2T)
  --
  -- where y1T = parEncAxRecNd zT sT (cor v1)(cor v2)
  --       y2T = ap2 Df_F2_s (Pair v1 v2)(Pair rec_v1 rec_v2)

  D_Rec_NN_fun_chain : Fun1
  D_Rec_NN_fun_chain = Comp2 Pair (KT tagCode_ruleTrans) inner_dispatch

  ----------------------------------------------------------------------
  -- Closure: D_Rec_NN_fun_chain is substF1-invariant.
  --
  -- Each component is closed:
  --   * cor, cFst, cSnd, I, Fst, Snd, Pair: structural (refl)
  --   * recF = Rec z s: closed iff z and s are closed (z_closed, s_closed)
  --   * recFst, recSnd, recPair: closed because recF is closed
  --   * KT zT, KT sT, KT tagCode_axRecNd, KT tagCode_ruleTrans:
  --       closed because the natCode/code-of-closed-term trees are closed
  --       via reifyClosed.
  --   * Comp2, Comp: closed if subterms are closed.

  recF_closed : (n : Nat) (r : Term) -> Eq (substF1 n r recF) recF
  recF_closed n r = eqCong2 Rec (z_closed n r) (s_closed n r)

  recFst_closed : (n : Nat) (r : Term) -> Eq (substF1 n r recFst) recFst
  recFst_closed n r = eqCong (\ f -> Comp f Fst) (recF_closed n r)

  recSnd_closed : (n : Nat) (r : Term) -> Eq (substF1 n r recSnd) recSnd
  recSnd_closed n r = eqCong (\ f -> Comp f Snd) (recF_closed n r)

  recPair_closed : (n : Nat) (r : Term) -> Eq (substF1 n r recPair) recPair
  recPair_closed n r =
    eqCong2 (\ a b -> Comp2 Pair a b) (recFst_closed n r) (recSnd_closed n r)

  y2_emitter_closed : (n : Nat) (r : Term) -> Eq (substF1 n r y2_emitter) y2_emitter
  y2_emitter_closed n r =
    eqCong2 (\ g h -> Comp2 g I h) (Df_F2_s_closed n r) (recPair_closed n r)

  -- substF1 n r (KT (reify T)) = KT (reify T) by induction on T.
  -- KT (reify T) reduces structurally on T (lf -> Z; nd a b -> Comp2 Pair (KT (reify a))(KT (reify b))),
  -- and substF1 then reduces on the resulting Fun1 expression.
  KT_reify_substF1_closed : (T : Tree) (n : Nat) (r : Term) ->
    Eq (substF1 n r (KT (reify T))) (KT (reify T))
  KT_reify_substF1_closed lf       n r = refl
  KT_reify_substF1_closed (nd a b) n r =
    eqCong2 (\ a' b' -> Comp2 Pair a' b')
      (KT_reify_substF1_closed a n r)
      (KT_reify_substF1_closed b n r)

  KT_zT_closed : (n : Nat) (r : Term) -> Eq (substF1 n r (KT zT)) (KT zT)
  KT_zT_closed n r = KT_reify_substF1_closed (code z) n r

  KT_sT_closed : (n : Nat) (r : Term) -> Eq (substF1 n r (KT sT)) (KT sT)
  KT_sT_closed n r = KT_reify_substF1_closed (codeF2 s) n r

  KT_tagAxRecNd_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r (KT tagCode_axRecNd)) (KT tagCode_axRecNd)
  KT_tagAxRecNd_closed n r = KT_reify_substF1_closed (natCode tagAxRecNd) n r

  KT_tagRuleTrans_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r (KT tagCode_ruleTrans)) (KT tagCode_ruleTrans)
  KT_tagRuleTrans_closed n r = KT_reify_substF1_closed (natCode tagRuleTrans) n r

  inner_aT_bT_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r inner_aT_bT) inner_aT_bT
  inner_aT_bT_closed n r = refl

  inner_sT_ab_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r inner_sT_ab) inner_sT_ab
  inner_sT_ab_closed n r =
    eqCong (\ f -> Comp2 Pair f inner_aT_bT) (KT_sT_closed n r)

  inner_zT_sT_ab_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r inner_zT_sT_ab) inner_zT_sT_ab
  inner_zT_sT_ab_closed n r =
    eqCong2 (\ f g -> Comp2 Pair f g) (KT_zT_closed n r) (inner_sT_ab_closed n r)

  y1_emitter_closed : (n : Nat) (r : Term) -> Eq (substF1 n r y1_emitter) y1_emitter
  y1_emitter_closed n r =
    eqCong2 (\ f g -> Comp2 Pair f g)
      (KT_tagAxRecNd_closed n r) (inner_zT_sT_ab_closed n r)

  inner_dispatch_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r inner_dispatch) inner_dispatch
  inner_dispatch_closed n r =
    eqCong2 (\ f g -> Comp2 Pair f g)
      (y1_emitter_closed n r) (y2_emitter_closed n r)

  D_Rec_NN_fun_chain_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r D_Rec_NN_fun_chain) D_Rec_NN_fun_chain
  D_Rec_NN_fun_chain_closed n r =
    eqCong2 (\ f g -> Comp2 Pair f g)
      (KT_tagRuleTrans_closed n r) (inner_dispatch_closed n r)
