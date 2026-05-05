{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecPCloseSNNFun -- chain Fun2 at Pair input for Th12 of RecP(s),
-- parametric in (s, Df_F2_s).  Mirrors BRA.Th12RecCloseSNNFun.
--
-- For RecP(s) at (p, Pair v1 v2):
--   axRecPNd: (RecP s) p (Pair v1 v2)
--               = s (Pair p (Pair v1 v2))
--                   (Pair ((RecP s) p v1) ((RecP s) p v2))
--
-- The chain at (p, Pair v1 v2) emits:
--   Pair tagCode_ruleTrans (Pair y1T y2T)
-- where:
--   y1T = parEncAxRecPNd sT (cor p) (cor v1) (cor v2)
--       = Pair tagCode_axRecPNd (Pair sT (Pair (cor p) (Pair (cor v1)(cor v2))))
--   y2T = ap2 Df_F2_s (Pair p (Pair v1 v2))
--                     (Pair ((RecP s) p v1) ((RecP s) p v2))
--
-- The chain dispatches via thmTDispRuleTrans_param to give
--   Pair u1 u4
-- where:
--   u1 = encoded LHS = encoded (RecP s) p (Pair v1 v2)
--   u4 = cor(s (Pair p (Pair v1 v2))(Pair rec_v1 rec_v2))
--      = cor((RecP s) p (Pair v1 v2))    [via cong1 cor (ruleSym axRecPNd)]
--
-- This file defines the chain Fun2 + closure only.

module BRA.Th12RecPCloseSNNFun where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.ReifyClosed using (reifyClosed)
open import BRA.Thm.Tag using (tagAxRecPNd ; tagRuleTrans)
open import BRA.Thm.ThmT using (tagCode_axRecPNd ; tagCode_ruleTrans)

------------------------------------------------------------------------
-- Module parameters.

module Th12RecPCloseSNNFun_Case
  (s : Fun2)
  (s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r s) s)
  (Df_F2_s : Fun2)
  (Df_F2_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Df_F2_s) Df_F2_s)
  where

  ----------------------------------------------------------------------
  -- Encoded constants.

  sT : Term
  sT = reify (codeF2 s)

  recPF : Fun2
  recPF = RecP s

  ----------------------------------------------------------------------
  -- Fun2 building blocks (input is (p, x); we emit functions of p and x).
  --
  --   ap2 (Lift cor) p x = ap1 cor p              (= cor p)
  --   ap2 (Post Snd Pair) p x = ap1 Snd (Pair p x) = x
  --   ap2 (Post Fst Pair) p x = ap1 Fst (Pair p x) = p
  --   ap2 (Post Fst (Post Snd Pair)) p x = Fst x
  --   ap2 (Post Snd (Post Snd Pair)) p x = Snd x

  -- Extract second arg (= x).
  pickX : Fun2
  pickX = Post Snd Pair

  -- Extract Fst of the second arg (= Fst x).
  fstX : Fun2
  fstX = Post Fst pickX

  -- Extract Snd of the second arg (= Snd x).
  sndX : Fun2
  sndX = Post Snd pickX

  -- cor of first arg (= cor p).
  cP : Fun2
  cP = Lift cor

  -- cor of Fst x.
  cFstX : Fun2
  cFstX = Post cor fstX

  -- cor of Snd x.
  cSndX : Fun2
  cSndX = Post cor sndX

  ----------------------------------------------------------------------
  -- Recursive emitters.
  --
  --   ap2 recP_first p x  = ap2 (RecP s) p (Fst x)
  --   ap2 recP_second p x = ap2 (RecP s) p (Snd x)
  --   ap2 recP_pair p x   = Pair ((RecP s) p (Fst x)) ((RecP s) p (Snd x))

  recP_first : Fun2
  recP_first = Fan (Lift I) fstX recPF

  recP_second : Fun2
  recP_second = Fan (Lift I) sndX recPF

  recP_pair : Fun2
  recP_pair = Fan recP_first recP_second Pair

  ----------------------------------------------------------------------
  -- y2 emitter:
  --   ap2 y2_emitter p x = ap2 Df_F2_s (Pair p x) (Pair rec_v1 rec_v2)
  --
  -- y2_emitter = Fan Pair recP_pair Df_F2_s
  --   ap2 _ p x = ap2 Df_F2_s (ap2 Pair p x) (ap2 recP_pair p x)
  --             = ap2 Df_F2_s (Pair p x) (Pair (RecP s p (Fst x)) (RecP s p (Snd x)))

  y2_emitter : Fun2
  y2_emitter = Fan Pair recP_pair Df_F2_s

  ----------------------------------------------------------------------
  -- y1 emitter: builds parEncAxRecPNd sT (cor p) (cor v1) (cor v2) at runtime.
  --
  -- parEncAxRecPNd sT pT aT bT
  --   = Pair tagCode_axRecPNd (Pair sT (Pair pT (Pair aT bT)))

  -- Inner: Pair (cor v1) (cor v2)
  inner_aT_bT : Fun2
  inner_aT_bT = Fan cFstX cSndX Pair

  -- Pair (cor p) (Pair (cor v1)(cor v2))
  inner_pT_ab : Fun2
  inner_pT_ab = Fan cP inner_aT_bT Pair

  -- Pair sT (Pair (cor p) (Pair (cor v1)(cor v2)))
  inner_sT_pT_ab : Fun2
  inner_sT_pT_ab = Fan (Lift (KT sT)) inner_pT_ab Pair

  -- y1_emitter : Pair tagCode_axRecPNd (...)
  y1_emitter : Fun2
  y1_emitter = Fan (Lift (KT tagCode_axRecPNd)) inner_sT_pT_ab Pair

  ----------------------------------------------------------------------
  -- Inner dispatch: Pair y1 y2.

  inner_dispatch : Fun2
  inner_dispatch = Fan y1_emitter y2_emitter Pair

  ----------------------------------------------------------------------
  -- D_RecP_NN_fun_chain : outer wrapper with tagCode_ruleTrans head.

  D_RecP_NN_fun_chain : Fun2
  D_RecP_NN_fun_chain = Fan (Lift (KT tagCode_ruleTrans)) inner_dispatch Pair

  ----------------------------------------------------------------------
  -- Closure proofs.

  -- substF1 n r (KT (reify T)) = KT (reify T) by induction on T.
  KT_reify_substF1_closed : (T : Tree) (n : Nat) (r : Term) ->
    Eq (substF1 n r (KT (reify T))) (KT (reify T))
  KT_reify_substF1_closed lf       n r = refl
  KT_reify_substF1_closed (nd a b) n r =
    eqCong2 (\ a' b' -> Comp2 Pair a' b')
      (KT_reify_substF1_closed a n r)
      (KT_reify_substF1_closed b n r)

  Lift_KT_reify_closed : (T : Tree) (n : Nat) (r : Term) ->
    Eq (substF2 n r (Lift (KT (reify T)))) (Lift (KT (reify T)))
  Lift_KT_reify_closed T n r = eqCong Lift (KT_reify_substF1_closed T n r)

  recPF_closed : (n : Nat) (r : Term) -> Eq (substF2 n r recPF) recPF
  recPF_closed n r = eqCong RecP (s_closed n r)

  -- pickX, fstX, sndX, cP, cFstX, cSndX are all built from closed primitives.
  -- They reduce structurally; closure is refl.
  pickX_closed : (n : Nat) (r : Term) -> Eq (substF2 n r pickX) pickX
  pickX_closed n r = refl

  fstX_closed : (n : Nat) (r : Term) -> Eq (substF2 n r fstX) fstX
  fstX_closed n r = refl

  sndX_closed : (n : Nat) (r : Term) -> Eq (substF2 n r sndX) sndX
  sndX_closed n r = refl

  cP_closed : (n : Nat) (r : Term) -> Eq (substF2 n r cP) cP
  cP_closed n r = refl

  cFstX_closed : (n : Nat) (r : Term) -> Eq (substF2 n r cFstX) cFstX
  cFstX_closed n r = refl

  cSndX_closed : (n : Nat) (r : Term) -> Eq (substF2 n r cSndX) cSndX
  cSndX_closed n r = refl

  recP_first_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r recP_first) recP_first
  recP_first_closed n r = eqCong (Fan (Lift I) fstX) (recPF_closed n r)

  recP_second_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r recP_second) recP_second
  recP_second_closed n r = eqCong (Fan (Lift I) sndX) (recPF_closed n r)

  recP_pair_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r recP_pair) recP_pair
  recP_pair_closed n r =
    eqCong2 (\ a b -> Fan a b Pair) (recP_first_closed n r) (recP_second_closed n r)

  y2_emitter_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r y2_emitter) y2_emitter
  y2_emitter_closed n r =
    eqCong2 (\ rec g -> Fan Pair rec g) (recP_pair_closed n r) (Df_F2_s_closed n r)

  Lift_KT_sT_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Lift (KT sT))) (Lift (KT sT))
  Lift_KT_sT_closed n r = Lift_KT_reify_closed (codeF2 s) n r

  Lift_KT_tagAxRecPNd_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Lift (KT tagCode_axRecPNd))) (Lift (KT tagCode_axRecPNd))
  Lift_KT_tagAxRecPNd_closed n r = Lift_KT_reify_closed (natCode tagAxRecPNd) n r

  Lift_KT_tagRuleTrans_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Lift (KT tagCode_ruleTrans))) (Lift (KT tagCode_ruleTrans))
  Lift_KT_tagRuleTrans_closed n r = Lift_KT_reify_closed (natCode tagRuleTrans) n r

  inner_aT_bT_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r inner_aT_bT) inner_aT_bT
  inner_aT_bT_closed n r = refl

  inner_pT_ab_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r inner_pT_ab) inner_pT_ab
  inner_pT_ab_closed n r = refl

  inner_sT_pT_ab_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r inner_sT_pT_ab) inner_sT_pT_ab
  inner_sT_pT_ab_closed n r =
    eqCong (\ k -> Fan k inner_pT_ab Pair) (Lift_KT_sT_closed n r)

  y1_emitter_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r y1_emitter) y1_emitter
  y1_emitter_closed n r =
    eqCong2 (\ k g -> Fan k g Pair)
      (Lift_KT_tagAxRecPNd_closed n r) (inner_sT_pT_ab_closed n r)

  inner_dispatch_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r inner_dispatch) inner_dispatch
  inner_dispatch_closed n r =
    eqCong2 (\ a b -> Fan a b Pair) (y1_emitter_closed n r) (y2_emitter_closed n r)

  D_RecP_NN_fun_chain_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r D_RecP_NN_fun_chain) D_RecP_NN_fun_chain
  D_RecP_NN_fun_chain_closed n r =
    eqCong2 (\ k g -> Fan k g Pair)
      (Lift_KT_tagRuleTrans_closed n r) (inner_dispatch_closed n r)
