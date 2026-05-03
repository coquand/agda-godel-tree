{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12TreeEqNNFun -- closed Fun2 for the (Pair, Pair) NN case of
-- Theorem 12 for TreeEq.
--
-- Redesigned (Phase 4 close): emits a chain Df at NN input.
--
--   ap2 D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4) =BRA
--     Pair tagCode_ruleTrans (Pair y1T y2T)
--
-- where:
--   y1T = parEncAxTreeEqNN (cor v1)(cor v2)(cor v3)(cor v4)
--       = encoded axTreeEqNN dispatch payload (cor-wrapped args).
--   y2T = ap2 D_IfLf (ap2 TreeEq v1 v3)
--                    (ap2 Pair (ap2 TreeEq v2 v4)(ap2 Pair O O))
--       = opaque-applied-form Fun2-image whose thmT-image comes from
--         Th12_F2_IfLf at (TreeEq v1 v3, Pair (TreeEq v2 v4)(Pair O O)).
--
-- The chain Df dispatches via thmTDispRuleTrans_param to give
-- Pair u1 u4 where:
--   u1 = parOutAxTreeEqNN's LHS slot at the cor-wrapped inputs
--      = mkAp2T cf2 (mkAp2T pCT (cor v1)(cor v2))(mkAp2T pCT (cor v3)(cor v4))
--      = mkAp2T cf2 (cor (Pair v1 v2))(cor (Pair v3 v4))      [via corOfPair x2]
--      = LHS slot of codeFTeq2_TreeEq (Pair v1 v2)(Pair v3 v4)
--   u4 = cor (IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O)))
--      = cor (TreeEq (Pair v1 v2)(Pair v3 v4))                [via cong1 cor (ruleSym axTreeEqNN)]
--
-- This file delivers D_TreeEq_NN_fun + closure only.  The reduction
-- proof at NN input lives in BRA/Th12TreeEqNNReduce.agda; the basePP_imp
-- proof in BRA/Th12TreeEqBasePP.agda.
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.Th12TreeEqNNFun where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxTreeEqNN ; tagRuleTrans)
open import BRA.Thm.ThmT using (tagCode_axTreeEqNN ; tagCode_ruleTrans)
open import BRA.Thm12.Parts.IfLf using (D_IfLf)

------------------------------------------------------------------------
-- Fun2 building blocks.

-- Project second arg of Fun2: ap2 sndProj x v = v.
sndProj : Fun2
sndProj = Post Snd Pair

-- Plain extractors (return v_i = i-th projection of (orig, recs)).
ev1 : Fun2
ev1 = Lift Fst                  -- ap2 _ x v = Fst x

ev2 : Fun2
ev2 = Lift Snd                  -- ap2 _ x v = Snd x

ev3 : Fun2
ev3 = Post Fst sndProj          -- ap2 _ x v = Fst v

ev4 : Fun2
ev4 = Post Snd sndProj          -- ap2 _ x v = Snd v

-- cor-wrapped extractors.
ecv1 : Fun2
ecv1 = Lift (Comp cor Fst)      -- ap2 _ x v = cor (Fst x)

ecv2 : Fun2
ecv2 = Lift (Comp cor Snd)      -- ap2 _ x v = cor (Snd x)

ecv3 : Fun2
ecv3 = Post (Comp cor Fst) sndProj  -- ap2 _ x v = cor (Fst v)

ecv4 : Fun2
ecv4 = Post (Comp cor Snd) sndProj  -- ap2 _ x v = cor (Snd v)

------------------------------------------------------------------------
-- y1Generator: at (Pair v1 v2, Pair v3 v4), produces
--   Pair tagCode_axTreeEqNN
--        (Pair (cor v1) (Pair (cor v2) (Pair (cor v3) (cor v4))))
-- = parEncAxTreeEqNN (cor v1)(cor v2)(cor v3)(cor v4).

innerPair34 : Fun2
innerPair34 = Fan ecv3 ecv4 Pair

innerPair234 : Fun2
innerPair234 = Fan ecv2 innerPair34 Pair

innerPair1234 : Fun2
innerPair1234 = Fan ecv1 innerPair234 Pair

KT_tagAxTreeEqNN : Fun2
KT_tagAxTreeEqNN = Lift (KT tagCode_axTreeEqNN)

y1Generator : Fun2
y1Generator = Fan KT_tagAxTreeEqNN innerPair1234 Pair

------------------------------------------------------------------------
-- y2Generator: at (Pair v1 v2, Pair v3 v4), produces
--   ap2 D_IfLf (ap2 TreeEq v1 v3)
--              (ap2 Pair (ap2 TreeEq v2 v4)(ap2 Pair O O))

TreeEq_v1v3_gen : Fun2
TreeEq_v1v3_gen = Fan ev1 ev3 TreeEq

TreeEq_v2v4_gen : Fun2
TreeEq_v2v4_gen = Fan ev2 ev4 TreeEq

pairOO : Term
pairOO = ap2 Pair O O

KT_pairOO : Fun2
KT_pairOO = Lift (KT pairOO)

innerPair_TreeEqv2v4_pairOO : Fun2
innerPair_TreeEqv2v4_pairOO = Fan TreeEq_v2v4_gen KT_pairOO Pair

y2Generator : Fun2
y2Generator = Fan TreeEq_v1v3_gen innerPair_TreeEqv2v4_pairOO D_IfLf

------------------------------------------------------------------------
-- Inner dispatch: combines y1Generator and y2Generator with Pair.

inner_dispatch : Fun2
inner_dispatch = Fan y1Generator y2Generator Pair

------------------------------------------------------------------------
-- D_TreeEq_NN_fun: outer wrapper with tagCode_ruleTrans head.
--
-- ap2 D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4) =BRA
--   Pair tagCode_ruleTrans (Pair y1T y2T)
-- where y1T = parEncAxTreeEqNN(cor v1)(cor v2)(cor v3)(cor v4)
--       y2T = ap2 D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O))

KT_tagRuleTrans : Fun2
KT_tagRuleTrans = Lift (KT tagCode_ruleTrans)

D_TreeEq_NN_fun : Fun2
D_TreeEq_NN_fun = Fan KT_tagRuleTrans inner_dispatch Pair

------------------------------------------------------------------------
-- Closure: D_TreeEq_NN_fun has no free variables.  All components
-- (Fan/Lift/Post/Comp/Fst/Snd/Pair/IfLf/TreeEq, cor, KT of closed
-- Terms, D_IfLf) are themselves substF-invariant by definitional
-- reduction.  refl suffices.

D_TreeEq_NN_closed : (x : Nat) (r : Term) ->
  Eq (substF2 x r D_TreeEq_NN_fun) D_TreeEq_NN_fun
D_TreeEq_NN_closed x r = refl
