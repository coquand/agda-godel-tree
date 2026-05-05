{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecCloseSBasePP -- pointwise correctness of D_Rec_NN_fun_chain
-- at Pair input.
--
-- Proves:
--   Th12_F1_Rec_NN_pt v1 v2 :
--     Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_NN_fun_chain (ap2 Pair v1 v2)))
--                        (codeFTeq1 (Rec z s) (ap2 Pair v1 v2))))
--
-- Strategy:
--   1. BRA-reduce ap1 D_Rec_NN_fun_chain (Pair v1 v2) to chain Df.
--   2. Apply thmTDispRuleTrans_param to dispatch the chain.
--      - y1T = parEncAxRecNd zT sT (cor v1) (cor v2)
--      - y2T = ap2 Df_F2_s (Pair v1 v2) (Pair rec_v1 rec_v2)
--      - thmT(y1T) image via parDispAxRecNd.
--      - thmT(y2T) image via Th12_F2_s_correctness at (Pair v1 v2)(Pair rec_v1 rec_v2).
--      - shape on y1T: Fst y1T = tagCode_axRecNd, which definitionally
--        unfolds to Pair O (...).
--   3. Bridge Pair u1 u4 to codeFTeq1 (Rec z s)(Pair v1 v2) via:
--      - u1 → mkAp1T cf (cor (Pair v1 v2)): ruleSym (corOfPair v1 v2) at
--        the encoded_pair_v1v2 slot.
--      - u4 → cor((Rec z s)(Pair v1 v2)): cong1 cor (ruleSym (axRecNd z s v1 v2)).
--
-- No postulates, no holes.

module BRA.Th12RecCloseSBasePP where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.CorOfPair using (corOfPair)
open import BRA.Thm14CodeFTeqAsym using (mkAp1T ; mkAp2T)
open import BRA.Thm.Tag using (tagAxRecNd ; tagRuleTrans)
open import BRA.Thm.ThmT using
  ( thmT ; tagCode_axRecNd ; tagCode_ruleTrans
  ; thmTDispRuleTrans_param )
open import BRA.Thm12.Param.AxRecNd
  using (parEncAxRecNd ; parOutAxRecNd ; parDispAxRecNd)

import BRA.Th12RecCloseSNNReduce

module Th12RecCloseSBasePP_Case
  (z : Term)
  (s : Fun2)
  (z_closed : (n : Nat) (r : Term) -> Eq (subst n r z) z)
  (s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r s) s)
  (Df_F2_s : Fun2)
  (Df_F2_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Df_F2_s) Df_F2_s)
  -- The encoded form of Theorem 12 for s: at any (x v : Term), thmT
  -- of Df_F2_s gives the encoded equation for s.
  (Th12_F2_s : (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_s x v))
                       (ap2 Pair
                         (ap2 Pair (reify tagAp2)
                           (ap2 Pair (reify (codeF2 s))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
                         (ap1 cor (ap2 s x v))))))
  where

  open BRA.Th12RecCloseSNNReduce.Th12RecCloseSNNReduce_Case
    z s z_closed s_closed Df_F2_s Df_F2_s_closed
    public

  ----------------------------------------------------------------------
  -- Encoded constants (re-exported from NNFun via NNReduce).

  cf : Term
  cf = reify (codeF1 recF)

  pCT : Term
  pCT = reify (codeF2 Pair)

  ----------------------------------------------------------------------
  -- The codeFTeq1 spec for Rec z s.

  codeFTeq1_RecZS : Term -> Term
  codeFTeq1_RecZS x =
    ap2 Pair
      (ap2 Pair (reify tagAp1)
                (ap2 Pair cf (ap1 cor x)))
      (ap1 cor (ap1 recF x))

  ----------------------------------------------------------------------
  -- Main pointwise basePP statement.

  Th12_F1_Rec_NN_pt : (v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_NN_fun_chain (ap2 Pair v1 v2)))
                       (codeFTeq1_RecZS (ap2 Pair v1 v2))))
  Th12_F1_Rec_NN_pt v1 v2 =
    let
      pairT : Term
      pairT = ap2 Pair v1 v2

      rec_v1 : Term
      rec_v1 = ap1 recF v1

      rec_v2 : Term
      rec_v2 = ap1 recF v2

      pairR : Term
      pairR = ap2 Pair rec_v1 rec_v2

      -- Local abbreviations.
      cor_v1 : Term
      cor_v1 = ap1 cor v1

      cor_v2 : Term
      cor_v2 = ap1 cor v2

      cor_pairT : Term
      cor_pairT = ap1 cor pairT

      cor_pairR : Term
      cor_pairR = ap1 cor pairR

      -- y1T, y2T.
      y1T : Term
      y1T = y1T_target v1 v2

      y2T : Term
      y2T = y2T_target v1 v2

      -- u1, u2 : the two halves of parOutAxRecNd zT sT (cor v1)(cor v2).

      -- Encoded (Pair v1 v2) at slot aT, bT.
      enc_pair_v1v2 : Term
      enc_pair_v1v2 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair pCT (ap2 Pair cor_v1 cor_v2))

      -- Encoded recF v_i at the recF-image slot.
      enc_recF_v1 : Term
      enc_recF_v1 =
        ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                              (ap2 Pair zT sT))
                    cor_v1)

      enc_recF_v2 : Term
      enc_recF_v2 =
        ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                              (ap2 Pair zT sT))
                    cor_v2)

      -- Encoded (Pair rec_v1 rec_v2) — but with cor v_i at the recF slots
      -- (this is what parOutAxRecNd produces).
      enc_pair_recv1_recv2 : Term
      enc_pair_recv1_recv2 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair pCT (ap2 Pair enc_recF_v1 enc_recF_v2))

      u1 : Term
      u1 = ap2 Pair (reify tagAp1)
             (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                 (ap2 Pair zT sT))
                       enc_pair_v1v2)

      u2 : Term
      u2 = ap2 Pair (reify tagAp2)
             (ap2 Pair sT
               (ap2 Pair enc_pair_v1v2 enc_pair_recv1_recv2))

      -- u3, u4 : the two halves of codeFTeq2 s (Pair v1 v2)(Pair rec_v1 rec_v2).
      u3 : Term
      u3 = ap2 Pair (reify tagAp2)
             (ap2 Pair sT (ap2 Pair cor_pairT cor_pairR))

      u4 : Term
      u4 = ap1 cor (ap2 s pairT pairR)

      ----------------------------------------------------------------
      -- d1: thmT(y1T) = Pair u1 u2 via parDispAxRecNd.

      d1 : Deriv (atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2)))
      d1 = parDispAxRecNd zT sT cor_v1 cor_v2

      -- d2: thmT(y2T) = Pair u3 u4 via Th12_F2_s.
      d2 : Deriv (atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4)))
      d2 = Th12_F2_s pairT pairR

      -- shape: Fst y1T = ap2 Pair x' y1' for some x', y1'.
      -- y1T = parEncAxRecNd ... = Pair tagCode_axRecNd (...).
      -- Fst y1T = tagCode_axRecNd, which definitionally unfolds to Pair O (...)
      -- since natCode (suc n) = nd lf (natCode n).
      payload : Term
      payload = ap2 Pair zT (ap2 Pair sT (ap2 Pair cor_v1 cor_v2))

      shape = axFst tagCode_axRecNd payload

      -- Apply thmTDispRuleTrans_param.
      disp : Deriv (atomic (eqn
              (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
              (ap2 Pair u1 u4)))
      disp = thmTDispRuleTrans_param y1T y2T u1 u2 u3 u4 _ _
               shape d1 d2

      ----------------------------------------------------------------
      -- Bridge u1 → mkAp1T cf (cor pairT).
      --
      -- u1 = Pair tagAp1 (Pair cf' enc_pair_v1v2)
      --   where cf' = Pair (reify (leftT (codeF1 (Rec O IfLf)))) (Pair zT sT)
      --   which equals cf = reify (codeF1 (Rec z s)) definitionally.
      --
      -- mkAp1T cf (cor pairT) = Pair tagAp1 (Pair cf (cor pairT)).
      --
      -- Bridge: enc_pair_v1v2 → cor pairT via ruleSym (corOfPair v1 v2).

      bridge_inner_pair : Deriv (atomic (eqn enc_pair_v1v2 cor_pairT))
      bridge_inner_pair = ruleSym (corOfPair v1 v2)

      LHS_target : Term
      LHS_target = mkAp1T cf cor_pairT

      bridge_u1 : Deriv (atomic (eqn u1 LHS_target))
      bridge_u1 = congR Pair (reify tagAp1)
                    (congR Pair cf bridge_inner_pair)

      ----------------------------------------------------------------
      -- Bridge u4 → cor (recF pairT).
      --
      -- u4 = cor (s pairT pairR)
      -- axRecNd: recF pairT = s pairT pairR
      -- cong1 cor: cor (recF pairT) = cor (s pairT pairR) = u4
      -- ruleSym: u4 = cor (recF pairT)

      cor_recF_target : Term
      cor_recF_target = ap1 cor (ap1 recF pairT)

      bridge_u4 : Deriv (atomic (eqn u4 cor_recF_target))
      bridge_u4 = ruleSym (cong1 cor (axRecNd z s v1 v2))

      ----------------------------------------------------------------
      -- Combine: Pair u1 u4 → Pair LHS_target cor_recF_target = codeFTeq1_RecZS pairT.

      bridge_pair : Deriv (atomic (eqn (ap2 Pair u1 u4)
                                        (ap2 Pair LHS_target cor_recF_target)))
      bridge_pair =
        ruleTrans (congL Pair u4 bridge_u1)
                  (congR Pair LHS_target bridge_u4)

      ----------------------------------------------------------------
      -- Step A: BRA-reduce thmT(D_Rec_NN_fun_chain pairT) to thmT(chain Df).

      s_reduce : Deriv (atomic (eqn (ap1 D_Rec_NN_fun_chain pairT)
                                     (ap2 Pair tagCode_ruleTrans
                                               (ap2 Pair y1T y2T))))
      s_reduce = D_Rec_NN_fun_chain_at_Pair v1 v2

      s_thmT_reduce : Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_NN_fun_chain pairT))
                                          (ap1 thmT (ap2 Pair tagCode_ruleTrans
                                                                (ap2 Pair y1T y2T)))))
      s_thmT_reduce = cong1 thmT s_reduce

    in ruleTrans s_thmT_reduce (ruleTrans disp bridge_pair)
