{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecPCloseSBasePP -- pointwise correctness of D_RecP_NN_fun_chain
-- at (p, Pair v1 v2).
--
-- Proves:
--   Th12_F2_RecP_NN_pt p v1 v2 :
--     Deriv (atomic (eqn (ap1 thmT (ap2 D_RecP_NN_fun_chain p (ap2 Pair v1 v2)))
--                        (codeFTeq2 (RecP s) p (ap2 Pair v1 v2))))

module BRA.Th12RecPCloseSBasePP where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.CorOfPair using (corOfPair)
open import BRA.Thm14CodeFTeqAsym using (mkAp2T)
open import BRA.Thm.Tag using (tagAxRecPNd ; tagRuleTrans)
open import BRA.Thm.ThmT using
  ( thmT ; tagCode_axRecPNd ; tagCode_ruleTrans
  ; thmTDispRuleTrans_param ; thmTDispAxRecPNd_param )

import BRA.Th12RecPCloseSNNReduce

module Th12RecPCloseSBasePP_Case
  (s : Fun2)
  (s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r s) s)
  (Df_F2_s : Fun2)
  (Df_F2_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Df_F2_s) Df_F2_s)
  (Th12_F2_s : (x v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Df_F2_s x v))
                       (ap2 Pair
                         (ap2 Pair (reify tagAp2)
                           (ap2 Pair (reify (codeF2 s))
                             (ap2 Pair (ap1 cor x) (ap1 cor v))))
                         (ap1 cor (ap2 s x v))))))
  where

  open BRA.Th12RecPCloseSNNReduce.Th12RecPCloseSNNReduce_Case
    s s_closed Df_F2_s Df_F2_s_closed
    public

  ----------------------------------------------------------------------
  -- Encoded constants.

  cf2 : Term
  cf2 = reify (codeF2 recPF)

  pCT : Term
  pCT = reify (codeF2 Pair)

  ----------------------------------------------------------------------
  -- The codeFTeq2 spec for RecP s.

  codeFTeq2_RecPS : Term -> Term -> Term
  codeFTeq2_RecPS p x =
    ap2 Pair
      (ap2 Pair (reify tagAp2)
                (ap2 Pair cf2
                          (ap2 Pair (ap1 cor p) (ap1 cor x))))
      (ap1 cor (ap2 recPF p x))

  ----------------------------------------------------------------------
  -- Main pointwise basePP statement.

  Th12_F2_RecP_NN_pt : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D_RecP_NN_fun_chain p (ap2 Pair v1 v2)))
                       (codeFTeq2_RecPS p (ap2 Pair v1 v2))))
  Th12_F2_RecP_NN_pt p v1 v2 =
    let
      pairV : Term
      pairV = ap2 Pair v1 v2

      rec_v1 : Term
      rec_v1 = ap2 recPF p v1

      rec_v2 : Term
      rec_v2 = ap2 recPF p v2

      pairR : Term
      pairR = ap2 Pair rec_v1 rec_v2

      cor_p : Term
      cor_p = ap1 cor p

      cor_v1 : Term
      cor_v1 = ap1 cor v1

      cor_v2 : Term
      cor_v2 = ap1 cor v2

      cor_pairV : Term
      cor_pairV = ap1 cor pairV

      cor_pairP_pairV : Term
      cor_pairP_pairV = ap1 cor (ap2 Pair p pairV)

      cor_pairR : Term
      cor_pairR = ap1 cor pairR

      y1T : Term
      y1T = y1T_target p v1 v2

      y2T : Term
      y2T = y2T_target p v1 v2

      ----------------------------------------------------------------
      -- u1, u2: parOutAxRecPNd(sT, cor p, cor v1, cor v2).

      -- Encoded (Pair v1 v2): Pair tagAp2 (Pair pCT (Pair (cor v1)(cor v2)))
      enc_pair_v1v2 : Term
      enc_pair_v1v2 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair pCT (ap2 Pair cor_v1 cor_v2))

      -- Encoded (Pair p (Pair v1 v2)): Pair tagAp2 (Pair pCT (Pair (cor p) enc_pair_v1v2))
      enc_pair_p_pair_v1v2 : Term
      enc_pair_p_pair_v1v2 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair pCT (ap2 Pair cor_p enc_pair_v1v2))

      -- Encoded recP head: Pair (reify (leftT (codeF2 (RecP IfLf)))) sT
      -- = reify (codeF2 (RecP s)) = cf2  (definitionally)
      recP_head : Term
      recP_head = ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT

      -- Encoded (RecP s p v_i): Pair tagAp2 (Pair recP_head (Pair (cor p)(cor v_i)))
      enc_recP_v1 : Term
      enc_recP_v1 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair recP_head (ap2 Pair cor_p cor_v1))

      enc_recP_v2 : Term
      enc_recP_v2 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair recP_head (ap2 Pair cor_p cor_v2))

      -- Encoded Pair (RecP s p v1)(RecP s p v2)
      enc_pair_rec_v1_rec_v2 : Term
      enc_pair_rec_v1_rec_v2 =
        ap2 Pair (reify tagAp2)
          (ap2 Pair pCT (ap2 Pair enc_recP_v1 enc_recP_v2))

      -- u1: encoded (RecP s) p (Pair v1 v2)
      u1 : Term
      u1 = ap2 Pair (reify tagAp2)
             (ap2 Pair recP_head
                       (ap2 Pair cor_p enc_pair_v1v2))

      -- u2: encoded RHS of axRecPNd
      u2 : Term
      u2 = ap2 Pair (reify tagAp2)
             (ap2 Pair sT
               (ap2 Pair enc_pair_p_pair_v1v2 enc_pair_rec_v1_rec_v2))

      -- u3, u4: codeFTeq2 s (Pair p (Pair v1 v2)) (Pair rec_v1 rec_v2)
      u3 : Term
      u3 = ap2 Pair (reify tagAp2)
             (ap2 Pair sT
               (ap2 Pair cor_pairP_pairV cor_pairR))

      u4 : Term
      u4 = ap1 cor (ap2 s (ap2 Pair p pairV) pairR)

      ----------------------------------------------------------------
      -- d1: thmT(y1T) = Pair u1 u2 via thmTDispAxRecPNd_param.

      d1 : Deriv (atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2)))
      d1 = thmTDispAxRecPNd_param sT cor_p cor_v1 cor_v2

      -- d2: thmT(y2T) = Pair u3 u4 via Th12_F2_s.
      d2 : Deriv (atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4)))
      d2 = Th12_F2_s (ap2 Pair p pairV) pairR

      -- shape: Fst y1T = Pair x' y'.
      payload : Term
      payload = ap2 Pair sT (ap2 Pair cor_p (ap2 Pair cor_v1 cor_v2))

      shape = axFst tagCode_axRecPNd payload

      -- Apply thmTDispRuleTrans_param.
      disp : Deriv (atomic (eqn
              (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
              (ap2 Pair u1 u4)))
      disp = thmTDispRuleTrans_param y1T y2T u1 u2 u3 u4 _ _
               shape d1 d2

      ----------------------------------------------------------------
      -- Bridge u1 → mkAp2T cf2 (cor p)(cor pairV).
      --
      -- u1 = Pair tagAp2 (Pair recP_head (Pair (cor p) enc_pair_v1v2))
      -- where recP_head = ap2 Pair (reify (leftT ...)) sT = cf2 (definitionally)
      --
      -- mkAp2T cf2 (cor p)(cor pairV) = Pair tagAp2 (Pair cf2 (Pair (cor p)(cor pairV))).
      --
      -- Bridge: enc_pair_v1v2 → cor pairV via ruleSym (corOfPair v1 v2).

      bridge_inner_pair : Deriv (atomic (eqn enc_pair_v1v2 cor_pairV))
      bridge_inner_pair = ruleSym (corOfPair v1 v2)

      LHS_target : Term
      LHS_target = mkAp2T cf2 cor_p cor_pairV

      bridge_u1 : Deriv (atomic (eqn u1 LHS_target))
      bridge_u1 =
        congR Pair (reify tagAp2)
          (congR Pair recP_head
            (congR Pair cor_p bridge_inner_pair))

      ----------------------------------------------------------------
      -- Bridge u4 → cor (recPF p pairV).
      --
      -- u4 = cor (s (Pair p pairV) (Pair rec_v1 rec_v2))
      -- axRecPNd: recPF p (Pair v1 v2) = s (Pair p (Pair v1 v2))(Pair rec_v1 rec_v2)
      -- cong1 cor: cor (recPF p pairV) = cor (s ...)
      -- ruleSym: u4 = cor (recPF p pairV)

      cor_recPF_target : Term
      cor_recPF_target = ap1 cor (ap2 recPF p pairV)

      bridge_u4 : Deriv (atomic (eqn u4 cor_recPF_target))
      bridge_u4 = ruleSym (cong1 cor (axRecPNd s p v1 v2))

      ----------------------------------------------------------------
      -- Combine.

      bridge_pair : Deriv (atomic (eqn (ap2 Pair u1 u4)
                                        (ap2 Pair LHS_target cor_recPF_target)))
      bridge_pair =
        ruleTrans (congL Pair u4 bridge_u1)
                  (congR Pair LHS_target bridge_u4)

      ----------------------------------------------------------------
      -- Step A: BRA-reduce thmT(D_RecP_NN_fun_chain p pairV) to thmT(chain Df).

      s_reduce : Deriv (atomic (eqn (ap2 D_RecP_NN_fun_chain p pairV)
                                     (ap2 Pair tagCode_ruleTrans
                                               (ap2 Pair y1T y2T))))
      s_reduce = D_RecP_NN_fun_chain_at_Pair p v1 v2

      s_thmT_reduce : Deriv (atomic (eqn (ap1 thmT (ap2 D_RecP_NN_fun_chain p pairV))
                                          (ap1 thmT (ap2 Pair tagCode_ruleTrans
                                                                (ap2 Pair y1T y2T)))))
      s_thmT_reduce = cong1 thmT s_reduce

    in ruleTrans s_thmT_reduce (ruleTrans disp bridge_pair)
