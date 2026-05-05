{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecPCloseS -- universal Theorem 12 for RecP(s), parametric in
-- (s, Df_F2_s, Df_F2_s_closed, Th12_F2_s).
--
-- Variable convention (mirrors Th12RecPUniv): p = var 1 (kept fresh),
-- x = var 0 (recursion variable for ruleIndBT).
--
-- Output: Th12_F2_RecP_s : Deriv P_Th12_RecP_s
--   where P_Th12_RecP_s = atomic (eqn (ap1 thmT (ap2 D2_RecP_s (var 1) (var 0)))
--                                     (codeFTeq2Asym (RecP s) (var 1) (var 0))).

module BRA.Th12RecPCloseS where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.ReifyClosed using (reifyClosed)
open import BRA.Thm14CodeFTeqAsym using (codeFTeq2Asym ; mkAp2T)
open import BRA.Thm.ThmT using (thmT ; thClosed)
open import BRA.Thm.Tag using (tagAxRecPLf)
open import BRA.Thm12.Param.AxRecPLf using (parEncAxRecPLf)

import BRA.Thm12.Parts.RecP
import BRA.Th12RecPCloseSBasePP

module Th12RecPCloseS_Case
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

  open BRA.Th12RecPCloseSBasePP.Th12RecPCloseSBasePP_Case
    s s_closed Df_F2_s Df_F2_s_closed Th12_F2_s
    public

  ----------------------------------------------------------------------
  -- D2_RecP_s : Fun2 via Parts/RecP.Construction with our chain.

  open BRA.Thm12.Parts.RecP.Construction
    s D_RecP_NN_fun_chain Th12_F2_RecP_NN_pt
    using (D2_RecP_s ; D_correct2_RecP_s_O ; D_correct2_RecP_s_Nd)

  ----------------------------------------------------------------------
  -- Closure of D2_RecP_s.
  --
  -- D2_RecP_s = Fan (Post Snd Pair) dispatchFun IfLf
  --   where dispatchFun = Fan lfPart D_RecP_NN_fun_chain Pair
  --         lfPart      = Fan (Lift (KT tagCode_axRecPLf)) lfPayload Pair
  --         lfPayload   = Fan (Lift (KT sT)) (Lift cor) Pair

  Lift_KT_sT_F2_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Lift (KT sT))) (Lift (KT sT))
  Lift_KT_sT_F2_closed n r = Lift_KT_reify_closed (codeF2 s) n r

  Lift_KT_tagAxRecPLf_F2_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Lift (KT (BRA.Thm.ThmT.tagCode_axRecPLf))))
       (Lift (KT (BRA.Thm.ThmT.tagCode_axRecPLf)))
  Lift_KT_tagAxRecPLf_F2_closed n r =
    Lift_KT_reify_closed (natCode tagAxRecPLf) n r

  -- lfPayload = Fan (Lift (KT sT)) (Lift cor) Pair.
  -- Lift cor is closed (cor is closed Fun1).
  lfPayload_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Fan (Lift (KT sT)) (Lift cor) Pair))
       (Fan (Lift (KT sT)) (Lift cor) Pair)
  lfPayload_closed n r =
    eqCong (\ k -> Fan k (Lift cor) Pair) (Lift_KT_sT_F2_closed n r)

  lfPart_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Fan (Lift (KT (BRA.Thm.ThmT.tagCode_axRecPLf)))
                          (Fan (Lift (KT sT)) (Lift cor) Pair) Pair))
       (Fan (Lift (KT (BRA.Thm.ThmT.tagCode_axRecPLf)))
            (Fan (Lift (KT sT)) (Lift cor) Pair) Pair)
  lfPart_closed n r =
    eqCong2 (\ k1 k2 -> Fan k1 k2 Pair)
      (Lift_KT_tagAxRecPLf_F2_closed n r) (lfPayload_closed n r)

  dispatchFun_closed : (n : Nat) (r : Term) ->
    Eq (substF2 n r (Fan (Fan (Lift (KT (BRA.Thm.ThmT.tagCode_axRecPLf)))
                               (Fan (Lift (KT sT)) (Lift cor) Pair) Pair)
                          D_RecP_NN_fun_chain Pair))
       (Fan (Fan (Lift (KT (BRA.Thm.ThmT.tagCode_axRecPLf)))
                  (Fan (Lift (KT sT)) (Lift cor) Pair) Pair)
            D_RecP_NN_fun_chain Pair)
  dispatchFun_closed n r =
    eqCong2 (\ a b -> Fan a b Pair)
      (lfPart_closed n r) (D_RecP_NN_fun_chain_closed n r)

  D2_RecP_s_closed : (n : Nat) (r : Term) -> Eq (substF2 n r D2_RecP_s) D2_RecP_s
  D2_RecP_s_closed n r =
    eqCong (\ d -> Fan (Post Snd Pair) d IfLf) (dispatchFun_closed n r)

  ----------------------------------------------------------------------
  -- recPF closure (already in NNFun via NNReduce/BasePP open public).

  ----------------------------------------------------------------------
  -- cor closure.

  cor_closed_eq : (n : Nat) (r : Term) -> Eq (substF1 n r cor) cor
  cor_closed_eq n r = refl

  ----------------------------------------------------------------------
  -- cf2 closure (cf2 = reify (codeF2 (RecP s))).

  cf2_closed : (n : Nat) (r : Term) -> Eq (subst n r cf2) cf2
  cf2_closed n r = reifyClosed (codeF2 recPF) n r

  ----------------------------------------------------------------------
  -- The universal Theorem 12 statement (var 1 = p, var 0 = x).

  P_Th12_RecP_s : Formula
  P_Th12_RecP_s = atomic (eqn (ap1 thmT (ap2 D2_RecP_s (var (suc zero)) (var zero)))
                              (codeFTeq2Asym recPF (var (suc zero)) (var zero)))

  ----------------------------------------------------------------------
  -- Lf-case at x = O (with p kept at var 1).
  --
  -- D_correct2_RecP_s_O p : thmT(D2_RecP_s p O) = codeFTeq2_RecP_s s p O
  --                       = codeFTeq2Asym (RecP s) p O    (definitionally)
  --
  -- substF zero O P_Th12_RecP_s reduces to:
  --   atomic (eqn (ap1 (substF1 zero O thmT)
  --                    (ap2 (substF2 zero O D2_RecP_s) (var 1) O))
  --               (subst zero O (codeFTeq2Asym recPF (var 1) (var 0))))
  -- We bridge via three eqSubst's: thClosed, D2_RecP_s_closed, codeFTeq2Asym_subst_eq.

  codeFTeq2Asym_subst_eq_O :
    Eq (subst zero O (codeFTeq2Asym recPF (var (suc zero)) (var zero)))
       (codeFTeq2Asym recPF (var (suc zero)) O)
  codeFTeq2Asym_subst_eq_O =
    eqCong3 (\ cf2' cor' recPF' -> ap2 Pair
      (ap2 Pair (reify tagAp2)
        (ap2 Pair cf2' (ap2 Pair (ap1 cor' (var (suc zero))) (ap1 cor' O))))
      (ap1 cor' (ap2 recPF' (var (suc zero)) O)))
      (cf2_closed zero O)
      (cor_closed_eq zero O)
      (recPF_closed zero O)

  baseLf_substF : Deriv (substF zero O P_Th12_RecP_s)
  baseLf_substF =
    eqSubst (\ thT' -> Deriv (atomic (eqn
        (ap1 thT' (ap2 (substF2 zero O D2_RecP_s) (var (suc zero)) O))
        (subst zero O (codeFTeq2Asym recPF (var (suc zero)) (var zero))))))
      (eqSym (thClosed zero O))
      (eqSubst (\ Df' -> Deriv (atomic (eqn
          (ap1 thmT (ap2 Df' (var (suc zero)) O))
          (subst zero O (codeFTeq2Asym recPF (var (suc zero)) (var zero))))))
        (eqSym (D2_RecP_s_closed zero O))
        (eqSubst (\ rhs -> Deriv (atomic (eqn
            (ap1 thmT (ap2 D2_RecP_s (var (suc zero)) O)) rhs)))
          (eqSym codeFTeq2Asym_subst_eq_O)
          (D_correct2_RecP_s_O (var (suc zero)))))

  ----------------------------------------------------------------------
  -- Step (Pair) case: align Th12_F2_RecP_NN_pt to substF form, absorb IHs.

  codeFTeq2Asym_subst_eq_Pair : (v1 v2 : Term) ->
    Eq (subst zero (ap2 Pair v1 v2)
              (codeFTeq2Asym recPF (var (suc zero)) (var zero)))
       (codeFTeq2Asym recPF (var (suc zero)) (ap2 Pair v1 v2))
  codeFTeq2Asym_subst_eq_Pair v1 v2 =
    eqCong3 (\ cf2' cor' recPF' -> ap2 Pair
      (ap2 Pair (reify tagAp2)
        (ap2 Pair cf2'
          (ap2 Pair (ap1 cor' (var (suc zero)))
                    (ap1 cor' (ap2 Pair v1 v2)))))
      (ap1 cor' (ap2 recPF' (var (suc zero)) (ap2 Pair v1 v2))))
      (cf2_closed zero (ap2 Pair v1 v2))
      (cor_closed_eq zero (ap2 Pair v1 v2))
      (recPF_closed zero (ap2 Pair v1 v2))

  basePair_substF : (v1T v2T : Term) ->
    Deriv (substF zero (ap2 Pair v1T v2T) P_Th12_RecP_s)
  basePair_substF v1T v2T =
    let pT = var (suc zero)
        pairV = ap2 Pair v1T v2T
        nn_pt : Deriv (atomic (eqn (ap1 thmT (ap2 D2_RecP_s pT pairV))
                                    (codeFTeq2Asym recPF pT pairV)))
        nn_pt = D_correct2_RecP_s_Nd pT v1T v2T
    in eqSubst (\ thT' -> Deriv (atomic (eqn
          (ap1 thT' (ap2 (substF2 zero pairV D2_RecP_s) pT pairV))
          (subst zero pairV (codeFTeq2Asym recPF pT (var zero))))))
        (eqSym (thClosed zero pairV))
        (eqSubst (\ Df' -> Deriv (atomic (eqn
            (ap1 thmT (ap2 Df' pT pairV))
            (subst zero pairV (codeFTeq2Asym recPF pT (var zero))))))
          (eqSym (D2_RecP_s_closed zero pairV))
          (eqSubst (\ rhs -> Deriv (atomic (eqn
              (ap1 thmT (ap2 D2_RecP_s pT pairV)) rhs)))
            (eqSym (codeFTeq2Asym_subst_eq_Pair v1T v2T))
            nn_pt))

  ----------------------------------------------------------------------
  -- Pack basePair as the imp form expected by ruleIndBT, absorbing
  -- the two IHs (cross-IH at v1 and v2) via axK.

  v1Nat : Nat
  v1Nat = suc (suc zero)

  v2Nat : Nat
  v2Nat = suc (suc (suc zero))

  v1T : Term
  v1T = var v1Nat

  v2T : Term
  v2T = var v2Nat

  basePair_imp : Deriv ((substF zero v1T P_Th12_RecP_s) imp
                        ((substF zero v2T P_Th12_RecP_s) imp
                         (substF zero (ap2 Pair v1T v2T) P_Th12_RecP_s)))
  basePair_imp =
    let
      Concl : Formula
      Concl = substF zero (ap2 Pair v1T v2T) P_Th12_RecP_s

      A1 : Formula
      A1 = substF zero v1T P_Th12_RecP_s

      A2 : Formula
      A2 = substF zero v2T P_Th12_RecP_s

      proof : Deriv Concl
      proof = basePair_substF v1T v2T

      step1 : Deriv (A2 imp Concl)
      step1 = mp (axK Concl A2) proof

      step2 : Deriv (A1 imp (A2 imp Concl))
      step2 = mp (axK (A2 imp Concl) A1) step1
    in step2

  ----------------------------------------------------------------------
  -- Final: Th12_F2_RecP_s via ruleIndBT.

  Th12_F2_RecP_s : Deriv P_Th12_RecP_s
  Th12_F2_RecP_s = ruleIndBT P_Th12_RecP_s v1Nat v2Nat baseLf_substF basePair_imp
