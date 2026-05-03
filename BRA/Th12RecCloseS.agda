{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecCloseS -- universal Theorem 12 for Rec(z, s), parametric in
-- (z, s, Df_F2_s, Th12_F2_s).
--
-- Mirrors BRA.Th12TreeEqClose: combines the lf-case (from Parts/Rec.Construction)
-- with the Pair-case (Th12_F1_Rec_NN_pt) via ruleIndBT (1D, on the input x).
--
-- Output: Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs
--   where P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 D_Rec_zs (var zero)))
--                                     (codeFTeq1Asym (Rec z s) (var zero))).
--
-- Strategy:
--   1. Build D_Rec_zs : Fun1 via Parts/Rec.Construction with our chain
--      D_Rec_NN_fun_chain.
--   2. Prove D_Rec_zs_closed by structural composition of sub-closures.
--   3. Lf-case: align D_correct_Rec_zs_O (from Parts/Rec.Construction) to
--      substF form via eqSubst on thClosed + D_Rec_zs_closed + recF_closed.
--   4. Pair-case: align Th12_F1_Rec_NN_pt to substF form, then absorb the
--      two IHs (from ruleIndBT step) via axK twice.
--   5. Apply ruleIndBT.
--
-- No postulates, no holes.

module BRA.Th12RecCloseS where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.ReifyClosed using (reifyClosed)
open import BRA.Thm14CodeFTeqAsym using (codeFTeq1Asym ; mkAp1T)
open import BRA.Thm.ThmT using (thmT ; thClosed)
open import BRA.Thm.Tag using (tagAxRecLf)
open import BRA.Thm12.Param.AxRecLf using (parEncAxRecLf)

import BRA.Thm12.Parts.Rec
import BRA.Th12RecCloseSBasePP

module Th12RecCloseS_Case
  (z : Term)
  (s : Fun2)
  (z_corLemma : Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))
  (z_closed : (n : Nat) (r : Term) -> Eq (subst n r z) z)
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

  open BRA.Th12RecCloseSBasePP.Th12RecCloseSBasePP_Case
    z s z_closed s_closed Df_F2_s Df_F2_s_closed Th12_F2_s
    public

  ----------------------------------------------------------------------
  -- D_Rec_zs : Fun1 via Parts/Rec.Construction with our chain.
  -- The Construction module needs:
  --   * z, s
  --   * z_corLemma
  --   * D_Rec_NN_fun (= D_Rec_NN_fun_chain from NNFun)
  --   * D_correct_Rec_NN_pt (= Th12_F1_Rec_NN_pt from BasePP).

  open BRA.Thm12.Parts.Rec.Construction
    z s z_corLemma D_Rec_NN_fun_chain Th12_F1_Rec_NN_pt
    using (D_Rec_zs ; D_correct_Rec_zs_O ; D_correct_Rec_zs_Nd)

  ----------------------------------------------------------------------
  -- Closure of D_Rec_zs.
  --
  -- D_Rec_zs = Comp2 IfLf I dispatchFun
  --   where dispatchFun = Comp2 Pair (KT (parEncAxRecLf zT sT)) D_Rec_NN_fun_chain.
  --
  -- All components closed: IfLf and I are closed (refl); KT (reify T) is
  -- closed via KT_reify_substF1_closed; D_Rec_NN_fun_chain is closed
  -- via D_Rec_NN_fun_chain_closed.

  parEncAxRecLf_tree : Tree
  parEncAxRecLf_tree = nd (natCode tagAxRecLf) (nd (code z) (codeF2 s))

  KT_parEncAxRecLf_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r (KT (parEncAxRecLf zT sT))) (KT (parEncAxRecLf zT sT))
  KT_parEncAxRecLf_closed n r = KT_reify_substF1_closed parEncAxRecLf_tree n r

  -- dispatchFun closure: Comp2 Pair (KT _) D_Rec_NN_fun_chain.
  dispatchFun_closed : (n : Nat) (r : Term) ->
    Eq (substF1 n r (Comp2 Pair (KT (parEncAxRecLf zT sT)) D_Rec_NN_fun_chain))
       (Comp2 Pair (KT (parEncAxRecLf zT sT)) D_Rec_NN_fun_chain)
  dispatchFun_closed n r =
    eqCong2 (\ a b -> Comp2 Pair a b)
      (KT_parEncAxRecLf_closed n r)
      (D_Rec_NN_fun_chain_closed n r)

  D_Rec_zs_closed : (n : Nat) (r : Term) -> Eq (substF1 n r D_Rec_zs) D_Rec_zs
  D_Rec_zs_closed n r =
    eqCong (\ d -> Comp2 IfLf I d) (dispatchFun_closed n r)

  ----------------------------------------------------------------------
  -- (recF_closed re-exported from NNFun via NNReduce/BasePP open public.)

  ----------------------------------------------------------------------
  -- cor closure: cor is a closed Fun1 (Rec O stepCor with O closed,
  -- stepCor closed).

  cor_closed_eq : (n : Nat) (r : Term) -> Eq (substF1 n r cor) cor
  cor_closed_eq n r = refl

  ----------------------------------------------------------------------
  -- cf closure (cf = reify (codeF1 (Rec z s))).
  --
  -- Note: codeF1 (Rec z s) = nd <tag> (nd (code z) (codeF2 s)).  We
  -- can't directly use reifyClosed because Agda has to compute reify
  -- of the codeF1 tree, but z and s are opaque.  However, by definition
  -- reify (nd a b) = ap2 Pair (reify a) (reify b), and since cf is
  -- definitionally a Pair-of-Pairs structure, we can prove closure by
  -- structural unfolding.

  cf_closed : (n : Nat) (r : Term) -> Eq (subst n r cf) cf
  cf_closed n r = reifyClosed (codeF1 recF) n r

  ----------------------------------------------------------------------
  -- The universal Theorem 12 statement for D_Rec_zs.

  P_Th12_Rec_zs : Formula
  P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 D_Rec_zs (var zero)))
                              (codeFTeq1Asym recF (var zero)))

  ----------------------------------------------------------------------
  -- Lf-case: align D_correct_Rec_zs_O to substF zero O P_Th12_Rec_zs.
  --
  -- D_correct_Rec_zs_O : thmT(D_Rec_zs O) = codeFTeq1_Rec_zs z s O
  --                    = codeFTeq1Asym (Rec z s) O    (definitionally)
  --
  -- substF zero O P_Th12_Rec_zs reduces (Agda definitional) to:
  --   atomic (eqn (ap1 (substF1 zero O thmT) (ap1 (substF1 zero O D_Rec_zs) O))
  --               (subst zero O (codeFTeq1Asym recF (var zero))))
  -- We bridge via three eqSubst's: thClosed, D_Rec_zs_closed,
  -- and codeFTeq1Asym_subst_eq.

  codeFTeq1Asym_subst_eq_O :
    Eq (subst zero O (codeFTeq1Asym recF (var zero)))
       (codeFTeq1Asym recF O)
  codeFTeq1Asym_subst_eq_O =
    eqCong3 (\ cf' cor' recF' -> ap2 Pair
      (ap2 Pair (reify tagAp1)(ap2 Pair cf' (ap1 cor' O)))
      (ap1 cor' (ap1 recF' O)))
      (cf_closed zero O)
      (cor_closed_eq zero O)
      (recF_closed zero O)

  baseLf_substF : Deriv (substF zero O P_Th12_Rec_zs)
  baseLf_substF =
    eqSubst (\ thT' -> Deriv (atomic (eqn
        (ap1 thT' (ap1 (substF1 zero O D_Rec_zs) O))
        (subst zero O (codeFTeq1Asym recF (var zero))))))
      (eqSym (thClosed zero O))
      (eqSubst (\ Df' -> Deriv (atomic (eqn
          (ap1 thmT (ap1 Df' O))
          (subst zero O (codeFTeq1Asym recF (var zero))))))
        (eqSym (D_Rec_zs_closed zero O))
        (eqSubst (\ rhs -> Deriv (atomic (eqn
            (ap1 thmT (ap1 D_Rec_zs O)) rhs)))
          (eqSym codeFTeq1Asym_subst_eq_O)
          D_correct_Rec_zs_O))

  ----------------------------------------------------------------------
  -- Step (Pair) case: align Th12_F1_Rec_NN_pt to substF form, absorb IHs.

  -- Eq lemma at variable input.
  codeFTeq1Asym_subst_eq_Pair : (v1 v2 : Term) ->
    Eq (subst zero (ap2 Pair v1 v2) (codeFTeq1Asym recF (var zero)))
       (codeFTeq1Asym recF (ap2 Pair v1 v2))
  codeFTeq1Asym_subst_eq_Pair v1 v2 =
    eqCong3 (\ cf' cor' recF' -> ap2 Pair
      (ap2 Pair (reify tagAp1)(ap2 Pair cf' (ap1 cor' (ap2 Pair v1 v2))))
      (ap1 cor' (ap1 recF' (ap2 Pair v1 v2))))
      (cf_closed zero (ap2 Pair v1 v2))
      (cor_closed_eq zero (ap2 Pair v1 v2))
      (recF_closed zero (ap2 Pair v1 v2))

  -- The Pair-case proof at concrete (v1T, v2T) aligned to substF form.
  basePair_substF : (v1T v2T : Term) ->
    Deriv (substF zero (ap2 Pair v1T v2T) P_Th12_Rec_zs)
  basePair_substF v1T v2T =
    let pairT = ap2 Pair v1T v2T
        nn_pt : Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs pairT))
                                    (codeFTeq1Asym recF pairT)))
        nn_pt = D_correct_Rec_zs_Nd v1T v2T
    in eqSubst (\ thT' -> Deriv (atomic (eqn
          (ap1 thT' (ap1 (substF1 zero pairT D_Rec_zs) pairT))
          (subst zero pairT (codeFTeq1Asym recF (var zero))))))
        (eqSym (thClosed zero pairT))
        (eqSubst (\ Df' -> Deriv (atomic (eqn
            (ap1 thmT (ap1 Df' pairT))
            (subst zero pairT (codeFTeq1Asym recF (var zero))))))
          (eqSym (D_Rec_zs_closed zero pairT))
          (eqSubst (\ rhs -> Deriv (atomic (eqn
              (ap1 thmT (ap1 D_Rec_zs pairT)) rhs)))
            (eqSym (codeFTeq1Asym_subst_eq_Pair v1T v2T))
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

  basePair_imp : Deriv ((substF zero v1T P_Th12_Rec_zs) imp
                        ((substF zero v2T P_Th12_Rec_zs) imp
                         (substF zero (ap2 Pair v1T v2T) P_Th12_Rec_zs)))
  basePair_imp =
    let
      Concl : Formula
      Concl = substF zero (ap2 Pair v1T v2T) P_Th12_Rec_zs

      A1 : Formula
      A1 = substF zero v1T P_Th12_Rec_zs

      A2 : Formula
      A2 = substF zero v2T P_Th12_Rec_zs

      proof : Deriv Concl
      proof = basePair_substF v1T v2T

      step1 : Deriv (A2 imp Concl)
      step1 = mp (axK Concl A2) proof

      step2 : Deriv (A1 imp (A2 imp Concl))
      step2 = mp (axK (A2 imp Concl) A1) step1
    in step2

  ----------------------------------------------------------------------
  -- Final: Th12_F1_Rec_zs via ruleIndBT.

  Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs
  Th12_F1_Rec_zs = ruleIndBT P_Th12_Rec_zs v1Nat v2Nat baseLf_substF basePair_imp
