{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12TreeEqBasePP -- pointwise basePP_imp body for Th12 TreeEq.
--
-- Proves at variable inputs (v1, v2, v3, v4 : Term):
--
--   Th12_F2_TreeEq_NN_pt v1 v2 v3 v4 :
--     Deriv (atomic (eqn
--       (ap1 thmT (ap2 D_TreeEq_NN_fun (ap2 Pair v1 v2)(ap2 Pair v3 v4)))
--       (codeFTeq2_TreeEq (ap2 Pair v1 v2)(ap2 Pair v3 v4))))
--
-- Strategy:
--   1. BRA-reduce ap2 D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4) to chain Df
--      via D_TreeEq_NN_fun_at_NN.
--   2. Apply thmTDispRuleTrans_param to dispatch the chain.
--      - y1T = parEncAxTreeEqNN (cor v1)(cor v2)(cor v3)(cor v4)
--      - y2T = ap2 D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4) pairOO)
--      - thmT(y1T) image via parDispAxTreeEqNN.
--      - thmT(y2T) image via Th12_F2_IfLf with two ruleInst.
--      - shape on y1T: Fst y1T = tagCode_axTreeEqNN, which definitionally
--        unfolds to Pair O (...).
--   3. Bridge Pair u1 u4 to codeFTeq2_TreeEq (Pair v1 v2)(Pair v3 v4) via:
--      - corPairUnfold v1 v2 + corPairUnfold v3 v4 (LHS slot bridges).
--      - cong1 cor (axTreeEqNN v1 v2 v3 v4) (RHS slot bridge).
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.Th12TreeEqBasePP where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxTreeEqNN ; tagRuleTrans)
open import BRA.Thm.ThmT using
  ( thmT ; tagCode_axTreeEqNN ; tagCode_ruleTrans )
open import BRA.Thm12.Param.AxTreeEqNN
  using (parEncAxTreeEqNN ; parOutAxTreeEqNN ; parDispAxTreeEqNN)
open import BRA.Thm12.Parts.IfLf using (D_IfLf ; codeFTeq2_IfLf ; D_correct2_IfLf)
open import BRA.Thm12.Parts.TreeEq using (codeFTeq2_TreeEq)

open import BRA.Th12TreeEqNNFun
open import BRA.Th12TreeEqNNReduce

------------------------------------------------------------------------
-- corPairUnfold v1 v2 : cor (Pair v1 v2)
--                       = Pair (reify tagAp2)(Pair (reify (codeF2 Pair))
--                                                  (Pair (cor v1)(cor v2)))
--
-- Standard lemma; mirrors BRA.Thm12.Parts.TreeEq.corPairUnfold (private).

corPairUnfold : (a b : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap2 Pair a b))
                      (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair (ap1 cor a) (ap1 cor b))))))
corPairUnfold a b =
  let recs = ap2 Pair (ap1 cor a) (ap1 cor b)
      orig = ap2 Pair a b
      origW = ap2 Pair O orig
  in ruleTrans (axRecNd stepCor a b) (stepCorRed origW recs)

------------------------------------------------------------------------
-- Closure args for D_correct2_IfLf at (TreeEq v1 v3, Pair (TreeEq v2 v4) pairOO).
--
-- For the basePP_imp use case, v1, v2, v3, v4 are var v1Nat..v4Nat
-- (vars 2..5).  None of these are var 0 or var 1, so all closure
-- conditions reduce to refl.
--
-- Generic statement: if v1, v2, v3, v4 don't free-occur var 0 or var 1,
-- then the four substitution closures hold.  Caller supplies the
-- equational evidence.

D_correct2_IfLf_at_TreeEq :
  (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_IfLf (ap2 TreeEq v1 v3)
                                            (ap2 Pair (ap2 TreeEq v2 v4) pairOO)))
                     (codeFTeq2_IfLf (ap2 TreeEq v1 v3)
                                     (ap2 Pair (ap2 TreeEq v2 v4) pairOO))))
D_correct2_IfLf_at_TreeEq v1 v2 v3 v4 =
  D_correct2_IfLf (ap2 TreeEq v1 v3)
                  (ap2 Pair (ap2 TreeEq v2 v4) pairOO)

------------------------------------------------------------------------
-- Main pointwise basePP statement.
--
-- Proves: thmT(D_TreeEq_NN_fun (Pair v1 v2)(Pair v3 v4)) =
--         codeFTeq2_TreeEq (Pair v1 v2)(Pair v3 v4)
--
-- Parametric on the 4 substitution-closure proofs (refl when v_i are
-- free vars not = var 0 or var 1).

Th12_F2_TreeEq_NN_pt :
  (v1 v2 v3 v4 : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq_NN_fun
                                     (ap2 Pair v1 v2)(ap2 Pair v3 v4)))
                     (codeFTeq2_TreeEq (ap2 Pair v1 v2)(ap2 Pair v3 v4))))
Th12_F2_TreeEq_NN_pt v1 v2 v3 v4 =
  let
    pairV12 : Term
    pairV12 = ap2 Pair v1 v2
    pairV34 : Term
    pairV34 = ap2 Pair v3 v4

    -- Local abbreviations for the corPair-unfold targets.
    cor_v1 : Term
    cor_v1 = ap1 cor v1
    cor_v2 : Term
    cor_v2 = ap1 cor v2
    cor_v3 : Term
    cor_v3 = ap1 cor v3
    cor_v4 : Term
    cor_v4 = ap1 cor v4

    -- y1T = parEncAxTreeEqNN(cor v1)(cor v2)(cor v3)(cor v4).
    y1T : Term
    y1T = y1T_target v1 v2 v3 v4

    -- y2T = ap2 D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4) pairOO).
    y2T : Term
    y2T = y2T_target v1 v2 v3 v4

    -- u1, u2 : the two halves of parOutAxTreeEqNN(cor v1, cor v2, cor v3, cor v4).

    -- u1 = encoded LHS = mkAp2T cf2 (mkAp2T pCT (cor v1)(cor v2))
    --                                (mkAp2T pCT (cor v3)(cor v4)).
    Pair_cor_v1_v2_enc : Term
    Pair_cor_v1_v2_enc =
      ap2 Pair (reify tagAp2)
        (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair cor_v1 cor_v2))
    Pair_cor_v3_v4_enc : Term
    Pair_cor_v3_v4_enc =
      ap2 Pair (reify tagAp2)
        (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair cor_v3 cor_v4))

    u1 : Term
    u1 = ap2 Pair (reify tagAp2)
           (ap2 Pair (reify (codeF2 TreeEq))
                     (ap2 Pair Pair_cor_v1_v2_enc Pair_cor_v3_v4_enc))

    -- u2 = encoded RHS via parOutAxTreeEqNN's second half.
    u2 : Term
    u2 = ap2 Pair (reify tagAp2)
           (ap2 Pair (reify (codeF2 IfLf))
             (ap2 Pair
               (ap2 Pair (reify tagAp2)
                 (ap2 Pair (reify (codeF2 TreeEq))
                           (ap2 Pair cor_v1 cor_v3)))
               (ap2 Pair (reify tagAp2)
                 (ap2 Pair (reify (codeF2 Pair))
                   (ap2 Pair
                     (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 TreeEq))
                                 (ap2 Pair cor_v2 cor_v4)))
                     (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 Pair))
                         (ap2 Pair O O))))))))

    -- u3, u4 : the two halves of codeFTeq2_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4) pairOO).
    -- u3 = mkAp2T cifLf (cor (TreeEq v1 v3))(cor (Pair (TreeEq v2 v4) pairOO)).
    u3 : Term
    u3 = ap2 Pair (reify tagAp2)
           (ap2 Pair (reify (codeF2 IfLf))
             (ap2 Pair (ap1 cor (ap2 TreeEq v1 v3))
                       (ap1 cor (ap2 Pair (ap2 TreeEq v2 v4) pairOO))))

    -- u4 = cor (IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4) pairOO)).
    u4 : Term
    u4 = ap1 cor (ap2 IfLf (ap2 TreeEq v1 v3)
                            (ap2 Pair (ap2 TreeEq v2 v4) pairOO))

    -- d1: thmT(y1T) = Pair u1 u2.
    -- parDispAxTreeEqNN gives thmT(parEncAxTreeEqNN ...) = parOutAxTreeEqNN ...
    -- which is exactly Pair u1 u2 (by structure of parOutAxTreeEqNN).
    d1 : Deriv (atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2)))
    d1 = parDispAxTreeEqNN cor_v1 cor_v2 cor_v3 cor_v4

    -- d2: thmT(y2T) = Pair u3 u4.
    -- y2T = ap2 D_IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4) pairOO).
    -- D_correct2_IfLf gives thmT(D_IfLf X V) = codeFTeq2_IfLf X V
    --                     = Pair (mkAp2T cifLf (cor X)(cor V))(cor (IfLf X V))
    --                     = Pair u3 u4.
    d2 : Deriv (atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4)))
    d2 = D_correct2_IfLf_at_TreeEq v1 v2 v3 v4

    -- shape: Fst y1T = ap2 Pair x' y1' for some x', y1'.
    -- y1T = parEncAxTreeEqNN ... = Pair tagCode_axTreeEqNN (...).
    -- Fst y1T = tagCode_axTreeEqNN (via axFst), which definitionally
    -- unfolds to ap2 Pair O (...) since natCode (suc n) = nd lf (natCode n).
    payload : Term
    payload = ap2 Pair cor_v1 (ap2 Pair cor_v2 (ap2 Pair cor_v3 cor_v4))

    shape = axFst tagCode_axTreeEqNN payload

    -- Apply thmTDispRuleTrans_param.
    -- Output: thmT(Pair tagCode_ruleTrans (Pair y1T y2T)) = Pair u1 u4.
    disp : Deriv (atomic (eqn
            (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
            (ap2 Pair u1 u4)))
    disp = BRA.Thm.ThmT.thmTDispRuleTrans_param y1T y2T u1 u2 u3 u4 _ _
             shape d1 d2

    -- Bridge u1 → LHS_target.
    -- LHS_target = Pair (reify tagAp2)
    --                   (Pair (reify (codeF2 TreeEq))
    --                         (Pair (cor (Pair v1 v2))(cor (Pair v3 v4)))).
    -- u1 differs only in the two innermost Pair slots:
    --   X1 = Pair_cor_v1_v2_enc → cor (Pair v1 v2)   [via ruleSym (corPairUnfold v1 v2)]
    --   X2 = Pair_cor_v3_v4_enc → cor (Pair v3 v4)   [via ruleSym (corPairUnfold v3 v4)]

    bridge_X1 : Deriv (atomic (eqn Pair_cor_v1_v2_enc (ap1 cor pairV12)))
    bridge_X1 = ruleSym (corPairUnfold v1 v2)

    bridge_X2 : Deriv (atomic (eqn Pair_cor_v3_v4_enc (ap1 cor pairV34)))
    bridge_X2 = ruleSym (corPairUnfold v3 v4)

    -- Pair X1 X2 → Pair (cor pairV12)(cor pairV34).
    bridge_inner_pair : Deriv (atomic (eqn
                          (ap2 Pair Pair_cor_v1_v2_enc Pair_cor_v3_v4_enc)
                          (ap2 Pair (ap1 cor pairV12)(ap1 cor pairV34))))
    bridge_inner_pair =
      ruleTrans (congL Pair Pair_cor_v3_v4_enc bridge_X1)
                (congR Pair (ap1 cor pairV12) bridge_X2)

    -- Pair (codeF2 TreeEq) (Pair X1 X2) → Pair (codeF2 TreeEq)(Pair cor cor).
    bridge_t2_inner : Deriv (atomic (eqn
                        (ap2 Pair (reify (codeF2 TreeEq))
                                  (ap2 Pair Pair_cor_v1_v2_enc Pair_cor_v3_v4_enc))
                        (ap2 Pair (reify (codeF2 TreeEq))
                                  (ap2 Pair (ap1 cor pairV12)(ap1 cor pairV34)))))
    bridge_t2_inner = congR Pair (reify (codeF2 TreeEq)) bridge_inner_pair

    -- u1 → LHS_target.
    LHS_target : Term
    LHS_target = ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 TreeEq))
                             (ap2 Pair (ap1 cor pairV12)(ap1 cor pairV34)))

    bridge_u1 : Deriv (atomic (eqn u1 LHS_target))
    bridge_u1 = congR Pair (reify tagAp2) bridge_t2_inner

    -- Bridge u4 → cor (TreeEq (Pair v1 v2)(Pair v3 v4)).
    -- u4 = cor (IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4) pairOO)).
    -- axTreeEqNN v1 v2 v3 v4 : TreeEq (Pair v1 v2)(Pair v3 v4)
    --                          = IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O))
    -- pairOO = ap2 Pair O O definitionally, so the RHS matches u4's inner.
    -- cong1 cor of the axiom:
    --   cor (TreeEq (Pair v1 v2)(Pair v3 v4))
    --     = cor (IfLf (TreeEq v1 v3)(Pair (TreeEq v2 v4)(Pair O O)))
    --     = u4.
    -- Take ruleSym to flip direction.

    cor_TreeEq_target : Term
    cor_TreeEq_target = ap1 cor (ap2 TreeEq pairV12 pairV34)

    bridge_u4 : Deriv (atomic (eqn u4 cor_TreeEq_target))
    bridge_u4 = ruleSym (cong1 cor (axTreeEqNN v1 v2 v3 v4))

    -- Bridge Pair u1 u4 → Pair LHS_target cor_TreeEq_target = codeFTeq2_TreeEq pairV12 pairV34.
    bridge_pair : Deriv (atomic (eqn (ap2 Pair u1 u4)
                                      (ap2 Pair LHS_target cor_TreeEq_target)))
    bridge_pair =
      ruleTrans (congL Pair u4 bridge_u1)
                (congR Pair LHS_target bridge_u4)

    -- Step A: BRA-reduce thmT(D_TreeEq_NN_fun ...) to thmT(chain Df).
    s_reduce : Deriv (atomic (eqn (ap2 D_TreeEq_NN_fun pairV12 pairV34)
                                   (ap2 Pair tagCode_ruleTrans
                                             (ap2 Pair y1T y2T))))
    s_reduce = D_TreeEq_NN_fun_at_NN v1 v2 v3 v4

    s_thmT_reduce : Deriv (atomic (eqn (ap1 thmT (ap2 D_TreeEq_NN_fun pairV12 pairV34))
                                        (ap1 thmT (ap2 Pair tagCode_ruleTrans
                                                              (ap2 Pair y1T y2T)))))
    s_thmT_reduce = cong1 thmT s_reduce

  in ruleTrans s_thmT_reduce (ruleTrans disp bridge_pair)
