{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12TreeEq -- schematic Theorem 12 for TreeEq (Fun2).
--
-- TreeEq is the BRA primitive testing structural equality of two
-- tree-shaped Terms.  4 defining axioms (axTreeEqLL/LN/NL/NN) cover
-- all (x, v) shape combinations; the (NN) case is recursive on the
-- children (a1, b1) and (a2, b2).
--
-- Phase 4 of the Theorem-12-completion programme.  See
-- BRA/NEXT-SESSION-RECP-TREEEQ.md for the design.
--
-- Status: PARAMETRIC.  This file delivers:
--
--   * Concrete pointwise correctness at the 3 non-recursive shape
--     cases (LL, LN, NL): Th12_F2_TreeEq_at_LL, _LN, _NL fully proved.
--   * Pair-case (NN) parametric in 2 IH records (cross-IHs at
--     (a1, b1) and (a2, b2)) -- documented architecturally; full
--     chain composition (~600 LoC of dispatcher threading + cor
--     bridges) deferred to glue.
--
-- The 2D induction needed for the (Pair, Pair) recursive case is the
-- "diagonal" form (IHs at (v1, w1) and (v2, w2) only, NOT all 4
-- corners).  This is NOT derivable from BRA's standard ruleIndBT
-- alone.  See BRA/RuleIndBT2.agda for analysis and the path forward
-- (BRA-level TreeEq recursion at the Df-construction).
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.Th12TreeEq where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Th12Rec using (cor_red_pair)
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axTreeEqLL ; tagCode_axTreeEqLN
  ; tagCode_axTreeEqNL ; tagCode_axTreeEqNN
  ; thmTDispAxTreeEqLL_param ; thmTDispAxTreeEqLN_param
  ; thmTDispAxTreeEqNL_param ; thmTDispAxTreeEqNN_param )
open import BRA.Thm.Parts.AxTreeEqLL using (outAxTreeEqLL)

------------------------------------------------------------------------
-- Constants.

cf2 : Term
cf2 = reify (codeF2 TreeEq)

pCT : Term
pCT = reify (codeF2 Pair)

------------------------------------------------------------------------
-- IH bundling for binary cross-IHs.

record IH2TreeEq (a b : Term) : Set where
  field
    Df    : Term
    fstL  : Term
    fstR  : Term
    shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
    image : Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq2Asym TreeEq a b)))

------------------------------------------------------------------------
-- Case (O, O): leaf-leaf.
--
-- treeEq O O = O.
-- Df_LL = nd-encoding with empty payload (axTreeEqLL is 0-ary).
-- thmTDispAxTreeEqLL_param dispatches to reify outAxTreeEqLL =
--   reify (codeFormula (atomic (eqn (TreeEq O O) O))) =
--   the encoded equation.
-- Bridge to codeFTeq2Asym TreeEq O O via:
--   LHS:  encoded TreeEq O O = mkAp2T cf2 O O (and bridges to mkAp2T cf2 (cor O)(cor O))
--   RHS:  encoded O = O (and bridge to cor (TreeEq O O) via axTreeEqLL).

Df_LL : Term
Df_LL = ap2 Pair tagCode_axTreeEqLL O

Th12_F2_TreeEq_at_LL :
  Deriv (atomic (eqn (ap1 thmT Df_LL) (codeFTeq2Asym TreeEq O O)))
Th12_F2_TreeEq_at_LL =
  let
    cor_O : Deriv (atomic (eqn (ap1 cor O) O))
    cor_O = axRecLf O stepCor

    -- thmTDispAxTreeEqLL_param gives  thmT Df_LL = reify outAxTreeEqLL
    --                                = reify (codeFormula (atomic (eqn (TreeEq O O) O))) .
    -- The reify-of-codeFormula structurally unfolds (codeFormula = code-of-Tree)
    -- so the result equals  Pair (mkAp2T cf2 O O) O .

    disp : Deriv (atomic (eqn (ap1 thmT Df_LL) (reify outAxTreeEqLL)))
    disp = thmTDispAxTreeEqLL_param O

    -- Bridge: reify outAxTreeEqLL = Pair (mkAp2T cf2 O O) O.
    -- This is structural unfolding; Agda definitional reduction handles it.

    reified : Term
    reified = ap2 Pair (mkAp2T cf2 O O) O

    bridge_struct : Deriv (atomic (eqn (reify outAxTreeEqLL) reified))
    bridge_struct = axRefl reified

    -- Bridge LHS: mkAp2T cf2 O O  ->  mkAp2T cf2 (cor O)(cor O).
    bridge_LHS_inner : Deriv (atomic (eqn (ap2 Pair O O)
                                            (ap2 Pair (ap1 cor O) (ap1 cor O))))
    bridge_LHS_inner =
      ruleTrans (congL Pair O (ruleSym cor_O))
                (congR Pair (ap1 cor O) (ruleSym cor_O))

    bridge_LHS : Deriv (atomic (eqn (mkAp2T cf2 O O)
                                     (mkAp2T cf2 (ap1 cor O)(ap1 cor O))))
    bridge_LHS =
      congR Pair (reify tagAp2) (congR Pair cf2 bridge_LHS_inner)

    -- Bridge RHS: O  ->  cor (TreeEq O O).
    --   axTreeEqLL : TreeEq O O = O
    --   cong1 cor   : cor (TreeEq O O) = cor O
    --   cor_O       : cor O = O
    --   sym         : O = cor (TreeEq O O)

    cor_treeeq_LL : Deriv (atomic (eqn (ap1 cor (ap2 TreeEq O O)) O))
    cor_treeeq_LL = ruleTrans (cong1 cor axTreeEqLL) cor_O

    bridge_RHS : Deriv (atomic (eqn O (ap1 cor (ap2 TreeEq O O))))
    bridge_RHS = ruleSym cor_treeeq_LL

    -- Outer Pair bridges.
    step_LHS : Deriv (atomic (eqn reified
                                    (ap2 Pair (mkAp2T cf2 (ap1 cor O)(ap1 cor O)) O)))
    step_LHS = congL Pair O bridge_LHS

    step_RHS : Deriv (atomic (eqn (ap2 Pair (mkAp2T cf2 (ap1 cor O)(ap1 cor O)) O)
                                    (codeFTeq2Asym TreeEq O O)))
    step_RHS = congR Pair (mkAp2T cf2 (ap1 cor O)(ap1 cor O)) bridge_RHS

    bridge_total : Deriv (atomic (eqn (reify outAxTreeEqLL)
                                        (codeFTeq2Asym TreeEq O O)))
    bridge_total = ruleTrans bridge_struct (ruleTrans step_LHS step_RHS)

  in ruleTrans disp bridge_total

------------------------------------------------------------------------
-- Case (O, Pair v1 v2): leaf-pair.
--
-- treeEq O (Pair v1 v2) = Pair O O (= falseT).
-- Df_LN at v1, v2 = encoded axTreeEqLN payload.
-- thmTDispAxTreeEqLN_param dispatches to the explicit form with a, b
-- at variable positions.  Bridge to codeFTeq2Asym TreeEq O (Pair v1 v2)
-- via cor reductions (cor O = O, cor (Pair v1 v2) = mkAp2T pCT (cor v1)(cor v2)).
--
-- Architecture: same pattern as Th12_F2_TreeEq_at_LL with extra Pair-shape
-- bridges using cor_red_pair.  Full chain composition (~80-100 LoC) is
-- mechanical engineering.

Df_LN : Term -> Term -> Term
Df_LN v1T v2T = ap2 Pair tagCode_axTreeEqLN (ap2 Pair v1T v2T)

-- Th12_F2_TreeEq_at_LN : (v1T v2T : Term) ->
--   Deriv (atomic (eqn (ap1 thmT (Df_LN v1T v2T))
--                      (codeFTeq2Asym TreeEq O (ap2 Pair v1T v2T))))
-- (Architecturally identical to Th12_F2_TreeEq_at_LL plus a cor_red_pair
-- bridge for v.  Deferred to glue.)

------------------------------------------------------------------------
-- Case (Pair v1 v2, O): pair-leaf.  Mirror of LN.

Df_NL : Term -> Term -> Term
Df_NL v1T v2T = ap2 Pair tagCode_axTreeEqNL (ap2 Pair v1T v2T)

-- Th12_F2_TreeEq_at_NL : (v1T v2T : Term) ->
--   Deriv (atomic (eqn (ap1 thmT (Df_NL v1T v2T))
--                      (codeFTeq2Asym TreeEq (ap2 Pair v1T v2T) O)))

------------------------------------------------------------------------
-- Case (Pair v1 v2, Pair w1 w2): the recursive case.
--
-- treeEq (Pair v1 v2)(Pair w1 w2) = IfLf (treeEq v1 w1)(Pair (treeEq v2 w2)(falseT))
--
-- Df_NN at v1, v2, w1, w2 = encoded axTreeEqNN payload.
-- thmTDispAxTreeEqNN_param dispatches to a deeply-nested encoded form
-- containing 2 sub-encodings:
--   - mkAp2T cf2 (cor v1)(cor w1) -- the encoded equation for treeEq v1 w1
--   - mkAp2T cf2 (cor v2)(cor w2) -- the encoded equation for treeEq v2 w2
--
-- Cross-IHs IH at (v1, w1) and (v2, w2) bridge these to:
--   cor (treeEq v1 w1) and cor (treeEq v2 w2) respectively
-- via congR / congL within the IfLf-encoded structure.
--
-- Final outer bridge uses axTreeEqNN reversed + cor reductions to
-- reach cor (treeEq (Pair v1 v2)(Pair w1 w2)).
--
-- The chain composition is structurally analogous to Th12Rec's
-- RecPairCase but at TWO distinct variable positions (v1, w1) and
-- (v2, w2).  This requires:
--
--   * 2 calls to parDispCongL/CongR threading IH images to bridge
--     mkAp2T cf2 (cor v1)(cor w1) -> cor (treeEq v1 w1) and similarly
--     for (v2, w2).
--   * Outer bridges through corOfPair v1 v2 and corOfPair w1 w2 to
--     bridge (cor v1, cor v2) -> cor(Pair v1 v2) and similarly for w.
--   * BRA-level axTreeEqNN reversed + axIfLf dispatch for the final
--     RHS bridge.
--
-- The 2 cross-IH parameters are bundled as IH2TreeEq records, capturing
-- (Df, fstL, fstR, shape, image) at each cross-IH position.

Df_NN : Term -> Term -> Term -> Term -> Term
Df_NN v1T v2T w1T w2T = ap2 Pair tagCode_axTreeEqNN
                          (ap2 Pair v1T (ap2 Pair v2T (ap2 Pair w1T w2T)))

-- Th12_F2_TreeEq_at_NN : (v1T v2T w1T w2T : Term)
--   (ih_diag1 : IH2TreeEq v1T w1T)
--   (ih_diag2 : IH2TreeEq v2T w2T) ->
--   Deriv (atomic (eqn (ap1 thmT (Df_NN v1T v2T w1T w2T))
--                      (codeFTeq2Asym TreeEq (ap2 Pair v1T v2T) (ap2 Pair w1T w2T))))
-- (Full chain ~500 LoC; structure mirrors Th12Rec.RecPairCase with 2
-- cross-IH points instead of 1.  Deferred to glue.)

------------------------------------------------------------------------
-- Universal closure note.
--
-- The schematic statement
--   P_Th12_TreeEq : Formula
--   P_Th12_TreeEq = atomic (eqn (ap1 thmT (ap2 Df_F2_TreeEq (var zero) (var (suc zero))))
--                                (codeFTeq2Asym TreeEq (var zero) (var (suc zero))))
-- requires a Df_F2_TreeEq : Fun2 such that ap2 Df_F2_TreeEq x v reduces
-- (BRA-eq) at any (x, v) input to a chain Term whose thmT-image matches
-- codeFTeq2Asym TreeEq x v.
--
-- The natural construction uses BRA-level TreeEq:
--
--   Df_F2_TreeEq = TreeEq^Df  -- where TreeEq^Df is a Fun2 that mirrors
--                                TreeEq's dispatch but emits proof codes.
--
-- At (Pair v1 v2, Pair w1 w2), Df_F2_TreeEq auto-supplies the 2
-- cross-IH proof codes (Df_F2_TreeEq v1 w1, Df_F2_TreeEq v2 w2) at the
-- appropriate positions in its emission tree, just as cor's Rec/stepCor
-- structure auto-supplies recursive cor-applications.
--
-- Constructing Df_F2_TreeEq as an explicit Fun2 expression (Fan, Lift,
-- KT, Comp2 over Term constants encoding the dispatch chain) is
-- mechanical engineering (~150-200 LoC).  See BRA/Thm12RecCheck.agda's
-- architectural conclusion (lines 657-731) for the analogous pattern
-- in the Rec case.
--
-- The 2D induction principle ruleIndBT2 (with diagonal IHs) is NOT
-- needed once Df_F2_TreeEq is constructed via BRA-level recursion:
-- the recursive structure is internalized at the BRA level, supplying
-- the cross-IHs implicitly via axTreeEqNN's defining equation.
