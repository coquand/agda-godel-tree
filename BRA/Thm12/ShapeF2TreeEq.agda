{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.ShapeF2TreeEq -- universal Fst-shape for the Th12TreeEqClose
-- D_TreeEq (= Construction.D_TreeEq instantiated with the specific
-- D_TreeEq_NN_fun from BRA.Th12TreeEqNNFun).
--
-- 4 leaf shape proofs (LL, LN, NL, NN) lifted via nested ruleIndBT.
--
-- LL/LN/NL leaf cases mirror IfLf's: D_TreeEq dispatches to
-- parEncAxTreeEq*, all Pair-shaped with Pair tagCode_axTreeEq* (...).
--
-- NN case dispatches to D_TreeEq_NN_fun = Fan KT_tagRuleTrans inner Pair.
-- ap2 D_TreeEq_NN_fun (Pair p q)(Pair a b) reduces (via axFan) to
-- Pair (ap2 KT_tagRuleTrans ...) (ap2 inner ...) — Pair-shaped.

module BRA.Thm12.ShapeF2TreeEq where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

open import BRA.Cor using (cor)
open import BRA.Th12TreeEqNNFun
  using ( D_TreeEq_NN_fun
        ; D_TreeEq_NN_closed
        ; KT_tagRuleTrans )

import BRA.Thm12.Parts.TreeEq
module CB = BRA.Thm12.Parts.TreeEq.ConstructionBase
              D_TreeEq_NN_fun D_TreeEq_NN_closed
open CB
  using ( D_TreeEq
        ; D_TreeEq_reduce_OO
        ; D_TreeEq_reduce_LN
        ; D_TreeEq_reduce_NL
        ; D_TreeEq_reduce_NN )

open import BRA.Thm12.Param.AxTreeEqLL using (parEncAxTreeEqLL)
open import BRA.Thm12.Param.AxTreeEqLN using (parEncAxTreeEqLN)
open import BRA.Thm12.Param.AxTreeEqNL using (parEncAxTreeEqNL)
open import BRA.Thm.ThmT using (tagCode_ruleTrans)
open import BRA.Thm.Tag using (tagRuleTrans)
open import BRA.Th12TreeEqNNFun using (inner_dispatch)

------------------------------------------------------------------------
-- Pair-eta.

private
  pair_eta : (a b : Term) ->
    Deriv (atomic (eqn (ap2 Pair a b)
                       (ap2 Pair (ap1 Fst (ap2 Pair a b))
                                 (ap1 Snd (ap2 Pair a b)))))
  pair_eta a b =
    let
      fstEq = axFst a b
      sndEq = axSnd a b
      step1 : Deriv (atomic (eqn (ap2 Pair a b)
                                 (ap2 Pair (ap1 Fst (ap2 Pair a b)) b)))
      step1 = congL Pair b (ruleSym fstEq)
      step2 : Deriv (atomic (eqn (ap2 Pair (ap1 Fst (ap2 Pair a b)) b)
                                 (ap2 Pair (ap1 Fst (ap2 Pair a b))
                                           (ap1 Snd (ap2 Pair a b)))))
      step2 = congR Pair (ap1 Fst (ap2 Pair a b)) (ruleSym sndEq)
    in ruleTrans step1 step2

------------------------------------------------------------------------
-- The shape formula at universal var 0 (= x) and var 1 (= v).

P_shape_TreeEq : Formula
P_shape_TreeEq =
  atomic (eqn (ap1 Fst (ap2 D_TreeEq (var zero) (var (suc zero))))
              (ap2 Pair
                (ap1 Fst (ap1 Fst (ap2 D_TreeEq (var zero) (var (suc zero)))))
                (ap1 Snd (ap1 Fst (ap2 D_TreeEq (var zero) (var (suc zero)))))))

------------------------------------------------------------------------
-- Leaf shape generator (specialized to D_TreeEq).

private
  leaf_shape :
    (X V : Term) (parEnc : Term) ->
    Deriv (atomic (eqn (ap2 D_TreeEq X V) parEnc)) ->
    (pTag pBody : Term) ->
    Deriv (atomic (eqn parEnc (ap2 Pair pTag pBody))) ->
    (tA tB : Term) ->
    Deriv (atomic (eqn pTag (ap2 Pair tA tB))) ->
    Deriv (atomic
      (eqn (ap1 Fst (ap2 D_TreeEq X V))
           (ap2 Pair
             (ap1 Fst (ap1 Fst (ap2 D_TreeEq X V)))
             (ap1 Snd (ap1 Fst (ap2 D_TreeEq X V))))))
  leaf_shape X V parEnc reduce pTag pBody parEncIsPair tA tB pTagIsPair =
    let
      s1 : Deriv (atomic (eqn (ap1 Fst (ap2 D_TreeEq X V))
                              (ap1 Fst parEnc)))
      s1 = cong1 Fst reduce
      s2a : Deriv (atomic (eqn (ap1 Fst parEnc)
                               (ap1 Fst (ap2 Pair pTag pBody))))
      s2a = cong1 Fst parEncIsPair
      s2b = axFst pTag pBody
      s2 = ruleTrans s2a s2b
      s12 = ruleTrans s1 s2

      etaTag = pair_eta tA tB
      bridge_fst = cong1 Fst (ruleSym pTagIsPair)
      bridge_snd = cong1 Snd (ruleSym pTagIsPair)
      etaTagBridged : Deriv (atomic (eqn pTag
                                          (ap2 Pair (ap1 Fst pTag) (ap1 Snd pTag))))
      etaTagBridged =
        ruleTrans pTagIsPair
          (ruleTrans etaTag
            (ruleTrans (congL Pair (ap1 Snd (ap2 Pair tA tB)) bridge_fst)
                       (congR Pair (ap1 Fst pTag) bridge_snd)))

      s123 = ruleTrans s12 etaTagBridged
      s12_sym = ruleSym s12
      rhs_fst = cong1 Fst s12_sym
      rhs_snd = cong1 Snd s12_sym
      rhs_pair =
        ruleTrans (congL Pair (ap1 Snd pTag) rhs_fst)
                  (congR Pair (ap1 Fst (ap1 Fst (ap2 D_TreeEq X V))) rhs_snd)
    in ruleTrans s123 rhs_pair

------------------------------------------------------------------------
-- Three concrete leaf shapes (LL/LN/NL): direct from the D_TreeEq_reduce_*
-- lemmas + leaf_shape.

shape_LL :
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_TreeEq O O))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_TreeEq O O)))
           (ap1 Snd (ap1 Fst (ap2 D_TreeEq O O))))))
shape_LL =
  leaf_shape O O (parEncAxTreeEqLL O) D_TreeEq_reduce_OO
             _ _ (axRefl _)
             _ _ (axRefl _)

shape_LN : (a b : Term) ->
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_TreeEq O (ap2 Pair a b)))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_TreeEq O (ap2 Pair a b))))
           (ap1 Snd (ap1 Fst (ap2 D_TreeEq O (ap2 Pair a b)))))))
shape_LN a b =
  leaf_shape O (ap2 Pair a b)
             (parEncAxTreeEqLN (ap1 cor a) (ap1 cor b))
             (D_TreeEq_reduce_LN a b)
             _ _ (axRefl _)
             _ _ (axRefl _)

shape_NL : (p q : Term) ->
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_TreeEq (ap2 Pair p q) O))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_TreeEq (ap2 Pair p q) O)))
           (ap1 Snd (ap1 Fst (ap2 D_TreeEq (ap2 Pair p q) O))))))
shape_NL p q =
  leaf_shape (ap2 Pair p q) O
             (parEncAxTreeEqNL (ap1 cor p) (ap1 cor q))
             (D_TreeEq_reduce_NL p q)
             _ _ (axRefl _)
             _ _ (axRefl _)

------------------------------------------------------------------------
-- NN leaf shape: dispatch through D_TreeEq_NN_fun's outer Fan.

private
  -- ap2 D_TreeEq_NN_fun X V = Pair (ap2 KT_tagRuleTrans X V) (ap2 inner X V).
  -- We only need the Pair form to apply pair_eta.
  D_TreeEq_NN_fun_pairForm : (X V : Term) ->
    Deriv (atomic (eqn (ap2 D_TreeEq_NN_fun X V)
                       (ap2 Pair (ap2 KT_tagRuleTrans X V)
                                 (ap2 inner_dispatch X V))))
  D_TreeEq_NN_fun_pairForm X V =
    axFan KT_tagRuleTrans inner_dispatch Pair X V

shape_NN : (p q a b : Term) ->
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_TreeEq (ap2 Pair p q) (ap2 Pair a b)))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_TreeEq (ap2 Pair p q) (ap2 Pair a b))))
           (ap1 Snd (ap1 Fst (ap2 D_TreeEq (ap2 Pair p q) (ap2 Pair a b)))))))
shape_NN p q a b =
  let
    X : Term
    X = ap2 Pair p q
    V : Term
    V = ap2 Pair a b

    -- D_TreeEq X V = D_TreeEq_NN_fun X V via D_TreeEq_reduce_NN.
    s_to_NN : Deriv (atomic (eqn (ap2 D_TreeEq X V) (ap2 D_TreeEq_NN_fun X V)))
    s_to_NN = D_TreeEq_reduce_NN p q a b

    -- D_TreeEq_NN_fun X V = Pair (KT_tagRuleTrans X V) (inner X V).
    s_NN_pair : Deriv (atomic (eqn (ap2 D_TreeEq_NN_fun X V)
                                    (ap2 Pair (ap2 KT_tagRuleTrans X V)
                                              (ap2 inner_dispatch X V))))
    s_NN_pair = D_TreeEq_NN_fun_pairForm X V

    -- KT_tagRuleTrans X V = tagCode_ruleTrans (= reify (natCode tagRuleTrans)).
    -- KT_tagRuleTrans = Lift (KT tagCode_ruleTrans), so ap2 _ X V = ap1 (KT tagCode_ruleTrans) X
    --   = tagCode_ruleTrans  via axKT (natCode tagRuleTrans) X.
    s_KT : Deriv (atomic (eqn (ap2 KT_tagRuleTrans X V)
                              tagCode_ruleTrans))
    s_KT = ruleTrans (axLift (KT tagCode_ruleTrans) X V)
                     (axKT (natCode tagRuleTrans) X)

    -- The full reduction: D_TreeEq X V = Pair tagCode_ruleTrans (inner X V).
    parEncForm : Term
    parEncForm = ap2 Pair tagCode_ruleTrans
                          (ap2 inner_dispatch X V)

    s_to_parEnc : Deriv (atomic (eqn (ap2 D_TreeEq X V) parEncForm))
    s_to_parEnc =
      ruleTrans s_to_NN
        (ruleTrans s_NN_pair
                   (congL Pair (ap2 inner_dispatch X V) s_KT))

  in leaf_shape X V parEncForm s_to_parEnc
                _ _ (axRefl _)
                _ _ (axRefl _)

------------------------------------------------------------------------
-- Nested ruleIndBT lift.

private
  v1OuterNat : Nat
  v1OuterNat = suc (suc zero)
  v2OuterNat : Nat
  v2OuterNat = suc (suc (suc zero))
  v1InnerNat : Nat
  v1InnerNat = suc (suc (suc (suc zero)))
  v2InnerNat : Nat
  v2InnerNat = suc (suc (suc (suc (suc zero))))
  vOuterNat : Nat
  vOuterNat = suc zero

  Q_baseO : Formula
  Q_baseO =
    atomic (eqn (ap1 Fst (ap2 D_TreeEq O (var zero)))
                (ap2 Pair
                  (ap1 Fst (ap1 Fst (ap2 D_TreeEq O (var zero))))
                  (ap1 Snd (ap1 Fst (ap2 D_TreeEq O (var zero))))))

  inner_base_O_proof : Deriv (substF zero O Q_baseO)
  inner_base_O_proof = shape_LL

  inner_step_O_concl :
    Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
  inner_step_O_concl = shape_LN (var v1InnerNat) (var v2InnerNat)

  inner_step_O_imp_inner :
    Deriv (substF zero (var v2InnerNat) Q_baseO imp
           substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
  inner_step_O_imp_inner =
    mp (axK (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
            (substF zero (var v2InnerNat) Q_baseO))
       inner_step_O_concl

  inner_step_O_imp :
    Deriv (substF zero (var v1InnerNat) Q_baseO imp
           (substF zero (var v2InnerNat) Q_baseO imp
            substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO))
  inner_step_O_imp =
    mp (axK (substF zero (var v2InnerNat) Q_baseO imp
             substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
            (substF zero (var v1InnerNat) Q_baseO))
       inner_step_O_imp_inner

  univ_x_O : Deriv Q_baseO
  univ_x_O = ruleIndBT Q_baseO v1InnerNat v2InnerNat
                       inner_base_O_proof inner_step_O_imp

  outer_base_proof : Deriv (substF zero O P_shape_TreeEq)
  outer_base_proof = ruleInst zero (var vOuterNat) univ_x_O

  pairOuter : Term
  pairOuter = ap2 Pair (var v1OuterNat) (var v2OuterNat)

  Q_stepP : Formula
  Q_stepP =
    atomic (eqn (ap1 Fst (ap2 D_TreeEq pairOuter (var zero)))
                (ap2 Pair
                  (ap1 Fst (ap1 Fst (ap2 D_TreeEq pairOuter (var zero))))
                  (ap1 Snd (ap1 Fst (ap2 D_TreeEq pairOuter (var zero))))))

  inner_base_P_proof : Deriv (substF zero O Q_stepP)
  inner_base_P_proof = shape_NL (var v1OuterNat) (var v2OuterNat)

  inner_step_P_concl :
    Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
  inner_step_P_concl =
    shape_NN (var v1OuterNat) (var v2OuterNat)
             (var v1InnerNat) (var v2InnerNat)

  inner_step_P_imp_inner :
    Deriv (substF zero (var v2InnerNat) Q_stepP imp
           substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
  inner_step_P_imp_inner =
    mp (axK (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
            (substF zero (var v2InnerNat) Q_stepP))
       inner_step_P_concl

  inner_step_P_imp :
    Deriv (substF zero (var v1InnerNat) Q_stepP imp
           (substF zero (var v2InnerNat) Q_stepP imp
            substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP))
  inner_step_P_imp =
    mp (axK (substF zero (var v2InnerNat) Q_stepP imp
             substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
            (substF zero (var v1InnerNat) Q_stepP))
       inner_step_P_imp_inner

  univ_x_P : Deriv Q_stepP
  univ_x_P = ruleIndBT Q_stepP v1InnerNat v2InnerNat
                       inner_base_P_proof inner_step_P_imp

  outer_step_concl : Deriv (substF zero pairOuter P_shape_TreeEq)
  outer_step_concl = ruleInst zero (var vOuterNat) univ_x_P

  outer_step_imp_inner :
    Deriv (substF zero (var v2OuterNat) P_shape_TreeEq imp
           substF zero pairOuter P_shape_TreeEq)
  outer_step_imp_inner =
    mp (axK (substF zero pairOuter P_shape_TreeEq)
            (substF zero (var v2OuterNat) P_shape_TreeEq))
       outer_step_concl

  outer_step_imp :
    Deriv (substF zero (var v1OuterNat) P_shape_TreeEq imp
           (substF zero (var v2OuterNat) P_shape_TreeEq imp
            substF zero pairOuter P_shape_TreeEq))
  outer_step_imp =
    mp (axK (substF zero (var v2OuterNat) P_shape_TreeEq imp
             substF zero pairOuter P_shape_TreeEq)
            (substF zero (var v1OuterNat) P_shape_TreeEq))
       outer_step_imp_inner

shape_D_F2_TreeEq_var01 : Deriv P_shape_TreeEq
shape_D_F2_TreeEq_var01 =
  ruleIndBT P_shape_TreeEq v1OuterNat v2OuterNat
            outer_base_proof outer_step_imp
