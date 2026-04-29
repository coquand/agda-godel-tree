{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecUniv -- universal closure infrastructure for Theorem 12 of Rec z s.
--
-- Builds on top of BRA.Th12Rec (which has the Pair-case Sigma proof).
-- Step-by-step plan:
--   Step A — Df_F1_Rec_zs : Fun1 (this file).
--   Step B — BRA-equality reductions at O and Pair v1 v2 (next).
--   Step C — Shape proof at any input (for IH1Rec.shape at var v_i).
--   Step D — Lf-case Deriv at substF zero O P_Th12_Rec_zs.
--   Step E — IH1Rec packaging at fresh vars (from a supplied IH-Deriv).
--   Step F — Pair-case Agda function: (ihD_v1 ihD_v2 : Deriv ...) -> Deriv ....
--   Step G — SKI lift to ruleIndBT step using axK + axS + axEqTrans + axEqCong*.
--   Step H — Final Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs via ruleIndBT.
--
-- Step A (this file): defines  Df_F1_Rec_zs  as a closed Fun1 expression
-- of the form  Comp2 Pair (KT tagCode_ruleTrans) inner_Rec  where
-- inner_Rec = Rec lf_inner step_inner.
--
-- Steps B-H follow in subsequent commits.

module BRA.Th12RecUniv where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_ruleTrans ; tagCode_axRecNd ; tagCode_axRefl
  ; tagCode_congL ; tagCode_congR )

------------------------------------------------------------------------
-- Helper Fun2 combinators for runtime emission.
--
-- step_inner takes (orig, recs) at runtime (axRecNd dispatch), where:
--   orig = Pair v1 v2  (the original input).
--   recs = Pair (inner_Rec v1) (inner_Rec v2)  (the recursive sub-results).

-- EmitPair ha hb : Fun2 such that ap2 (EmitPair ha hb) orig recs
--   = Pair (ap2 ha orig recs) (ap2 hb orig recs).
EmitPair : Fun2 -> Fun2 -> Fun2
EmitPair ha hb = Fan ha hb Pair

-- KT2 k : Fun2 emitting constant k regardless of (orig, recs).
KT2 : Term -> Fun2
KT2 k = Lift (KT k)

-- FromOrig f : Fun2 emitting (ap1 f orig).
FromOrig : Fun1 -> Fun2
FromOrig f = Lift f

-- Recs : Fun2 emitting recs.
Recs : Fun2
Recs = Post Snd Pair

-- RecsFst : Fun2 emitting (Fst recs).
RecsFst : Fun2
RecsFst = Post Fst Recs

-- RecsSnd : Fun2 emitting (Snd recs).
RecsSnd : Fun2
RecsSnd = Post Snd Recs

------------------------------------------------------------------------
-- Main parametric module.

module Th12RecUnivCase
  (z : Term)
  (s : Fun2)
  where

  zT : Term
  zT = reify (code z)

  sT : Term
  sT = reify (codeF2 s)

  recF : Fun1
  recF = Rec z s

  cf : Term
  cf = reify (codeF1 recF)

  pCT : Term
  pCT = reify (codeF2 Pair)

  ----------------------------------------------------------------------
  -- The lf-case payload (closed Term):
  --   lf_inner = Pair Df_lf_orig (Pair tagCode_axRefl (cor (recF O)))
  -- where Df_lf_orig = Pair tagCode_axRecLf (Pair zT sT) is the encoded
  -- axRecLf payload.
  --
  -- This wraps the leaf-case via parDispRuleTrans + axRefl-as-no-op so
  -- the OUTER Pair tagCode_ruleTrans wrapper makes thmT-image align
  -- with codeFTeq1Asym recF O.
  --
  -- thmT-image computation (via parDispRuleTrans):
  --   y1 = Df_lf_orig:    image Pair (mkAp1T cf (cor O)) (cor (recF O))   [= codeFTeq1Asym recF O]
  --   y2 = Pair tagCode_axRefl (cor (recF O)):   image Pair (cor (recF O)) (cor (recF O))   [via axRefl]
  --   composed: Pair (mkAp1T cf (cor O)) (cor (recF O)) = codeFTeq1Asym recF O.

  Df_lf_orig : Term
  Df_lf_orig = ap2 Pair (reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) (ap2 Pair zT sT)
  -- Note: tagAxRecLf = 11 (= suc^11 zero).  Reify of natCode 11 is the closed-Tree
  -- encoding.  Equivalent to  ap2 Pair tagCode_axRecLf (ap2 Pair zT sT)  but
  -- written explicitly to avoid the import.  We use tagCode_axRecLf below
  -- where it's available.

  -- Alternative (cleaner): import tagCode_axRecLf from ThmT.
  -- Df_lf_orig = ap2 Pair tagCode_axRecLf (ap2 Pair zT sT).

  encAxReflRecFO : Term
  encAxReflRecFO = ap2 Pair tagCode_axRefl (ap1 cor (ap1 recF O))

  lf_inner : Term
  lf_inner = ap2 Pair Df_lf_orig encAxReflRecFO

  ----------------------------------------------------------------------
  -- step_inner : Fun2 such that, at runtime ap2 step_inner (Pair v1 v2)
  -- (Pair (inner_Rec v1)(inner_Rec v2)), it BRA-reduces to:
  --
  --   Pair Df_chain1 Df_E_v2_lifted
  --
  -- (i.e., the "inner content" of Df_chain12 from RecPairCase, sans
  -- the outer Pair tagCode_ruleTrans wrapper provided by Comp2 Pair).
  --
  -- step_inner is a deeply-nested Fan-of-Fan using helper combinators.

  -- emit_cv1 : ap2 emit_cv1 orig recs = ap1 cor (ap1 Fst orig) = cor v1.
  emit_cv1 : Fun2
  emit_cv1 = FromOrig (Comp cor Fst)

  emit_cv2 : Fun2
  emit_cv2 = FromOrig (Comp cor Snd)

  -- emit_X : Fun2 emitting X = mkAp2T pCT cv1 cv2 = Pair tagAp2 (Pair pCT (Pair cv1 cv2)).
  emit_X : Fun2
  emit_X = EmitPair (KT2 (reify tagAp2))
             (EmitPair (KT2 pCT)
                (EmitPair emit_cv1 emit_cv2))

  -- emit_mkAp1Tcf t : Fun2 emitting mkAp1T cf t = Pair tagAp1 (Pair cf t).
  -- where t is itself emitted by emit_t.
  emit_mkAp1Tcf : Fun2 -> Fun2
  emit_mkAp1Tcf emit_t =
    EmitPair (KT2 (reify tagAp1))
      (EmitPair (KT2 cf) emit_t)

  -- emit_ih_v1_Df : Fun2 emitting ih_v1.Df = Df_F1_Rec_zs v1
  --              = Pair tagCode_ruleTrans (Fst recs)
  emit_ih_v1_Df : Fun2
  emit_ih_v1_Df = EmitPair (KT2 tagCode_ruleTrans) RecsFst

  emit_ih_v2_Df : Fun2
  emit_ih_v2_Df = EmitPair (KT2 tagCode_ruleTrans) RecsSnd

  -- emit_Df_E1 : Fun2 emitting Df_E1 = Pair tagCode_axRecNd (Pair zT (Pair sT (Pair cv1 cv2))).
  emit_Df_E1 : Fun2
  emit_Df_E1 = EmitPair (KT2 tagCode_axRecNd)
                (EmitPair (KT2 zT)
                  (EmitPair (KT2 sT)
                    (EmitPair emit_cv1 emit_cv2)))

  -- emit_Df_E_v1 : Fun2 emitting Df_E_v1 =
  --   Pair tagCode_congL (Pair pCT (Pair ih_v1.Df (mkAp1T cf cv2))).
  emit_Df_E_v1 : Fun2
  emit_Df_E_v1 = EmitPair (KT2 tagCode_congL)
                   (EmitPair (KT2 pCT)
                     (EmitPair emit_ih_v1_Df
                       (emit_mkAp1Tcf emit_cv2)))

  -- emit_Df_E_v1_lifted : Fun2 emitting Df_E_v1_lifted =
  --   Pair tagCode_congR (Pair sT (Pair Df_E_v1 X)).
  emit_Df_E_v1_lifted : Fun2
  emit_Df_E_v1_lifted = EmitPair (KT2 tagCode_congR)
                          (EmitPair (KT2 sT)
                            (EmitPair emit_Df_E_v1 emit_X))

  -- emit_Df_chain1 = Pair tagCode_ruleTrans (Pair Df_E1 Df_E_v1_lifted).
  emit_Df_chain1 : Fun2
  emit_Df_chain1 = EmitPair (KT2 tagCode_ruleTrans)
                     (EmitPair emit_Df_E1 emit_Df_E_v1_lifted)

  -- emit_corRecV1 : Fun2 emitting cor rec_v1 = ap1 cor (ap1 recF (Fst orig))
  --   = ap1 (Comp cor (Comp recF Fst)) orig.
  emit_corRecV1 : Fun2
  emit_corRecV1 = FromOrig (Comp cor (Comp recF Fst))

  -- emit_Df_E_v2 = Pair tagCode_congR (Pair pCT (Pair ih_v2.Df (cor rec_v1))).
  emit_Df_E_v2 : Fun2
  emit_Df_E_v2 = EmitPair (KT2 tagCode_congR)
                   (EmitPair (KT2 pCT)
                     (EmitPair emit_ih_v2_Df emit_corRecV1))

  -- emit_Df_E_v2_lifted = Pair tagCode_congR (Pair sT (Pair Df_E_v2 X)).
  emit_Df_E_v2_lifted : Fun2
  emit_Df_E_v2_lifted = EmitPair (KT2 tagCode_congR)
                          (EmitPair (KT2 sT)
                            (EmitPair emit_Df_E_v2 emit_X))

  ----------------------------------------------------------------------
  -- step_inner : the full Fun2 step that emits the Pair-case content.

  step_inner : Fun2
  step_inner = EmitPair emit_Df_chain1 emit_Df_E_v2_lifted

  ----------------------------------------------------------------------
  -- inner_Rec : Fun1 = Rec lf_inner step_inner.
  --   ap1 inner_Rec O           = lf_inner (via axRecLf).
  --   ap1 inner_Rec (Pair v1 v2) = step_inner (Pair v1 v2)
  --                                  (Pair (inner_Rec v1)(inner_Rec v2))
  --                                via axRecNd.

  inner_Rec : Fun1
  inner_Rec = Rec lf_inner step_inner

  ----------------------------------------------------------------------
  -- Df_F1_Rec_zs : the schematic Theorem 12 witness for Rec z s.
  --
  -- ap1 Df_F1_Rec_zs x = Pair tagCode_ruleTrans (ap1 inner_Rec x)
  -- via axComp2 + axKT.
  --
  -- This Pair-headed structure is what makes the shape proof at var v_i
  -- achievable for IH1Rec packaging.

  Df_F1_Rec_zs : Fun1
  Df_F1_Rec_zs = Comp2 Pair (KT tagCode_ruleTrans) inner_Rec

  ----------------------------------------------------------------------
  -- Step A complete.  Steps B-H to follow:
  --   B (~80 LoC):  Df_F1_Rec_zs_at_O  : Deriv (eqn (ap1 Df_F1_Rec_zs O) lf_inner_form).
  --                Df_F1_Rec_zs_at_Pair : Deriv (eqn (ap1 Df_F1_Rec_zs (Pair v1 v2))
  --                                              (concrete chain Term)).
  --   C (~40 LoC):  shape_at : (x : Term) -> Deriv (eqn (Fst (ap1 Df_F1_Rec_zs x))
  --                                                  (Pair O ...)).
  --   D (~40 LoC):  Th12_at_lf : Deriv (eqn (thmT (ap1 Df_F1_Rec_zs O))
  --                                         (codeFTeq1Asym recF O))
  --                via Step B + Th12_F1_Rec_zs_at_lf (from BRA.Th12Rec) +
  --                parDispRuleTrans wrapping.
  --   E (~40 LoC):  toIH1Rec : (v : Nat) -> Deriv (substF zero (var v) P_Th12_Rec_zs)
  --                            -> IH1Rec recF (var v).
  --   F (~50 LoC):  basePair : (ihD_v1 : Deriv ...) -> (ihD_v2 : Deriv ...)
  --                            -> Deriv (substF zero (Pair (var v1)(var v2)) P_Th12_Rec_zs).
  --                Uses Step E + RecPairCase.thm12_Rec_zs_pair (from BRA.Th12Rec).
  --   G (~80 LoC):  SKI lift via axK + axS + axEqTrans + axEqCong*.
  --   H (~30 LoC):  Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs via ruleIndBT.
