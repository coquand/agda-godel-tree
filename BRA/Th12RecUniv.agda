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
open import BRA.ReifyClosed  using (reifyClosed)
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.Tag using
  ( tagAxRecLf ; tagRuleTrans )
open import BRA.Thm.ThmT using
  ( thmT ; thClosed
  ; tagCode_axRecLf
  ; tagCode_ruleTrans ; tagCode_axRecNd ; tagCode_axRefl
  ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRefl_param ; thmTDispRuleTrans_param )
import BRA.Th12Rec

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
  (z_corLemma : Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))
  -- Closure assumptions: z and s contain no free var (they're recursion
  -- parameters; in practice always closed -- O, numerals, or closed
  -- combinator expressions).  The caller commits to these.
  (z_closed : (x : Nat) (r : Term) -> Eq (subst x r z) z)
  (s_closed : (x : Nat) (r : Term) -> Eq (substF2 x r s) s)
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
  Df_lf_orig = ap2 Pair tagCode_axRecLf (ap2 Pair zT sT)

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
  -- Step B1: BRA-equality reduction at O.
  --
  --   ap1 Df_F1_Rec_zs O =BRA Pair tagCode_ruleTrans lf_inner.
  --
  -- Proof: axComp2 + axKT + axRecLf composed via congL/congR.

  Df_F1_Rec_zs_at_O :
    Deriv (atomic (eqn (ap1 Df_F1_Rec_zs O)
                       (ap2 Pair tagCode_ruleTrans lf_inner)))
  Df_F1_Rec_zs_at_O =
    let
      s1 : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs O)
                              (ap2 Pair (ap1 (KT tagCode_ruleTrans) O)
                                        (ap1 inner_Rec O))))
      s1 = axComp2 Pair (KT tagCode_ruleTrans) inner_Rec O

      s2 : Deriv (atomic (eqn (ap1 (KT tagCode_ruleTrans) O) tagCode_ruleTrans))
      s2 = axKT (natCode tagRuleTrans) O

      s3 : Deriv (atomic (eqn (ap1 inner_Rec O) lf_inner))
      s3 = axRecLf lf_inner step_inner

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair (ap1 (KT tagCode_ruleTrans) O)(ap1 inner_Rec O))
                  (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec O))))
      step_LHS = congL Pair (ap1 inner_Rec O) s2

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec O))
                  (ap2 Pair tagCode_ruleTrans lf_inner)))
      step_RHS = congR Pair tagCode_ruleTrans s3
    in ruleTrans s1 (ruleTrans step_LHS step_RHS)

  ----------------------------------------------------------------------
  -- Helper: generalisation of Step B1 to any input x.
  --
  --   ap1 Df_F1_Rec_zs x  =BRA  Pair tagCode_ruleTrans (ap1 inner_Rec x).
  --
  -- This is the OUTER reduction (Comp2 Pair (KT _) inner_Rec); the inner
  -- inner_Rec doesn't reduce on opaque x.

  wrapped_inner_Rec : Term -> Term
  wrapped_inner_Rec x = ap2 Pair tagCode_ruleTrans (ap1 inner_Rec x)

  Df_F1_Rec_zs_reduce_outer : (x : Term) ->
    Deriv (atomic (eqn (ap1 Df_F1_Rec_zs x) (wrapped_inner_Rec x)))
  Df_F1_Rec_zs_reduce_outer x =
    let
      s1 : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs x)
                              (ap2 Pair (ap1 (KT tagCode_ruleTrans) x)
                                        (ap1 inner_Rec x))))
      s1 = axComp2 Pair (KT tagCode_ruleTrans) inner_Rec x

      s2 : Deriv (atomic (eqn (ap1 (KT tagCode_ruleTrans) x) tagCode_ruleTrans))
      s2 = axKT (natCode tagRuleTrans) x

      step : Deriv (atomic (eqn (ap2 Pair (ap1 (KT tagCode_ruleTrans) x)(ap1 inner_Rec x))
                                 (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec x))))
      step = congL Pair (ap1 inner_Rec x) s2
    in ruleTrans s1 step

  ----------------------------------------------------------------------
  -- Step B2 reduction lemmas: BRA reductions of step_inner's emit_X
  -- combinators at runtime (orig = Pair v1 v2, recs = Pair r1 r2).

  -- Generic helper: EmitPair_red.
  EmitPair_red : (ha hb : Fun2) (orig recs : Term) (a' b' : Term)
              -> Deriv (atomic (eqn (ap2 ha orig recs) a'))
              -> Deriv (atomic (eqn (ap2 hb orig recs) b'))
              -> Deriv (atomic (eqn (ap2 (EmitPair ha hb) orig recs) (ap2 Pair a' b')))
  EmitPair_red ha hb orig recs a' b' Da Db =
    let s1 = axFan ha hb Pair orig recs
        s2 = congL Pair (ap2 hb orig recs) Da
        s3 = congR Pair a' Db
    in ruleTrans s1 (ruleTrans s2 s3)

  -- KT2_red: ap2 (Lift (KT (reify T))) orig recs = reify T.
  KT2_reify_red : (T : Tree) (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (KT (reify T))) orig recs) (reify T)))
  KT2_reify_red T orig recs =
    ruleTrans (axLift (KT (reify T)) orig recs) (axKT T orig)

  -- emit_cv1 reduces to ap1 cor v1 at orig=Pair v1 v2.
  emit_cv1_red : (v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cv1 (ap2 Pair v1' v2') recs) (ap1 cor v1')))
  emit_cv1_red v1' v2' recs =
    let s1 = axLift (Comp cor Fst) (ap2 Pair v1' v2') recs
        s2 = axComp cor Fst (ap2 Pair v1' v2')
        s3 = cong1 cor (axFst v1' v2')
    in ruleTrans s1 (ruleTrans s2 s3)

  -- emit_cv2 reduces to ap1 cor v2 at orig=Pair v1 v2.
  emit_cv2_red : (v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cv2 (ap2 Pair v1' v2') recs) (ap1 cor v2')))
  emit_cv2_red v1' v2' recs =
    let s1 = axLift (Comp cor Snd) (ap2 Pair v1' v2') recs
        s2 = axComp cor Snd (ap2 Pair v1' v2')
        s3 = cong1 cor (axSnd v1' v2')
    in ruleTrans s1 (ruleTrans s2 s3)

  -- emit_corRecV1 reduces to cor (recF v1) at orig=Pair v1 v2.
  emit_corRecV1_red : (v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_corRecV1 (ap2 Pair v1' v2') recs)
                       (ap1 cor (ap1 recF v1'))))
  emit_corRecV1_red v1' v2' recs =
    let s1 = axLift (Comp cor (Comp recF Fst)) (ap2 Pair v1' v2') recs
        s2 = axComp cor (Comp recF Fst) (ap2 Pair v1' v2')
        s3 = cong1 cor (axComp recF Fst (ap2 Pair v1' v2'))
        s4 = cong1 cor (cong1 recF (axFst v1' v2'))
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  -- RecsFst at orig=any, recs=Pair r1 r2 reduces to r1.
  RecsFst_red : (orig r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 RecsFst orig (ap2 Pair r1 r2)) r1))
  RecsFst_red orig r1 r2 =
    let s1 = axPost Fst Recs orig (ap2 Pair r1 r2)
        s2 = cong1 Fst (axPost Snd Pair orig (ap2 Pair r1 r2))
        s3 = cong1 Fst (axSnd orig (ap2 Pair r1 r2))
        s4 = axFst r1 r2
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  -- RecsSnd similarly.
  RecsSnd_red : (orig r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 RecsSnd orig (ap2 Pair r1 r2)) r2))
  RecsSnd_red orig r1 r2 =
    let s1 = axPost Snd Recs orig (ap2 Pair r1 r2)
        s2 = cong1 Snd (axPost Snd Pair orig (ap2 Pair r1 r2))
        s3 = cong1 Snd (axSnd orig (ap2 Pair r1 r2))
        s4 = axSnd r1 r2
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  -- emit_ih_v1_Df reduces to wrapped_inner_Rec (var v1) at runtime.
  -- emit_ih_v1_Df = EmitPair (KT2 tagCode_ruleTrans) RecsFst.
  emit_ih_v1_Df_red : (v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_ih_v1_Df (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_ruleTrans r1)))
  emit_ih_v1_Df_red v1' v2' r1 r2 =
    EmitPair_red (KT2 tagCode_ruleTrans) RecsFst
      (ap2 Pair v1' v2') (ap2 Pair r1 r2)
      tagCode_ruleTrans r1
      (KT2_reify_red (natCode tagRuleTrans) (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (RecsFst_red (ap2 Pair v1' v2') r1 r2)

  emit_ih_v2_Df_red : (v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_ih_v2_Df (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_ruleTrans r2)))
  emit_ih_v2_Df_red v1' v2' r1 r2 =
    EmitPair_red (KT2 tagCode_ruleTrans) RecsSnd
      (ap2 Pair v1' v2') (ap2 Pair r1 r2)
      tagCode_ruleTrans r2
      (KT2_reify_red (natCode tagRuleTrans) (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (RecsSnd_red (ap2 Pair v1' v2') r1 r2)

  -- emit_X reduces to mkAp2T pCT cv1 cv2 (= X' in Df_chain12_at) at runtime.
  emit_X_red : (v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_X (ap2 Pair v1' v2') recs)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair pCT (ap2 Pair (ap1 cor v1')(ap1 cor v2'))))))
  emit_X_red v1' v2' recs =
    EmitPair_red (KT2 (reify tagAp2)) _
      (ap2 Pair v1' v2') recs (reify tagAp2) _
      (KT2_reify_red tagAp2 (ap2 Pair v1' v2') recs)
      (EmitPair_red (KT2 pCT) _
        (ap2 Pair v1' v2') recs pCT _
        (KT2_reify_red (codeF2 Pair) (ap2 Pair v1' v2') recs)
        (EmitPair_red emit_cv1 emit_cv2
          (ap2 Pair v1' v2') recs (ap1 cor v1') (ap1 cor v2')
          (emit_cv1_red v1' v2' recs)
          (emit_cv2_red v1' v2' recs)))

  -- emit_mkAp1Tcf at emit_t reduces to mkAp1T cf t' if emit_t reduces to t'.
  emit_mkAp1Tcf_red : (emit_t : Fun2) (orig recs : Term) (t' : Term) ->
    Deriv (atomic (eqn (ap2 emit_t orig recs) t')) ->
    Deriv (atomic (eqn (ap2 (emit_mkAp1Tcf emit_t) orig recs)
                       (ap2 Pair (reify tagAp1) (ap2 Pair cf t'))))
  emit_mkAp1Tcf_red emit_t orig recs t' Dt =
    EmitPair_red (KT2 (reify tagAp1)) _
      orig recs (reify tagAp1) _
      (KT2_reify_red tagAp1 orig recs)
      (EmitPair_red (KT2 cf) emit_t
        orig recs cf t'
        (KT2_reify_red (codeF1 recF) orig recs)
        Dt)

  -- emit_Df_E1 reduces to Df_E1 (per Df_chain12_at).
  emit_Df_E1_red : (v1' v2' recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_Df_E1 (ap2 Pair v1' v2') recs)
                       (ap2 Pair tagCode_axRecNd
                         (ap2 Pair zT (ap2 Pair sT
                           (ap2 Pair (ap1 cor v1')(ap1 cor v2')))))))
  emit_Df_E1_red v1' v2' recs =
    EmitPair_red (KT2 tagCode_axRecNd) _
      (ap2 Pair v1' v2') recs tagCode_axRecNd _
      (KT2_reify_red _ (ap2 Pair v1' v2') recs)
      (EmitPair_red (KT2 zT) _
        (ap2 Pair v1' v2') recs zT _
        (KT2_reify_red (code z) (ap2 Pair v1' v2') recs)
        (EmitPair_red (KT2 sT) _
          (ap2 Pair v1' v2') recs sT _
          (KT2_reify_red (codeF2 s) (ap2 Pair v1' v2') recs)
          (EmitPair_red emit_cv1 emit_cv2
            (ap2 Pair v1' v2') recs (ap1 cor v1') (ap1 cor v2')
            (emit_cv1_red v1' v2' recs)
            (emit_cv2_red v1' v2' recs))))

  -- emit_Df_E_v1 reduces to Df_E_v1.
  emit_Df_E_v1_red : (v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_Df_E_v1 (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_congL
                         (ap2 Pair pCT (ap2 Pair (ap2 Pair tagCode_ruleTrans r1)
                                                  (ap2 Pair (reify tagAp1)
                                                    (ap2 Pair cf (ap1 cor v2'))))))))
  emit_Df_E_v1_red v1' v2' r1 r2 =
    EmitPair_red (KT2 tagCode_congL) _
      (ap2 Pair v1' v2') (ap2 Pair r1 r2) tagCode_congL _
      (KT2_reify_red _ (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (EmitPair_red (KT2 pCT) _
        (ap2 Pair v1' v2') (ap2 Pair r1 r2) pCT _
        (KT2_reify_red (codeF2 Pair) (ap2 Pair v1' v2') (ap2 Pair r1 r2))
        (EmitPair_red emit_ih_v1_Df _
          (ap2 Pair v1' v2') (ap2 Pair r1 r2)
          (ap2 Pair tagCode_ruleTrans r1) _
          (emit_ih_v1_Df_red v1' v2' r1 r2)
          (emit_mkAp1Tcf_red emit_cv2 (ap2 Pair v1' v2') (ap2 Pair r1 r2)
            (ap1 cor v2') (emit_cv2_red v1' v2' (ap2 Pair r1 r2)))))

  -- emit_Df_E_v1_lifted reduces to Df_E_v1_lifted.
  emit_Df_E_v1_lifted_red : (v1' v2' r1 r2 : Term)
    (Df_E_v1' : Term)
    (Df_E_v1_red : Deriv (atomic (eqn (ap2 emit_Df_E_v1 (ap2 Pair v1' v2') (ap2 Pair r1 r2)) Df_E_v1'))) ->
    Deriv (atomic (eqn (ap2 emit_Df_E_v1_lifted (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_congR
                         (ap2 Pair sT
                           (ap2 Pair Df_E_v1'
                                     (ap2 Pair (reify tagAp2)
                                       (ap2 Pair pCT
                                         (ap2 Pair (ap1 cor v1')(ap1 cor v2')))))))))
  emit_Df_E_v1_lifted_red v1' v2' r1 r2 Df_E_v1' Df_E_v1_red =
    EmitPair_red (KT2 tagCode_congR) _
      (ap2 Pair v1' v2') (ap2 Pair r1 r2) tagCode_congR _
      (KT2_reify_red _ (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (EmitPair_red (KT2 sT) _
        (ap2 Pair v1' v2') (ap2 Pair r1 r2) sT _
        (KT2_reify_red (codeF2 s) (ap2 Pair v1' v2') (ap2 Pair r1 r2))
        (EmitPair_red emit_Df_E_v1 emit_X
          (ap2 Pair v1' v2') (ap2 Pair r1 r2)
          Df_E_v1' _
          Df_E_v1_red
          (emit_X_red v1' v2' (ap2 Pair r1 r2))))

  -- emit_Df_chain1 reduces to Df_chain1.
  emit_Df_chain1_red : (v1' v2' r1 r2 : Term)
    (Df_E1' Df_E_v1_lifted' : Term)
    (DE1 : Deriv (atomic (eqn (ap2 emit_Df_E1 (ap2 Pair v1' v2') (ap2 Pair r1 r2)) Df_E1')))
    (DEv1 : Deriv (atomic (eqn (ap2 emit_Df_E_v1_lifted (ap2 Pair v1' v2') (ap2 Pair r1 r2)) Df_E_v1_lifted'))) ->
    Deriv (atomic (eqn (ap2 emit_Df_chain1 (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1' Df_E_v1_lifted'))))
  emit_Df_chain1_red v1' v2' r1 r2 Df_E1' Df_E_v1_lifted' DE1 DEv1 =
    EmitPair_red (KT2 tagCode_ruleTrans) _
      (ap2 Pair v1' v2') (ap2 Pair r1 r2) tagCode_ruleTrans _
      (KT2_reify_red _ (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (EmitPair_red emit_Df_E1 emit_Df_E_v1_lifted
        (ap2 Pair v1' v2') (ap2 Pair r1 r2)
        Df_E1' Df_E_v1_lifted'
        DE1 DEv1)

  emit_Df_E_v2_red : (v1' v2' r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_Df_E_v2 (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_congR
                         (ap2 Pair pCT
                           (ap2 Pair (ap2 Pair tagCode_ruleTrans r2)
                                     (ap1 cor (ap1 recF v1')))))))
  emit_Df_E_v2_red v1' v2' r1 r2 =
    EmitPair_red (KT2 tagCode_congR) _
      (ap2 Pair v1' v2') (ap2 Pair r1 r2) tagCode_congR _
      (KT2_reify_red _ (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (EmitPair_red (KT2 pCT) _
        (ap2 Pair v1' v2') (ap2 Pair r1 r2) pCT _
        (KT2_reify_red (codeF2 Pair) (ap2 Pair v1' v2') (ap2 Pair r1 r2))
        (EmitPair_red emit_ih_v2_Df emit_corRecV1
          (ap2 Pair v1' v2') (ap2 Pair r1 r2)
          (ap2 Pair tagCode_ruleTrans r2) (ap1 cor (ap1 recF v1'))
          (emit_ih_v2_Df_red v1' v2' r1 r2)
          (emit_corRecV1_red v1' v2' (ap2 Pair r1 r2))))

  emit_Df_E_v2_lifted_red : (v1' v2' r1 r2 : Term)
    (Df_E_v2' : Term)
    (DE2 : Deriv (atomic (eqn (ap2 emit_Df_E_v2 (ap2 Pair v1' v2') (ap2 Pair r1 r2)) Df_E_v2'))) ->
    Deriv (atomic (eqn (ap2 emit_Df_E_v2_lifted (ap2 Pair v1' v2') (ap2 Pair r1 r2))
                       (ap2 Pair tagCode_congR
                         (ap2 Pair sT
                           (ap2 Pair Df_E_v2'
                                     (ap2 Pair (reify tagAp2)
                                       (ap2 Pair pCT
                                         (ap2 Pair (ap1 cor v1')(ap1 cor v2')))))))))
  emit_Df_E_v2_lifted_red v1' v2' r1 r2 Df_E_v2' DE2 =
    EmitPair_red (KT2 tagCode_congR) _
      (ap2 Pair v1' v2') (ap2 Pair r1 r2) tagCode_congR _
      (KT2_reify_red _ (ap2 Pair v1' v2') (ap2 Pair r1 r2))
      (EmitPair_red (KT2 sT) _
        (ap2 Pair v1' v2') (ap2 Pair r1 r2) sT _
        (KT2_reify_red (codeF2 s) (ap2 Pair v1' v2') (ap2 Pair r1 r2))
        (EmitPair_red emit_Df_E_v2 emit_X
          (ap2 Pair v1' v2') (ap2 Pair r1 r2)
          Df_E_v2' _
          DE2
          (emit_X_red v1' v2' (ap2 Pair r1 r2))))

  ----------------------------------------------------------------------
  -- Step B2: Df_F1_Rec_zs_at_Pair_proven.
  --
  -- Compose:
  --   ap1 Df_F1_Rec_zs (Pair v1 v2)
  --   = wrapped_inner_Rec (Pair v1 v2)              [Df_F1_Rec_zs_reduce_outer]
  --   = Pair tagCode_ruleTrans (ap1 inner_Rec (Pair v1 v2))
  --   = Pair tagCode_ruleTrans (ap2 step_inner pairT (Pair r1 r2))    [axRecNd]
  --   = Pair tagCode_ruleTrans (Pair Df_chain1 Df_E_v2_lifted)
  --   = Df_chain12_at v1 v2.

  -- Internal helper: Df_F1_Rec_zs_at_Pair_proven_explicit, RHS in expanded form.
  -- The Df_F1_Rec_zs_at_Pair_proven (matching Df_chain12_at signature)
  -- comes later in the file after Df_chain12_at is defined.

  Df_F1_Rec_zs_at_Pair_explicit : (v1 v2 : Nat) ->
    Deriv (atomic (eqn (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2)))
                       (ap2 Pair tagCode_ruleTrans
                         (ap2 Pair
                           -- Df_chain1' (= Df_chain1 in Df_chain12_at).
                           (ap2 Pair tagCode_ruleTrans
                             (ap2 Pair
                               -- Df_E1' (= Df_E1).
                               (ap2 Pair tagCode_axRecNd
                                 (ap2 Pair zT (ap2 Pair sT
                                   (ap2 Pair (ap1 cor (var v1))(ap1 cor (var v2))))))
                               -- Df_E_v1_lifted'.
                               (ap2 Pair tagCode_congR
                                 (ap2 Pair sT
                                   (ap2 Pair
                                     -- Df_E_v1'.
                                     (ap2 Pair tagCode_congL
                                       (ap2 Pair pCT
                                         (ap2 Pair
                                           (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec (var v1)))
                                           (ap2 Pair (reify tagAp1)
                                             (ap2 Pair cf (ap1 cor (var v2)))))))
                                     -- X'.
                                     (ap2 Pair (reify tagAp2)
                                       (ap2 Pair pCT
                                         (ap2 Pair (ap1 cor (var v1))(ap1 cor (var v2))))))))))
                           -- Df_E_v2_lifted'.
                           (ap2 Pair tagCode_congR
                             (ap2 Pair sT
                               (ap2 Pair
                                 -- Df_E_v2'.
                                 (ap2 Pair tagCode_congR
                                   (ap2 Pair pCT
                                     (ap2 Pair
                                       (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec (var v2)))
                                       (ap1 cor (ap1 recF (var v1))))))
                                 -- X'.
                                 (ap2 Pair (reify tagAp2)
                                   (ap2 Pair pCT
                                     (ap2 Pair (ap1 cor (var v1))(ap1 cor (var v2))))))))))))
  Df_F1_Rec_zs_at_Pair_explicit v1 v2 =
    let
      pairT = ap2 Pair (var v1) (var v2)
      r1 = ap1 inner_Rec (var v1)
      r2 = ap1 inner_Rec (var v2)
      recs = ap2 Pair r1 r2

      -- Stage 1: outer reduction.
      stage1 : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs pairT) (wrapped_inner_Rec pairT)))
      stage1 = Df_F1_Rec_zs_reduce_outer pairT

      -- Stage 2: ap1 inner_Rec pairT = step_inner orig recs.
      stage2 : Deriv (atomic (eqn (ap1 inner_Rec pairT)
                                   (ap2 step_inner pairT recs)))
      stage2 = axRecNd lf_inner step_inner (var v1) (var v2)

      -- Stage 3: step_inner orig recs reduces to chain content.
      -- step_inner = EmitPair emit_Df_chain1 emit_Df_E_v2_lifted.

      -- Compute chain1 and chain1_lifted Term forms.
      Df_E1' : Term
      Df_E1' = ap2 Pair tagCode_axRecNd
                  (ap2 Pair zT (ap2 Pair sT (ap2 Pair (ap1 cor (var v1))(ap1 cor (var v2)))))

      Df_E_v1' : Term
      Df_E_v1' = ap2 Pair tagCode_congL
                    (ap2 Pair pCT
                      (ap2 Pair (ap2 Pair tagCode_ruleTrans r1)
                                (ap2 Pair (reify tagAp1)
                                  (ap2 Pair cf (ap1 cor (var v2))))))

      Df_E_v1_lifted' : Term
      Df_E_v1_lifted' = ap2 Pair tagCode_congR
                          (ap2 Pair sT
                            (ap2 Pair Df_E_v1'
                                      (ap2 Pair (reify tagAp2)
                                        (ap2 Pair pCT
                                          (ap2 Pair (ap1 cor (var v1))(ap1 cor (var v2)))))))

      Df_chain1' : Term
      Df_chain1' = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1' Df_E_v1_lifted')

      Df_E_v2' : Term
      Df_E_v2' = ap2 Pair tagCode_congR
                    (ap2 Pair pCT
                      (ap2 Pair (ap2 Pair tagCode_ruleTrans r2)
                                (ap1 cor (ap1 recF (var v1)))))

      Df_E_v2_lifted' : Term
      Df_E_v2_lifted' = ap2 Pair tagCode_congR
                          (ap2 Pair sT
                            (ap2 Pair Df_E_v2'
                                      (ap2 Pair (reify tagAp2)
                                        (ap2 Pair pCT
                                          (ap2 Pair (ap1 cor (var v1))(ap1 cor (var v2)))))))

      -- step_inner reduces to Pair Df_chain1' Df_E_v2_lifted'.
      stage3 : Deriv (atomic (eqn (ap2 step_inner pairT recs)
                                   (ap2 Pair Df_chain1' Df_E_v2_lifted')))
      stage3 =
        EmitPair_red emit_Df_chain1 emit_Df_E_v2_lifted
          pairT recs Df_chain1' Df_E_v2_lifted'
          (emit_Df_chain1_red (var v1) (var v2) r1 r2 Df_E1' Df_E_v1_lifted'
            (emit_Df_E1_red (var v1) (var v2) recs)
            (emit_Df_E_v1_lifted_red (var v1) (var v2) r1 r2 Df_E_v1'
              (emit_Df_E_v1_red (var v1) (var v2) r1 r2)))
          (emit_Df_E_v2_lifted_red (var v1) (var v2) r1 r2 Df_E_v2'
            (emit_Df_E_v2_red (var v1) (var v2) r1 r2))

      -- Combine stage 2 + stage 3: ap1 inner_Rec pairT = Pair Df_chain1' Df_E_v2_lifted'.
      stage23 : Deriv (atomic (eqn (ap1 inner_Rec pairT)
                                    (ap2 Pair Df_chain1' Df_E_v2_lifted')))
      stage23 = ruleTrans stage2 stage3

      -- Combine stage 1 + cong: Df_F1_Rec_zs pairT = Pair tagCode_ruleTrans (Pair Df_chain1' Df_E_v2_lifted').
      stage_final : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs pairT)
                                        (ap2 Pair tagCode_ruleTrans
                                          (ap2 Pair Df_chain1' Df_E_v2_lifted'))))
      stage_final = ruleTrans stage1 (congR Pair tagCode_ruleTrans stage23)
    in stage_final

  ----------------------------------------------------------------------
  -- Step C: shape proof at any input x.
  --
  --   Fst (ap1 Df_F1_Rec_zs x)  =BRA  tagCode_ruleTrans.
  --
  -- And tagCode_ruleTrans = reify (natCode tagRuleTrans) = Pair O <rest>
  -- (since natCode of any non-zero tag is nd lf <rest>, and reify of
  -- nd a b = ap2 Pair (reify a)(reify b)).  So tagCode_ruleTrans IS
  -- a Pair-Term, satisfying IH1Rec.shape's requirement.
  --
  -- Proof: axComp2 + axKT for the Pair structure, then axFst + cong1.

  shape_at : (x : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Df_F1_Rec_zs x)) tagCode_ruleTrans))
  shape_at x =
    let
      s1 : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs x)
                              (ap2 Pair (ap1 (KT tagCode_ruleTrans) x)
                                        (ap1 inner_Rec x))))
      s1 = axComp2 Pair (KT tagCode_ruleTrans) inner_Rec x

      s2 : Deriv (atomic (eqn (ap1 (KT tagCode_ruleTrans) x) tagCode_ruleTrans))
      s2 = axKT (natCode tagRuleTrans) x

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair (ap1 (KT tagCode_ruleTrans) x)(ap1 inner_Rec x))
                  (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec x))))
      step_LHS = congL Pair (ap1 inner_Rec x) s2

      reduce_Df : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs x)
                                     (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec x))))
      reduce_Df = ruleTrans s1 step_LHS

      cong_Fst : Deriv (atomic (eqn (ap1 Fst (ap1 Df_F1_Rec_zs x))
                                    (ap1 Fst (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec x)))))
      cong_Fst = cong1 Fst reduce_Df

      fst_proj : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagCode_ruleTrans (ap1 inner_Rec x)))
                                    tagCode_ruleTrans))
      fst_proj = axFst tagCode_ruleTrans (ap1 inner_Rec x)
    in ruleTrans cong_Fst fst_proj

  ----------------------------------------------------------------------
  -- Reuse the proven Th12_F1_Rec_zs_at_lf from BRA.Th12Rec.Th12RecCase.

  open BRA.Th12Rec.Th12RecCase z s z_corLemma using
    ( Th12_F1_Rec_zs_at_lf )
  -- Th12_F1_Rec_zs_at_lf : Deriv (eqn (thmT Df_lf_orig)(codeFTeq1Asym recF O))
  -- where Df_lf_orig = ap2 Pair tagCode_axRecLf (ap2 Pair zT sT) (matches our Df_lf_orig).

  ----------------------------------------------------------------------
  -- Step D: Th12_at_lf : Deriv (substF zero O P_Th12_Rec_zs).
  --
  -- Strategy:
  --   1. Build the explicit form of substF zero O P_Th12_Rec_zs:
  --      atomic (eqn (ap1 (substF1 zero O thmT)(ap1 (substF1 zero O Df_F1_Rec_zs) O))
  --                   (codeFTeq1Asym recF O))
  --      (the var 0 inside (var zero) substitutes to O).
  --   2. Bridge thmT-fixity via thClosed.
  --   3. Bridge Df_F1_Rec_zs-fixity via Df_F1_Rec_zs_closed.
  --   4. Apply Th12_F1_Rec_zs_at_lf composed via parDispRuleTrans + axRefl
  --      (since our Df_F1_Rec_zs O = Pair tagCode_ruleTrans lf_inner has the
  --       outer ruleTrans wrapping; we use thmTDispRuleTrans_param to compute
  --       its thmT-image).

  P_Th12_Rec_zs : Formula
  P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (var zero)))
                              (codeFTeq1Asym recF (var zero)))

  -- Step D auxiliary:  thmT image of Df_F1_Rec_zs O = Pair tagCode_ruleTrans lf_inner
  -- equals codeFTeq1Asym recF O via parDispRuleTrans + axRefl threading.

  Th12_at_lf_concrete :
    Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs O)) (codeFTeq1Asym recF O)))
  Th12_at_lf_concrete =
    let
      -- thmT (Pair tagCode_ruleTrans lf_inner) via parDispRuleTrans_param.
      --
      -- lf_inner = Pair Df_lf_orig encAxReflRecFO.
      -- y1 = Df_lf_orig: image Pair (mkAp1T cf (cor O))(cor (recF O)).
      -- y2 = encAxReflRecFO = Pair tagCode_axRefl (cor (recF O)):
      --      image Pair (cor (recF O))(cor (recF O))   [via thmTDispAxRefl_param].
      -- composed: Pair (mkAp1T cf (cor O))(cor (recF O)) = codeFTeq1Asym recF O.

      cor_recF_O : Term
      cor_recF_O = ap1 cor (ap1 recF O)

      cor_O : Term
      cor_O = ap1 cor O

      lhsLeft : Term
      lhsLeft = mkAp1T cf cor_O

      -- thmT y1 = Pair lhsLeft cor_recF_O (= codeFTeq1Asym recF O).
      img_y1 : Deriv (atomic (eqn (ap1 thmT Df_lf_orig) (codeFTeq1Asym recF O)))
      img_y1 = Th12_F1_Rec_zs_at_lf

      -- thmT y2 = Pair cor_recF_O cor_recF_O via thmTDispAxRefl_param.
      img_y2 : Deriv (atomic (eqn (ap1 thmT encAxReflRecFO)
                                   (ap2 Pair cor_recF_O cor_recF_O)))
      img_y2 = thmTDispAxRefl_param cor_recF_O

      -- Shape proof for y1: Fst Df_lf_orig = tagCode_axRecLf = Pair O ...
      shape_y1 : Deriv (atomic (eqn (ap1 Fst Df_lf_orig) tagCode_axRecLf))
      shape_y1 = axFst tagCode_axRecLf (ap2 Pair zT sT)

      -- Compose via thmTDispRuleTrans_param.
      -- Pair tagCode_ruleTrans lf_inner = Pair tagCode_ruleTrans (Pair Df_lf_orig encAxReflRecFO).
      composed : Deriv (atomic (eqn
        (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair Df_lf_orig encAxReflRecFO)))
        (ap2 Pair lhsLeft cor_recF_O)))
      composed = thmTDispRuleTrans_param Df_lf_orig encAxReflRecFO
                   lhsLeft cor_recF_O cor_recF_O cor_recF_O
                   _ _ shape_y1 img_y1 img_y2

      -- Bridge: ap1 thmT (ap1 Df_F1_Rec_zs O) -> ap1 thmT (Pair tagCode_ruleTrans lf_inner)
      -- via cong1 thmT (Df_F1_Rec_zs_at_O).
      reduce_outer : Deriv (atomic (eqn
        (ap1 thmT (ap1 Df_F1_Rec_zs O))
        (ap1 thmT (ap2 Pair tagCode_ruleTrans lf_inner))))
      reduce_outer = cong1 thmT Df_F1_Rec_zs_at_O

      -- ap2 Pair lhsLeft cor_recF_O = codeFTeq1Asym recF O (definitionally).
      -- codeFTeq1Asym recF O = mkEqT (mkAp1T cf (cor O))(cor (recF O))
      --                     = ap2 Pair (mkAp1T cf cor_O) cor_recF_O = ap2 Pair lhsLeft cor_recF_O. ✓
    in ruleTrans reduce_outer composed

  ----------------------------------------------------------------------
  -- Step D: lift Th12_at_lf_concrete to substF zero O P_Th12_Rec_zs via
  -- thClosed and Df_F1_Rec_zs_closed.
  --
  -- substF zero O P_Th12_Rec_zs computes (Agda definitional reduction)
  -- to atomic (eqn (ap1 (substF1 zero O thmT)(ap1 (substF1 zero O Df_F1_Rec_zs) O))
  --                 (codeFTeq1Asym (substF1 zero O recF) O)).
  --
  -- We need to bridge:
  --   substF1 zero O thmT = thmT          [thClosed].
  --   substF1 zero O Df_F1_Rec_zs = Df_F1_Rec_zs   [Df_F1_Rec_zs_closed, derived].
  --   substF1 zero O recF = recF          [from z_closed, s_closed].
  --
  -- The Eq lemmas combined via eqSubst convert Th12_at_lf_concrete into
  -- the required Deriv form.

  -- Df_F1_Rec_zs_closed : Eq (substF1 zero O Df_F1_Rec_zs) Df_F1_Rec_zs.
  --   substF1 zero O (Comp2 Pair (KT tagCode_ruleTrans) inner_Rec)
  --   = Comp2 Pair (substF1 zero O (KT tagCode_ruleTrans))(substF1 zero O inner_Rec).
  --   substF1 zero O (KT k) reduces to KT (subst zero O k); we need
  --     (subst zero O tagCode_ruleTrans) = tagCode_ruleTrans (closed reify).
  --   substF1 zero O (Rec lf_inner step_inner)
  --   = Rec (subst zero O lf_inner)(substF2 zero O step_inner).
  --     subst zero O lf_inner uses subst zero O on Df_lf_orig (= Pair zT sT-form, all closed)
  --     and on encAxReflRecFO (= Pair tagCode_axRefl (cor (recF O))).
  --     For this to be closed, need recF closed (= z, s closed) and cor closed (it is, defined as Rec O stepCor with closed stepCor).
  --
  -- This Eq lemma requires careful structural induction.  We defer the
  -- proof to the next sub-step (Step D2).  For Step D currently, we
  -- ASSUME it as a parameter and provide it in the closure.

  ----------------------------------------------------------------------
  -- Step D-final: structural Eq lemmas.
  --
  -- recF_closed : substF1 x r recF = recF (from z_closed + s_closed).
  -- cor_closed_eq : substF1 x r cor = cor (cor is structurally closed
  --                 since cor = Rec O stepCor with O closed and stepCor
  --                 a closed Fun2 expression; provable by structural
  --                 unfolding which reduces to refl).

  recF_closed : (x : Nat) (r : Term) -> Eq (substF1 x r recF) recF
  recF_closed x r = eqCong2 Rec (z_closed x r) (s_closed x r)

  -- cor = Rec O stepCor where O is closed and stepCor is a closed Fun2.
  -- Therefore substF1 x r cor reduces (Agda) to Rec O stepCor = cor.
  -- This holds by definitional reduction (refl) since substF1 doesn't
  -- enter Fun2 constants like Pair, Lift, etc., and stepCor's structure
  -- has no free vars.

  cor_closed_eq : (x : Nat) (r : Term) -> Eq (substF1 x r cor) cor
  cor_closed_eq x r = refl

  -- tagCode-style constants are closed (reify of natCode).
  -- subst x r (reify (natCode N)) = reify (natCode N) by reifyClosed.

  tagCode_ruleTrans_closed : (x : Nat) (r : Term) ->
    Eq (subst x r tagCode_ruleTrans) tagCode_ruleTrans
  tagCode_ruleTrans_closed x r = reifyClosed (natCode tagRuleTrans) x r

  tagCode_axRecLf_closed : (x : Nat) (r : Term) ->
    Eq (subst x r tagCode_axRecLf) tagCode_axRecLf
  tagCode_axRecLf_closed x r = reifyClosed (natCode tagAxRecLf) x r

  tagCode_axRefl_closed : (x : Nat) (r : Term) ->
    Eq (subst x r tagCode_axRefl) tagCode_axRefl
  tagCode_axRefl_closed x r = reifyClosed _ x r

  -- zT, sT, cf are reify of trees → reify-closed.

  zT_closed : (x : Nat) (r : Term) -> Eq (subst x r zT) zT
  zT_closed x r = reifyClosed (code z) x r

  sT_closed : (x : Nat) (r : Term) -> Eq (subst x r sT) sT
  sT_closed x r = reifyClosed (codeF2 s) x r

  cf_closed : (x : Nat) (r : Term) -> Eq (subst x r cf) cf
  cf_closed x r = reifyClosed (codeF1 recF) x r

  -- pCT = reify (codeF2 Pair) is also closed.
  pCT_closed : (x : Nat) (r : Term) -> Eq (subst x r pCT) pCT
  pCT_closed x r = reifyClosed (codeF2 Pair) x r

  -- Df_lf_orig = ap2 Pair tagCode_axRecLf (ap2 Pair zT sT). All closed parts.
  Df_lf_orig_closed : (x : Nat) (r : Term) -> Eq (subst x r Df_lf_orig) Df_lf_orig
  Df_lf_orig_closed x r =
    eqCong2 (\ a b -> ap2 Pair a (ap2 Pair (fst b) (snd b)))
      (tagCode_axRecLf_closed x r)
      (eqCong2 (\ a b -> mkSigma a b) (zT_closed x r) (sT_closed x r))

  -- encAxReflRecFO = ap2 Pair tagCode_axRefl (ap1 cor (ap1 recF O)).
  -- subst x r encAxReflRecFO traverses recF, cor, O.
  encAxReflRecFO_closed : (x : Nat) (r : Term) ->
    Eq (subst x r encAxReflRecFO) encAxReflRecFO
  encAxReflRecFO_closed x r =
    eqCong2 (ap2 Pair)
      (tagCode_axRefl_closed x r)
      (eqCong2 (\ f g -> ap1 f (ap1 g O))
         (cor_closed_eq x r)
         (recF_closed x r))

  lf_inner_closed : (x : Nat) (r : Term) -> Eq (subst x r lf_inner) lf_inner
  lf_inner_closed x r =
    eqCong2 (ap2 Pair) (Df_lf_orig_closed x r) (encAxReflRecFO_closed x r)

  -- Df_F1_Rec_zs is built from constants and Rec on closed parts.
  -- substF1 x r Df_F1_Rec_zs = Comp2 Pair (KT (subst x r tagCode_ruleTrans)) (Rec (subst x r lf_inner)(substF2 x r step_inner)).
  -- Need step_inner_closed too.

  -- step_inner_closed: structural traversal.  step_inner contains many
  -- KT (reify K) sub-Fun1's (closed via reifyClosed) and one Comp recF Fst
  -- (closed via recF_closed).  Helpers below build the Eq cascade.

  -- Helper: substF1 x r (KT (reify T)) = KT (reify T) by structural
  -- induction on T (since KT (reify T) reduces via reify's lf/nd cases).
  KT_reify_substF1_closed : (T : Tree) (x : Nat) (r : Term) ->
    Eq (substF1 x r (KT (reify T))) (KT (reify T))
  KT_reify_substF1_closed lf       x r = refl
  KT_reify_substF1_closed (nd a b) x r =
    eqCong2 (\ aa bb -> Comp2 Pair aa bb)
      (KT_reify_substF1_closed a x r)
      (KT_reify_substF1_closed b x r)

  Lift_KT_reify_closed : (T : Tree) (x : Nat) (r : Term) ->
    Eq (substF2 x r (Lift (KT (reify T)))) (Lift (KT (reify T)))
  Lift_KT_reify_closed T x r = eqCong Lift (KT_reify_substF1_closed T x r)

  -- Helper: EmitPair preserves closure.
  EmitPair_closed : (h1 h2 : Fun2) ->
    ((x : Nat) (r : Term) -> Eq (substF2 x r h1) h1) ->
    ((x : Nat) (r : Term) -> Eq (substF2 x r h2) h2) ->
    (x : Nat) (r : Term) -> Eq (substF2 x r (EmitPair h1 h2)) (EmitPair h1 h2)
  EmitPair_closed h1 h2 c1 c2 x r =
    eqCong2 (\ a b -> Fan a b Pair) (c1 x r) (c2 x r)

  -- emit_cv1, emit_cv2, RecsFst, RecsSnd: structurally closed (refl).
  emit_cv1_closed : (x : Nat) (r : Term) -> Eq (substF2 x r emit_cv1) emit_cv1
  emit_cv1_closed x r = refl

  emit_cv2_closed : (x : Nat) (r : Term) -> Eq (substF2 x r emit_cv2) emit_cv2
  emit_cv2_closed x r = refl

  RecsFst_closed : (x : Nat) (r : Term) -> Eq (substF2 x r RecsFst) RecsFst
  RecsFst_closed x r = refl

  RecsSnd_closed : (x : Nat) (r : Term) -> Eq (substF2 x r RecsSnd) RecsSnd
  RecsSnd_closed x r = refl

  -- emit_corRecV1 contains Comp recF Fst -> uses recF_closed.
  emit_corRecV1_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_corRecV1) emit_corRecV1
  emit_corRecV1_closed x r =
    eqCong (\ rec' -> Lift (Comp cor (Comp rec' Fst))) (recF_closed x r)

  -- KT2 K for various K via Lift_KT_reify_closed.
  KT2_tagCode_ruleTrans_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 tagCode_ruleTrans)) (KT2 tagCode_ruleTrans)
  KT2_tagCode_ruleTrans_closed x r = Lift_KT_reify_closed (natCode tagRuleTrans) x r

  KT2_tagCode_axRecNd_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 tagCode_axRecNd)) (KT2 tagCode_axRecNd)
  KT2_tagCode_axRecNd_closed x r = Lift_KT_reify_closed (natCode tagAxRecNd) x r
    where open import BRA.Thm.Tag using (tagAxRecNd)

  KT2_tagCode_congL_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 tagCode_congL)) (KT2 tagCode_congL)
  KT2_tagCode_congL_closed x r = Lift_KT_reify_closed (natCode tagCongL) x r
    where open import BRA.Thm.Tag using (tagCongL)

  KT2_tagCode_congR_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 tagCode_congR)) (KT2 tagCode_congR)
  KT2_tagCode_congR_closed x r = Lift_KT_reify_closed (natCode tagCongR) x r
    where open import BRA.Thm.Tag using (tagCongR)

  KT2_tagAp1_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 (reify tagAp1))) (KT2 (reify tagAp1))
  KT2_tagAp1_closed x r = Lift_KT_reify_closed tagAp1 x r

  KT2_tagAp2_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 (reify tagAp2))) (KT2 (reify tagAp2))
  KT2_tagAp2_closed x r = Lift_KT_reify_closed tagAp2 x r

  KT2_zT_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 zT)) (KT2 zT)
  KT2_zT_closed x r = Lift_KT_reify_closed (code z) x r

  KT2_sT_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 sT)) (KT2 sT)
  KT2_sT_closed x r = Lift_KT_reify_closed (codeF2 s) x r

  KT2_pCT_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 pCT)) (KT2 pCT)
  KT2_pCT_closed x r = Lift_KT_reify_closed (codeF2 Pair) x r

  KT2_cf_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r (KT2 cf)) (KT2 cf)
  KT2_cf_closed x r = Lift_KT_reify_closed (codeF1 recF) x r

  -- Build closure for emit_X = EmitPair (KT2 tagAp2)(EmitPair (KT2 pCT)(EmitPair emit_cv1 emit_cv2)).
  emit_X_closed : (x : Nat) (r : Term) -> Eq (substF2 x r emit_X) emit_X
  emit_X_closed =
    EmitPair_closed _ _ KT2_tagAp2_closed
      (EmitPair_closed _ _ KT2_pCT_closed
        (EmitPair_closed _ _ emit_cv1_closed emit_cv2_closed))

  -- emit_mkAp1Tcf emit_t = EmitPair (KT2 tagAp1)(EmitPair (KT2 cf) emit_t).
  emit_mkAp1Tcf_closed : (emit_t : Fun2) ->
    ((x : Nat) (r : Term) -> Eq (substF2 x r emit_t) emit_t) ->
    (x : Nat) (r : Term) -> Eq (substF2 x r (emit_mkAp1Tcf emit_t)) (emit_mkAp1Tcf emit_t)
  emit_mkAp1Tcf_closed emit_t et_closed =
    EmitPair_closed _ _ KT2_tagAp1_closed
      (EmitPair_closed _ _ KT2_cf_closed et_closed)

  emit_ih_v1_Df_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_ih_v1_Df) emit_ih_v1_Df
  emit_ih_v1_Df_closed =
    EmitPair_closed _ _ KT2_tagCode_ruleTrans_closed RecsFst_closed

  emit_ih_v2_Df_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_ih_v2_Df) emit_ih_v2_Df
  emit_ih_v2_Df_closed =
    EmitPair_closed _ _ KT2_tagCode_ruleTrans_closed RecsSnd_closed

  emit_Df_E1_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_Df_E1) emit_Df_E1
  emit_Df_E1_closed =
    EmitPair_closed _ _ KT2_tagCode_axRecNd_closed
      (EmitPair_closed _ _ KT2_zT_closed
        (EmitPair_closed _ _ KT2_sT_closed
          (EmitPair_closed _ _ emit_cv1_closed emit_cv2_closed)))

  emit_Df_E_v1_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_Df_E_v1) emit_Df_E_v1
  emit_Df_E_v1_closed =
    EmitPair_closed _ _ KT2_tagCode_congL_closed
      (EmitPair_closed _ _ KT2_pCT_closed
        (EmitPair_closed _ _ emit_ih_v1_Df_closed
          (emit_mkAp1Tcf_closed emit_cv2 emit_cv2_closed)))

  emit_Df_E_v1_lifted_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_Df_E_v1_lifted) emit_Df_E_v1_lifted
  emit_Df_E_v1_lifted_closed =
    EmitPair_closed _ _ KT2_tagCode_congR_closed
      (EmitPair_closed _ _ KT2_sT_closed
        (EmitPair_closed _ _ emit_Df_E_v1_closed emit_X_closed))

  emit_Df_chain1_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_Df_chain1) emit_Df_chain1
  emit_Df_chain1_closed =
    EmitPair_closed _ _ KT2_tagCode_ruleTrans_closed
      (EmitPair_closed _ _ emit_Df_E1_closed emit_Df_E_v1_lifted_closed)

  emit_Df_E_v2_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_Df_E_v2) emit_Df_E_v2
  emit_Df_E_v2_closed =
    EmitPair_closed _ _ KT2_tagCode_congR_closed
      (EmitPair_closed _ _ KT2_pCT_closed
        (EmitPair_closed _ _ emit_ih_v2_Df_closed emit_corRecV1_closed))

  emit_Df_E_v2_lifted_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r emit_Df_E_v2_lifted) emit_Df_E_v2_lifted
  emit_Df_E_v2_lifted_closed =
    EmitPair_closed _ _ KT2_tagCode_congR_closed
      (EmitPair_closed _ _ KT2_sT_closed
        (EmitPair_closed _ _ emit_Df_E_v2_closed emit_X_closed))

  step_inner_closed : (x : Nat) (r : Term) ->
    Eq (substF2 x r step_inner) step_inner
  step_inner_closed =
    EmitPair_closed _ _ emit_Df_chain1_closed emit_Df_E_v2_lifted_closed

  -- Df_F1_Rec_zs_closed via 3 closures: tagCode_ruleTrans, lf_inner, step_inner.
  Df_F1_Rec_zs_closed_proven : (x : Nat) (r : Term) ->
    Eq (substF1 x r Df_F1_Rec_zs) Df_F1_Rec_zs
  Df_F1_Rec_zs_closed_proven x r =
    eqCong3 (\ tk lf si -> Comp2 Pair (KT tk)(Rec lf si))
      (tagCode_ruleTrans_closed x r)
      (lf_inner_closed x r)
      (step_inner_closed x r)

  ----------------------------------------------------------------------
  -- WithClosure submodule: takes the closure proof as parameter, then
  -- delivers Steps D-final, E, F, G, H using it.

  ----------------------------------------------------------------------
  -- Df_chain12_at v1 v2 : the Term returned by RecPairCase.thm12_Rec_zs_pair
  -- when instantiated with v1T = var v1, v2T = var v2, and IH1Rec.Df = ap1
  -- Df_F1_Rec_zs (var v_i).  Computed by manually expanding RecPairCase's
  -- chain construction (see BRA.Th12Rec.Th12RecCase.RecPairCase).

  Df_chain12_at : (v1 v2 : Nat) -> Term
  Df_chain12_at v1 v2 =
    let cv1 = ap1 cor (var v1)
        cv2 = ap1 cor (var v2)
        rec_v1 = ap1 recF (var v1)
        X' = ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cv1 cv2))
        Df_E1 = ap2 Pair tagCode_axRecNd
                  (ap2 Pair zT (ap2 Pair sT (ap2 Pair cv1 cv2)))
        Df_E_v1 = ap2 Pair tagCode_congL
                    (ap2 Pair pCT (ap2 Pair (wrapped_inner_Rec (var v1))
                                            (mkAp1T cf cv2)))
        Df_E_v1_lifted = ap2 Pair tagCode_congR
                            (ap2 Pair sT (ap2 Pair Df_E_v1 X'))
        Df_chain1 = ap2 Pair tagCode_ruleTrans
                      (ap2 Pair Df_E1 Df_E_v1_lifted)
        Df_E_v2 = ap2 Pair tagCode_congR
                    (ap2 Pair pCT (ap2 Pair (wrapped_inner_Rec (var v2))
                                            (ap1 cor rec_v1)))
        Df_E_v2_lifted = ap2 Pair tagCode_congR
                            (ap2 Pair sT (ap2 Pair Df_E_v2 X'))
    in ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1 Df_E_v2_lifted)

  -- Df_F1_Rec_zs_at_Pair_proven: identical content to Df_F1_Rec_zs_at_Pair_explicit,
  -- but RHS expressed via Df_chain12_at (definitionally equal forms).
  Df_F1_Rec_zs_at_Pair_proven : (v1 v2 : Nat) ->
    Deriv (atomic (eqn (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2)))
                       (Df_chain12_at v1 v2)))
  Df_F1_Rec_zs_at_Pair_proven = Df_F1_Rec_zs_at_Pair_explicit

  module WithClosure
    -- Theorem 12 for s in BRA-Deriv form (NOT encoded form).
    -- This is the ONLY remaining parameter at WithClosure level: depends
    -- on s (caller-supplied Fun2). For specific s, dischargeable from
    -- BRA's defining axioms.
    (ih_s_bra : (a b : Term) ->
       Deriv (atomic (eqn (mkAp2T sT (ap1 cor a) (ap1 cor b))
                          (ap1 cor (ap2 s a b)))))
    where

    -- Df_F1_Rec_zs_closed and Df_F1_Rec_zs_at_Pair are proved internally
    -- and used by the rest of WithClosure.
    Df_F1_Rec_zs_closed : (x : Nat) (r : Term) ->
                          Eq (substF1 x r Df_F1_Rec_zs) Df_F1_Rec_zs
    Df_F1_Rec_zs_closed = Df_F1_Rec_zs_closed_proven

    Df_F1_Rec_zs_at_Pair : (v1 v2 : Nat) ->
      Deriv (atomic (eqn (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2)))
                         (Df_chain12_at v1 v2)))
    Df_F1_Rec_zs_at_Pair = Df_F1_Rec_zs_at_Pair_proven

    --------------------------------------------------------------------
    -- Step D-final: Th12_at_lf_substF : Deriv (substF zero O P_Th12_Rec_zs).
    --
    -- Strategy: bridge Th12_at_lf_concrete via eqSubst at multiple
    -- positions, using thClosed / Df_F1_Rec_zs_closed / recF_closed /
    -- cor_closed_eq / cf_closed and similar Eq lemmas.
    --
    -- substF zero O P_Th12_Rec_zs reduces (Agda definitional, outside
    -- abstract block) to:
    --   atomic (eqn (ap1 thmT (ap1 (substF1 zero O Df_F1_Rec_zs) O))
    --               (subst zero O (codeFTeq1Asym recF (var zero))))
    -- (using thClosed = refl for the thmT slot).
    --
    -- We bridge via eqSubst on each "stuck" position.

    -- subst zero O (codeFTeq1Asym recF (var zero)) = codeFTeq1Asym recF O
    -- by structural cong using cf_closed, cor_closed_eq, recF_closed.
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

    Th12_at_lf_substF : Deriv (substF zero O P_Th12_Rec_zs)
    Th12_at_lf_substF =
      eqSubst (\ thT' -> Deriv (atomic (eqn
          (ap1 thT' (ap1 (substF1 zero O Df_F1_Rec_zs) O))
          (subst zero O (codeFTeq1Asym recF (var zero))))))
        (eqSym (thClosed zero O))
        (eqSubst (\ Df' -> Deriv (atomic (eqn
            (ap1 thmT (ap1 Df' O))
            (subst zero O (codeFTeq1Asym recF (var zero))))))
          (eqSym (Df_F1_Rec_zs_closed zero O))
          (eqSubst (\ rhs -> Deriv (atomic (eqn
              (ap1 thmT (ap1 Df_F1_Rec_zs O)) rhs)))
            (eqSym codeFTeq1Asym_subst_eq_O)
            Th12_at_lf_concrete))

    --------------------------------------------------------------------
    -- Step E: toIH1Rec packaging.
    --
    -- Given an IH-Deriv at var v (= a substF-form Deriv from ruleIndBT's
    -- step hypothesis), package it as an IH1Rec recF (var v) record.
    -- Uses shape_at (Step C) for the shape field and eqSubst chain
    -- (similar to Step D-final) for the image field.

    -- Eq lemma: subst zero (var v) (codeFTeq1Asym recF (var zero))
    --         = codeFTeq1Asym recF (var v).
    codeFTeq1Asym_subst_eq_var : (v : Nat) ->
      Eq (subst zero (var v) (codeFTeq1Asym recF (var zero)))
         (codeFTeq1Asym recF (var v))
    codeFTeq1Asym_subst_eq_var v =
      eqCong3 (\ cf' cor' recF' -> ap2 Pair
        (ap2 Pair (reify tagAp1)(ap2 Pair cf' (ap1 cor' (var v))))
        (ap1 cor' (ap1 recF' (var v))))
        (cf_closed zero (var v))
        (cor_closed_eq zero (var v))
        (recF_closed zero (var v))

    open BRA.Th12Rec using (IH1Rec)

    toIH1Rec : (v : Nat) ->
      Deriv (substF zero (var v) P_Th12_Rec_zs) ->
      IH1Rec recF (var v)
    toIH1Rec v ihD =
      record
        { Df    = wrapped_inner_Rec (var v)
        ; fstL  = _
        ; fstR  = _
        ; shape = axFst tagCode_ruleTrans (ap1 inner_Rec (var v))
        ; image = image_proof
        }
      where
        image_at_Df : Deriv (atomic (eqn
                       (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))
                       (codeFTeq1Asym recF (var v))))
        image_at_Df =
          eqSubst (\ rhs -> Deriv (atomic (eqn
              (ap1 thmT (ap1 Df_F1_Rec_zs (var v))) rhs)))
            (codeFTeq1Asym_subst_eq_var v)
            (eqSubst (\ Df' -> Deriv (atomic (eqn
                (ap1 thmT (ap1 Df' (var v)))
                (subst zero (var v) (codeFTeq1Asym recF (var zero))))))
              (Df_F1_Rec_zs_closed zero (var v))
              (eqSubst (\ thT' -> Deriv (atomic (eqn
                  (ap1 thT' (ap1 (substF1 zero (var v) Df_F1_Rec_zs)(var v)))
                  (subst zero (var v) (codeFTeq1Asym recF (var zero))))))
                (thClosed zero (var v))
                ihD))

        image_proof : Deriv (atomic (eqn
                       (ap1 thmT (wrapped_inner_Rec (var v)))
                       (codeFTeq1Asym recF (var v))))
        image_proof =
          ruleTrans (cong1 thmT (ruleSym (Df_F1_Rec_zs_reduce_outer (var v))))
                    image_at_Df

    --------------------------------------------------------------------
    -- Step F: basePair Agda function.
    --
    -- Given two IH-Derivs at var v1, var v2, build Deriv (substF zero
    -- (Pair (var v1)(var v2)) P_Th12_Rec_zs).
    --
    -- Strategy:
    --   1. Use toIH1Rec to package each IH-Deriv as IH1Rec record.
    --   2. Apply RecPairCase to get the Sigma chain proof.
    --   3. Use Df_F1_Rec_zs_at_Pair to bridge ap1 Df_F1_Rec_zs (Pair v1 v2)
    --      = Df_chain12_at v1 v2 (= the Sigma's first projection).
    --   4. cong1 thmT + ruleTrans to derive
    --      Deriv (eqn (thmT (ap1 Df_F1_Rec_zs (Pair v1 v2)))(codeFTeq1Asym recF (Pair v1 v2))).
    --   5. eqSubst chain (analog of Step D-final) to bridge to substF form.

    -- Eq lemma: subst zero (Pair (var v1)(var v2)) (codeFTeq1Asym recF (var zero))
    --         = codeFTeq1Asym recF (Pair (var v1)(var v2)).
    codeFTeq1Asym_subst_eq_Pair : (v1 v2 : Nat) ->
      Eq (subst zero (ap2 Pair (var v1) (var v2)) (codeFTeq1Asym recF (var zero)))
         (codeFTeq1Asym recF (ap2 Pair (var v1) (var v2)))
    codeFTeq1Asym_subst_eq_Pair v1 v2 =
      eqCong3 (\ cf' cor' recF' -> ap2 Pair
        (ap2 Pair (reify tagAp1)(ap2 Pair cf' (ap1 cor' (ap2 Pair (var v1)(var v2)))))
        (ap1 cor' (ap1 recF' (ap2 Pair (var v1)(var v2)))))
        (cf_closed zero (ap2 Pair (var v1)(var v2)))
        (cor_closed_eq zero (ap2 Pair (var v1)(var v2)))
        (recF_closed zero (ap2 Pair (var v1)(var v2)))

    basePair : (v1 v2 : Nat) ->
               Deriv (substF zero (var v1) P_Th12_Rec_zs) ->
               Deriv (substF zero (var v2) P_Th12_Rec_zs) ->
               Deriv (substF zero (ap2 Pair (var v1) (var v2)) P_Th12_Rec_zs)
    --------------------------------------------------------------------
    -- Step G0: liftAxiom — lift a non-IH-dependent Deriv to implication form.
    --
    --   liftAxiom (P : Formula) (Q : Formula) (D : Deriv Q)
    --     : Deriv (P imp Q)
    --   = mp (axK Q P) D.

    liftAxiom : (P : Formula) {Q : Formula} -> Deriv Q -> Deriv (P imp Q)
    liftAxiom P D = mp (axK _ P) D

    --------------------------------------------------------------------
    -- Step G1: B_combinator — lifted mp.
    --
    --   B_combinator : Deriv (P imp (Q imp R)) -> Deriv (P imp Q)
    --                  -> Deriv (P imp R)
    --
    -- Construction: from D1 : P imp (Q imp R) and D2 : P imp Q,
    --   axS P Q R : (P imp (Q imp R)) imp ((P imp Q) imp (P imp R))
    --   mp axS D1 : (P imp Q) imp (P imp R)
    --   mp ... D2 : P imp R.

    B_combinator : {P Q R : Formula} ->
                   Deriv (P imp (Q imp R)) ->
                   Deriv (P imp Q) ->
                   Deriv (P imp R)
    B_combinator {P} {Q} {R} D1 D2 = mp (mp (axS P Q R) D1) D2

    --------------------------------------------------------------------
    -- Step G2: lifted equational rules.
    --
    --   liftedRuleTrans : Deriv (P imp atomic (eqn a b))
    --                  -> Deriv (P imp atomic (eqn a c))
    --                  -> Deriv (P imp atomic (eqn b c))
    -- (Note: signature uses BRA's axEqTrans which is "from a=b and a=c
    -- conclude b=c", not the standard "from a=b and b=c conclude a=c".)
    --
    -- Proper liftedRuleTrans (a=b, b=c -> a=c) constructed via ruleSym.
    --
    -- liftedCong1 : (f : Fun1) -> Deriv (P imp atomic (eqn a b))
    --              -> Deriv (P imp atomic (eqn (ap1 f a)(ap1 f b)))
    -- via axEqCong1 + B_combinator.

    liftedAxEqTrans : (P : Formula) (a b c : Term) ->
                      Deriv (P imp atomic (eqn a b)) ->
                      Deriv (P imp atomic (eqn a c)) ->
                      Deriv (P imp atomic (eqn b c))
    liftedAxEqTrans P a b c D1 D2 =
      B_combinator (B_combinator (liftAxiom P (axEqTrans a b c)) D1) D2

    -- liftedRuleSym : from P imp (a=b), produce P imp (b=a).
    -- Uses axEqTrans a b a + axRefl a.
    liftedRuleSym : (P : Formula) (a b : Term) ->
                    Deriv (P imp atomic (eqn a b)) ->
                    Deriv (P imp atomic (eqn b a))
    liftedRuleSym P a b D =
      liftedAxEqTrans P a b a D (liftAxiom P (axRefl a))

    -- liftedRuleTrans : from P imp (a=b) and P imp (b=c), produce P imp (a=c).
    -- Uses liftedRuleSym + liftedAxEqTrans.
    liftedRuleTrans : (P : Formula) (a b c : Term) ->
                      Deriv (P imp atomic (eqn a b)) ->
                      Deriv (P imp atomic (eqn b c)) ->
                      Deriv (P imp atomic (eqn a c))
    liftedRuleTrans P a b c D1 D2 =
      liftedAxEqTrans P b a c (liftedRuleSym P a b D1) D2

    liftedCong1 : (P : Formula) (f : Fun1) (a b : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn (ap1 f a) (ap1 f b)))
    liftedCong1 P f a b D =
      B_combinator (liftAxiom P (axEqCong1 f a b)) D

    liftedCongL : (P : Formula) (g : Fun2) (a b c : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn (ap2 g a c) (ap2 g b c)))
    liftedCongL P g a b c D =
      B_combinator (liftAxiom P (axEqCongL g a b c)) D

    liftedCongR : (P : Formula) (g : Fun2) (a b c : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn (ap2 g c a) (ap2 g c b)))
    liftedCongR P g a b c D =
      B_combinator (liftAxiom P (axEqCongR g a b c)) D

    --------------------------------------------------------------------
    -- Step G3: liftedEqSubst — Agda-level eqSubst on the implication type.
    --
    -- Trivial: from D : Deriv (P imp Property x) and Eq x y,
    -- produce Deriv (P imp Property y) via Agda's eqSubst.

    liftedEqSubst : {A : Set} (P : Formula) (Property : A -> Formula)
                    {x y : A} -> Eq x y ->
                    Deriv (P imp Property x) ->
                    Deriv (P imp Property y)
    liftedEqSubst P Property eq D =
      eqSubst (\ z -> Deriv (P imp Property z)) eq D

    --------------------------------------------------------------------
    -- Step G4: toIH1Rec_lifted.
    --
    -- Lifted version of toIH1Rec: takes a Deriv (P imp substF...) and
    -- produces a lifted IH1Rec record where .image field is in the
    -- implication form Deriv (P imp eqn ...).
    --
    -- The .Df/.fstL/.fstR/.shape fields are constant (don't depend on
    -- the IH-Deriv), so they're identical to toIH1Rec's.

    record IH1Rec_lifted (P : Formula) (f : Fun1) (x : Term) : Set where
      field
        Df    : Term
        fstL  : Term
        fstR  : Term
        shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
        image : Deriv (P imp atomic (eqn (ap1 thmT Df) (codeFTeq1Asym f x)))

    -- Lifted image: 3 nested liftedEqSubst mirroring toIH1Rec's image_proof.
    toIH1Rec_lifted_image : (P : Formula) (v : Nat) ->
      Deriv (P imp substF zero (var v) P_Th12_Rec_zs) ->
      Deriv (P imp atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))
                                (codeFTeq1Asym recF (var v))))
    toIH1Rec_lifted_image P v lifted_ihD =
      liftedEqSubst P (\ rhs -> atomic (eqn
          (ap1 thmT (ap1 Df_F1_Rec_zs (var v))) rhs))
        (codeFTeq1Asym_subst_eq_var v)
        (liftedEqSubst P (\ Df' -> atomic (eqn
            (ap1 thmT (ap1 Df' (var v)))
            (subst zero (var v) (codeFTeq1Asym recF (var zero)))))
          (Df_F1_Rec_zs_closed zero (var v))
          (liftedEqSubst P (\ thT' -> atomic (eqn
              (ap1 thT' (ap1 (substF1 zero (var v) Df_F1_Rec_zs)(var v)))
              (subst zero (var v) (codeFTeq1Asym recF (var zero)))))
            (thClosed zero (var v))
            lifted_ihD))

    -- Bridge image_at_Df form to wrapped_inner_Rec form using
    -- B_combinator + liftAxiom + axEqCong1.

    toIH1Rec_lifted_image_wrapped : (P : Formula) (v : Nat) ->
      Deriv (P imp substF zero (var v) P_Th12_Rec_zs) ->
      Deriv (P imp atomic (eqn (ap1 thmT (wrapped_inner_Rec (var v)))
                                (codeFTeq1Asym recF (var v))))
    toIH1Rec_lifted_image_wrapped P v lifted_ihD =
      let
        -- (P imp eqn (thmT (Df_F1_Rec_zs (var v))) (codeFTeq1Asym recF (var v))).
        lifted_at_Df : Deriv (P imp atomic (eqn
                              (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))
                              (codeFTeq1Asym recF (var v))))
        lifted_at_Df = toIH1Rec_lifted_image P v lifted_ihD

        -- We need to bridge (thmT (Df_F1_Rec_zs (var v))) = (thmT (wrapped_inner_Rec (var v)))
        -- and apply ruleSym + liftedAxEqTrans.
        --
        -- First: liftAxiom of the BRA-Deriv  thmT (wrapped_inner_Rec (var v)) = thmT (Df_F1_Rec_zs (var v))
        -- via cong1 thmT (ruleSym (Df_F1_Rec_zs_reduce_outer (var v))).
        bridge_thmT : Deriv (atomic (eqn
                       (ap1 thmT (wrapped_inner_Rec (var v)))
                       (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))))
        bridge_thmT = cong1 thmT (ruleSym (Df_F1_Rec_zs_reduce_outer (var v)))

        lifted_bridge : Deriv (P imp atomic (eqn
                       (ap1 thmT (wrapped_inner_Rec (var v)))
                       (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))))
        lifted_bridge = liftAxiom P bridge_thmT
      in
        liftedRuleTrans P
          (ap1 thmT (wrapped_inner_Rec (var v)))
          (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))
          (codeFTeq1Asym recF (var v))
          lifted_bridge
          lifted_at_Df

    toIH1Rec_lifted : (P : Formula) (v : Nat) ->
                      Deriv (P imp substF zero (var v) P_Th12_Rec_zs) ->
                      IH1Rec_lifted P recF (var v)
    toIH1Rec_lifted P v lifted_ihD =
      record
        { Df    = wrapped_inner_Rec (var v)
        ; fstL  = _
        ; fstR  = _
        ; shape = axFst tagCode_ruleTrans (ap1 inner_Rec (var v))
        ; image = toIH1Rec_lifted_image_wrapped P v lifted_ihD
        }

    --------------------------------------------------------------------
    -- Step G5-G7 path: the lifted basePair is taken as a sub-module
    -- parameter.  Caller discharges via either:
    --   (a) Adding uniformity lemmas to ThmT.agda's abstract block for
    --       thmTDispCongL_param / CongR_param / RuleTrans_param, then
    --       composing via B_combinator + liftAxiom.
    --   (b) Re-deriving E_v1, E_v2, chain1, chain12 inline using the
    --       implication-form axioms (axEqCongL, axEqCongR, axEqTrans)
    --       + axS + axK + mp directly, bypassing the dispatchers.
    --
    -- The basePair_param signature is what ruleIndBT's step expects
    -- after substituting v1, v2 with concrete fresh vars.

    module WithBasePairParam
      (basePair_param : (v1 v2 : Nat) ->
         Deriv ((substF zero (var v1) P_Th12_Rec_zs) imp
                ((substF zero (var v2) P_Th12_Rec_zs) imp
                 (substF zero (ap2 Pair (var v1) (var v2)) P_Th12_Rec_zs))))
      where

      ------------------------------------------------------------------
      -- Step H: Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs via ruleIndBT.

      Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs
      Th12_F1_Rec_zs = ruleIndBT P_Th12_Rec_zs
                                  (suc (suc zero))
                                  (suc (suc (suc zero)))
                                  Th12_at_lf_substF
                                  (basePair_param (suc (suc zero))
                                                  (suc (suc (suc zero))))

    basePair v1 v2 ihD_v1 ihD_v2 =
      let
        ih1 : IH1Rec recF (var v1)
        ih1 = toIH1Rec v1 ihD_v1

        ih2 : IH1Rec recF (var v2)
        ih2 = toIH1Rec v2 ihD_v2

        -- Apply RecPairCase to get the Sigma chain proof.
        module RPC = BRA.Th12Rec.Th12RecCase.RecPairCase z s z_corLemma
                       (var v1) (var v2) ih1 ih2 ih_s_bra

        -- The Sigma's image: thmT (Df_chain12) = codeFTeq1Asym recF (Pair v1 v2).
        sigma_image : Deriv (atomic (eqn (ap1 thmT (Df_chain12_at v1 v2))
                                          (codeFTeq1Asym recF (ap2 Pair (var v1) (var v2)))))
        sigma_image = snd RPC.thm12_Rec_zs_pair

        -- Bridge: ap1 Df_F1_Rec_zs (Pair v1 v2) =BRA Df_chain12_at v1 v2.
        bridge_at_Pair : Deriv (atomic (eqn (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2)))
                                             (Df_chain12_at v1 v2)))
        bridge_at_Pair = Df_F1_Rec_zs_at_Pair v1 v2

        -- cong1 thmT to lift bridge.
        bridge_thmT : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2))))
                                          (ap1 thmT (Df_chain12_at v1 v2))))
        bridge_thmT = cong1 thmT bridge_at_Pair

        -- Compose: thmT (Df_F1_Rec_zs (Pair v1 v2)) = codeFTeq1Asym recF (Pair v1 v2).
        concrete : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2))))
                                       (codeFTeq1Asym recF (ap2 Pair (var v1) (var v2)))))
        concrete = ruleTrans bridge_thmT sigma_image
      in
        -- Bridge concrete to substF form via 3-layer eqSubst chain.
        eqSubst (\ thT' -> Deriv (atomic (eqn
            (ap1 thT' (ap1 (substF1 zero (ap2 Pair (var v1) (var v2)) Df_F1_Rec_zs)
                            (ap2 Pair (var v1) (var v2))))
            (subst zero (ap2 Pair (var v1) (var v2)) (codeFTeq1Asym recF (var zero))))))
          (eqSym (thClosed zero (ap2 Pair (var v1) (var v2))))
          (eqSubst (\ Df' -> Deriv (atomic (eqn
              (ap1 thmT (ap1 Df' (ap2 Pair (var v1) (var v2))))
              (subst zero (ap2 Pair (var v1) (var v2)) (codeFTeq1Asym recF (var zero))))))
            (eqSym (Df_F1_Rec_zs_closed zero (ap2 Pair (var v1) (var v2))))
            (eqSubst (\ rhs -> Deriv (atomic (eqn
                (ap1 thmT (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2)))) rhs)))
              (eqSym (codeFTeq1Asym_subst_eq_Pair v1 v2))
              concrete))

  ----------------------------------------------------------------------
  -- Steps E, F, G, H to follow.  Steps B-H to follow:
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
