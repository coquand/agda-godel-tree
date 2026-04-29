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
  -- (closed via recF_closed).  Most positions reduce to refl; the
  -- recF-containing position needs explicit cong.
  --
  -- Rather than a deep cascade of eqCong's, we make step_inner_closed a
  -- module sub-parameter via WithClosure (below).  For typical concrete
  -- (closed z, s) instances, the caller discharges as `\ _ _ -> refl`.

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
                    (ap2 Pair pCT (ap2 Pair (ap1 Df_F1_Rec_zs (var v1))
                                            (mkAp1T cf cv2)))
        Df_E_v1_lifted = ap2 Pair tagCode_congR
                            (ap2 Pair sT (ap2 Pair Df_E_v1 X'))
        Df_chain1 = ap2 Pair tagCode_ruleTrans
                      (ap2 Pair Df_E1 Df_E_v1_lifted)
        Df_E_v2 = ap2 Pair tagCode_congR
                    (ap2 Pair pCT (ap2 Pair (ap1 Df_F1_Rec_zs (var v2))
                                            (ap1 cor rec_v1)))
        Df_E_v2_lifted = ap2 Pair tagCode_congR
                            (ap2 Pair sT (ap2 Pair Df_E_v2 X'))
    in ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1 Df_E_v2_lifted)

  module WithClosure
    (Df_F1_Rec_zs_closed :
       (x : Nat) (r : Term) ->
       Eq (substF1 x r Df_F1_Rec_zs) Df_F1_Rec_zs)
    -- Theorem 12 for s in BRA-Deriv form (NOT encoded form).
    (ih_s_bra : (a b : Term) ->
       Deriv (atomic (eqn (mkAp2T sT (ap1 cor a) (ap1 cor b))
                          (ap1 cor (ap2 s a b)))))
    -- Step B2 (mechanical, ~150-200 LoC): BRA-equality bridging
    -- ap1 Df_F1_Rec_zs (Pair v1 v2) to Df_chain12_at v1 v2.
    (Df_F1_Rec_zs_at_Pair : (v1 v2 : Nat) ->
       Deriv (atomic (eqn (ap1 Df_F1_Rec_zs (ap2 Pair (var v1) (var v2)))
                          (Df_chain12_at v1 v2))))
    where

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
        { Df    = ap1 Df_F1_Rec_zs (var v)
        ; fstL  = _
        ; fstR  = _
        ; shape = shape_at (var v)
        ; image = image_proof
        }
      where
        -- ihD has type substF zero (var v) P_Th12_Rec_zs, which Agda reduces to:
        --   atomic (eqn (ap1 (substF1 zero (var v) thmT)
        --                    (ap1 (substF1 zero (var v) Df_F1_Rec_zs)(var v)))
        --               (subst zero (var v) (codeFTeq1Asym recF (var zero))))
        -- Bridge to (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))(codeFTeq1Asym recF (var v)))
        -- via the same 3-layer eqSubst chain as Step D-final.
        image_proof : Deriv (atomic (eqn
                       (ap1 thmT (ap1 Df_F1_Rec_zs (var v)))
                       (codeFTeq1Asym recF (var v))))
        image_proof =
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
