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
  -- Steps A, B1, C, D-partial complete.
  --
  -- Step D2 (~30 LoC): discharge the two structural Eq lemmas
  --   Df_F1_Rec_zs_closed : (r : Term) -> Eq (substF1 zero r Df_F1_Rec_zs) Df_F1_Rec_zs
  --   recF_closed : (r : Term) -> Eq (substF1 zero r recF) recF
  -- by structural induction using z_closed + s_closed + reifyClosed for
  -- the various reify-of-natCode terms.
  --
  -- These let us bridge  Th12_at_lf_concrete  to  Deriv (substF zero O P_Th12_Rec_zs)
  -- via eqSubst, completing Step D.
  --
  -- Subsequent steps E, F, G, H follow as outlined.  Steps B-H to follow:
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
