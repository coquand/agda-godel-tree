{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Th12TreeRecInternal -- internalised treeRec D2 builder.
--
-- Replaces the FromBridges parameters  D2_treeRec_NN_fun  and
-- D_correct2_treeRec_NN_pt  by an *internal* construction parametric
-- only on the IH-on-f and IH-on-s (from thm12_F1 f / thm12_F2 s).
--
-- Architecture (mirrors BRA/Th12RecPUniv.agda but for arbitrary f):
--
--   D2_treeRec_fs : Fun2  =  treeRec lf_emitter step_emitter
--
-- where:
--   * lf_emitter : Fun1 emits the leaf chain Df (uses Df_f).
--   * step_emitter : Fun2 emits the Pair-case chain Df at runtime.
--     The recursive Df-slots are supplied automatically by treeRec's
--     evaluation: at (orig = Pair p (Pair v1 v2), recs = Pair r1 r2),
--     r1 / r2 are exactly  ap2 D2_treeRec_fs p v1  and
--     ap2 D2_treeRec_fs p v2  (cross-IH-shaped).
--
-- This file delivers:
--   * D2_treeRec_fs : Fun2 (closed in (f, s, Df_f, Df_s)).
--   * Df_F2_treeRec_fs_at_O : leaf reduction.
--   * D_correct2_treeRec_fs_O : (p : Term) -> Deriv ... (leaf correctness).
--
-- Pair-case correctness proof (universal closure via ruleIndBT) is
-- under construction; see BRA/NEXT-SESSION-TREEREC-NN-INTERNAL.md.

module BRA2.Th12TreeRecInternal where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.SubstClosure using (Fun1_closed ; Fun2_closed ; subst_reify)
open import BRA2.Thm.Tag using (tagAxTreeRecLf ; tagAxTreeRecNd ; tagRuleTrans
                              ; tagCongL ; tagCongR)
open import BRA2.Thm.ThmT using (thmT
                               ; tagCode_axTreeRecLf ; tagCode_axTreeRecNd
                               ; tagCode_ruleTrans
                               ; tagCode_congL ; tagCode_congR
                               ; thClosed
                               ; thmTDispRuleTrans_param_doublelifted
                               ; thmTDispCongL_param_doublelifted
                               ; thmTDispCongR_param_doublelifted)
open import BRA2.Thm12.Param.AxTreeRecLf
  using (parEncAxTreeRecLf ; parOutAxTreeRecLf ; parDispAxTreeRecLf)
open import BRA2.Thm12.Param.AxTreeRecNd
  using (parEncAxTreeRecNd ; parOutAxTreeRecNd ; parDispAxTreeRecNd)
open import BRA2.Thm12.Param.RuleTrans
  using (parEncRuleTrans ; parDispRuleTrans)
open import BRA2.Thm12.Param.CongR
  using (parEncCongR ; parOutCongR ; parDispCongR)
open import BRA2.Thm12.Param.CongL
  using (parEncCongL ; parOutCongL ; parDispCongL)
open import BRA2.Thm.EvalHelpers using
  ( liftAxiom ; B_combinator ; liftedRuleTrans ; liftedCong1
  ; liftedCongL ; liftedCongR
  ; liftAxiomTwo ; B_combinatorTwo ; liftedRuleTransTwo
  ; liftedCong1Two ; liftedCongLTwo ; liftedCongRTwo )
open import BRA2.CorOfPair using (corOfPair)

------------------------------------------------------------------------
-- The codeFTeq2 spec: encoded equation for treeRec f s at (p, x).

codeFTeq2_treeRec_fs : (f : Fun1) (s : Fun2) -> Term -> Term -> Term
codeFTeq2_treeRec_fs f s p x =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 (treeRec f s)))
                        (ap2 Pair (ap1 cor p) (ap1 cor x))))
    (ap1 cor (ap2 (treeRec f s) p x))

------------------------------------------------------------------------
-- Generic codeFTeq2 for any Fun2 g (used by IH-on-s).

codeFTeq2_gen : (g : Fun2) -> Term -> Term -> Term
codeFTeq2_gen g X V =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 g))
                        (ap2 Pair (ap1 cor X) (ap1 cor V))))
    (ap1 cor (ap2 g X V))

------------------------------------------------------------------------
-- The codeFTeq1 spec for IH-on-f.

codeFTeq1_for : (f : Fun1) -> Term -> Term
codeFTeq1_for f q =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 f)) (ap1 cor q)))
    (ap1 cor (ap1 f q))

------------------------------------------------------------------------
-- Construction module.

module Construction
  (f : Fun1) (s : Fun2)
  (Df_f : Fun1)
  (proof_f : (q : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap1 Df_f q)) (codeFTeq1_for f q))))
  (Df_s : Fun2)
  (proof_s : (X V : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Df_s X V)) (codeFTeq2_gen s X V))))
  where

  ----------------------------------------------------------------------
  -- Encoded forms (closed).

  fT : Term
  fT = reify (codeF1 f)

  sT : Term
  sT = reify (codeF2 s)

  cf2_TR : Term
  cf2_TR = reify (codeF2 (treeRec f s))

  ----------------------------------------------------------------------
  -- Step A: lf_emitter : Fun1.
  --
  -- Want:
  --   ap1 lf_emitter p
  --     =BRA parEncRuleTrans (parEncAxTreeRecLf fT sT (cor p)) (ap1 Df_f p)
  --     =    Pair tagCode_ruleTrans
  --             (Pair (parEncAxTreeRecLf fT sT (cor p))
  --                   (ap1 Df_f p))
  --     =    Pair tagCode_ruleTrans
  --             (Pair
  --               (Pair tagCode_axTreeRecLf
  --                     (Pair fT (Pair sT (cor p))))
  --               (ap1 Df_f p))

  -- ap1 (KT (reify v)) p = reify v.

  -- Encoding building blocks (Fun1, since we apply at p only):
  --   Df_f as Fun1 itself                          -- inner second arg
  --   Comp cor I = "lambda p . cor p"              -- emits cor p
  --   KT (reify v) = constant emitter

  -- inner_payload p = Pair sT (cor p)
  inner_payload : Fun1
  inner_payload = Comp2 Pair (KT sT) cor

  -- f_treeRec_payload p = Pair fT (Pair sT (cor p))
  f_treeRec_payload : Fun1
  f_treeRec_payload = Comp2 Pair (KT fT) inner_payload

  -- f_treeRec_part p = parEncAxTreeRecLf fT sT (cor p)
  --                  = Pair tagCode_axTreeRecLf (Pair fT (Pair sT (cor p)))
  f_treeRec_part : Fun1
  f_treeRec_part = Comp2 Pair (KT tagCode_axTreeRecLf) f_treeRec_payload

  -- inner_chain_pair p = Pair (parEncAxTreeRecLf fT sT (cor p)) (ap1 Df_f p)
  inner_chain_pair : Fun1
  inner_chain_pair = Comp2 Pair f_treeRec_part Df_f

  -- lf_emitter p = parEncRuleTrans (parEncAxTreeRecLf fT sT (cor p)) (Df_f p)
  lf_emitter : Fun1
  lf_emitter = Comp2 Pair (KT tagCode_ruleTrans) inner_chain_pair

  ----------------------------------------------------------------------
  -- Step B: step_emitter : Fun2.
  --
  -- step_emitter is invoked by treeRec at runtime when input is Pair-shaped:
  --   ap2 step_emitter (Pair p (Pair v1 v2)) (Pair r1 r2)
  -- where r1 = ap2 D2_treeRec_fs p v1 and r2 = ap2 D2_treeRec_fs p v2
  -- (cross-IH-shaped Df slots).
  --
  -- We want it to emit the chain Df:
  --
  --   parEncRuleTrans
  --     (parEncAxTreeRecNd fT sT (cor p) (cor v1) (cor v2))
  --     (parEncRuleTrans
  --        (parEncCongR s (lifted-cross-IH-bridge for v1) X1)
  --        (parEncRuleTrans
  --           (parEncCongR s (lifted-cross-IH-bridge for v2) X2)
  --           (Df_s applied at full (X, V))))
  --
  -- Concrete construction is deferred — see Pair-case correctness proof
  -- (under construction).  For now, emit a placeholder using primitives
  -- already in scope; the body will be filled in once the chain is
  -- finalised.

  ----------------------------------------------------------------------
  -- Encoded constants we'll reference (cf2_Pair etc.)

  cf2_Pair : Term
  cf2_Pair = reify (codeF2 Pair)

  ----------------------------------------------------------------------
  -- emit_* combinators for step_emitter.
  --
  -- Convention: at runtime, orig = Pair p (Pair v1 v2) and recs = Pair r1 r2.
  -- Each emit_K : Fun2 such that ap2 emit_K orig recs = (specified piece).

  -- Generic: lift a Fun1 expression of `orig` through Lift.
  -- ap2 (Lift f) orig recs = ap1 f orig.

  -- Projectors as Fun1's (consumed by Lift below).
  Fst1 : Fun1
  Fst1 = Fst

  v1Fun1 : Fun1
  v1Fun1 = Comp Fst Snd

  v2Fun1 : Fun1
  v2Fun1 = Comp Snd Snd

  cor_p_F : Fun1
  cor_p_F = Comp cor Fst1

  cor_v1_F : Fun1
  cor_v1_F = Comp cor v1Fun1

  cor_v2_F : Fun1
  cor_v2_F = Comp cor v2Fun1

  -- treeRec-applied builders: ap2 (treeRec f s) p v_i = ap1 (treeRec_p_v_i_F) orig.
  treeRec_p_v1_F : Fun1
  treeRec_p_v1_F = Comp2 (treeRec f s) Fst1 v1Fun1                              -- treeRec f s p v1

  treeRec_p_v2_F : Fun1
  treeRec_p_v2_F = Comp2 (treeRec f s) Fst1 v2Fun1                              -- treeRec f s p v2

  cor_TR_p_v1_F : Fun1                                                          -- cor (treeRec p v1)
  cor_TR_p_v1_F = Comp cor treeRec_p_v1_F

  cor_TR_p_v2_F : Fun1
  cor_TR_p_v2_F = Comp cor treeRec_p_v2_F

  -- Lift to Fun2 (so ap2 takes (orig, recs)).
  emit_orig : Fun2
  emit_orig = Lift I

  emit_p : Fun2
  emit_p = Lift Fst1

  emit_v1 : Fun2
  emit_v1 = Lift v1Fun1

  emit_v2 : Fun2
  emit_v2 = Lift v2Fun1

  emit_cor_p : Fun2
  emit_cor_p = Lift cor_p_F

  emit_cor_v1 : Fun2
  emit_cor_v1 = Lift cor_v1_F

  emit_cor_v2 : Fun2
  emit_cor_v2 = Lift cor_v2_F

  emit_TR_p_v1 : Fun2
  emit_TR_p_v1 = Lift treeRec_p_v1_F

  emit_TR_p_v2 : Fun2
  emit_TR_p_v2 = Lift treeRec_p_v2_F

  emit_cor_TR_p_v1 : Fun2
  emit_cor_TR_p_v1 = Lift cor_TR_p_v1_F

  emit_cor_TR_p_v2 : Fun2
  emit_cor_TR_p_v2 = Lift cor_TR_p_v2_F

  -- recs projectors.
  emit_r1 : Fun2
  emit_r1 = Post Fst (Post Snd Pair)

  emit_r2 : Fun2
  emit_r2 = Post Snd (Post Snd Pair)

  -- Constant emitters (lift KT through Lift).
  KT2 : Term -> Fun2
  KT2 t = Lift (KT t)

  ----------------------------------------------------------------------
  -- Composite emitters using Fan-of-Pair to build encoded sub-terms.
  --
  -- EmitPair ha hb = Fan ha hb Pair gives: ap2 (EmitPair ha hb) o r = Pair (ap2 ha o r)(ap2 hb o r).

  EmitPair : Fun2 -> Fun2 -> Fun2
  EmitPair ha hb = Fan ha hb Pair

  -- mkAp2T cf2 a b = Pair (reify tagAp2)(Pair cf2 (Pair a b)) — emit at runtime.
  emit_mkAp2T_cf2_Pair_corv1_corv2 : Fun2
  emit_mkAp2T_cf2_Pair_corv1_corv2 =
    EmitPair (KT2 (reify tagAp2))
             (EmitPair (KT2 cf2_Pair)
                       (EmitPair emit_cor_v1 emit_cor_v2))

  -- enc_TR_v1 = mkAp2T cf2_TR (cor p)(cor v1).
  emit_enc_TR_v1 : Fun2
  emit_enc_TR_v1 =
    EmitPair (KT2 (reify tagAp2))
             (EmitPair (KT2 cf2_TR)
                       (EmitPair emit_cor_p emit_cor_v1))

  emit_enc_TR_v2 : Fun2
  emit_enc_TR_v2 =
    EmitPair (KT2 (reify tagAp2))
             (EmitPair (KT2 cf2_TR)
                       (EmitPair emit_cor_p emit_cor_v2))

  -- enc_X = mkAp2T cf2_Pair (cor p)(mkAp2T cf2_Pair (cor v1)(cor v2)).
  emit_enc_X : Fun2
  emit_enc_X =
    EmitPair (KT2 (reify tagAp2))
             (EmitPair (KT2 cf2_Pair)
                       (EmitPair emit_cor_p emit_mkAp2T_cf2_Pair_corv1_corv2))

  ----------------------------------------------------------------------
  -- Step 1 of chain: parEncCongL Pair r1 enc_TR_v2.
  --   = Pair tagCode_congL (Pair (Pair cf2_Pair enc_TR_v2) r1)
  -- This lifts (enc_TR_v1, cor(treeRec p v1)) to
  --   (mkAp2T cf2_Pair enc_TR_v1 enc_TR_v2, mkAp2T cf2_Pair (cor(treeRec p v1)) enc_TR_v2)

  emit_parEncCongL_Pair_r1_enc_TR_v2 : Fun2
  emit_parEncCongL_Pair_r1_enc_TR_v2 =
    EmitPair (KT2 tagCode_congL)
             (EmitPair (EmitPair (KT2 cf2_Pair) emit_enc_TR_v2) emit_r1)

  -- Step 2 of chain: parEncCongR Pair r2 (cor(treeRec p v1)).
  emit_parEncCongR_Pair_r2_cor_TR_v1 : Fun2
  emit_parEncCongR_Pair_r2_cor_TR_v1 =
    EmitPair (KT2 tagCode_congR)
             (EmitPair (EmitPair (KT2 cf2_Pair) emit_cor_TR_p_v1) emit_r2)

  -- Wrap each in parEncCongR s ... enc_X.
  emit_step1_chain : Fun2
  emit_step1_chain =
    EmitPair (KT2 tagCode_congR)
             (EmitPair (EmitPair (KT2 sT) emit_enc_X)
                       emit_parEncCongL_Pair_r1_enc_TR_v2)

  emit_step2_chain : Fun2
  emit_step2_chain =
    EmitPair (KT2 tagCode_congR)
             (EmitPair (EmitPair (KT2 sT) emit_enc_X)
                       emit_parEncCongR_Pair_r2_cor_TR_v1)

  ----------------------------------------------------------------------
  -- Step 3 of chain: Df_s applied at (orig, V) where V = Pair (treeRec p v1)(treeRec p v2).
  --   = ap2 Df_s orig V.

  emit_V : Fun2  -- emits Pair (treeRec p v1)(treeRec p v2).
  emit_V = EmitPair emit_TR_p_v1 emit_TR_p_v2

  emit_Df_s_app : Fun2
  -- ap2 emit_Df_s_app orig recs = ap2 Df_s orig V.
  -- Construction: Lift (Comp2 Df_s I V_emit_F1) where V_emit_F1 : Fun1 of orig produces V.
  emit_Df_s_app =
    Lift (Comp2 Df_s I
           (Comp2 Pair treeRec_p_v1_F treeRec_p_v2_F))

  ----------------------------------------------------------------------
  -- Build the chain:
  -- chainDf =
  --   parEncRuleTrans (parEncAxTreeRecNd ...)
  --     (parEncRuleTrans step1
  --       (parEncRuleTrans step2 Df_s_app))

  -- parEncAxTreeRecNd as a Fun2 emitter (produces it at runtime).
  -- parEncAxTreeRecNd fT sT (cor p)(cor v1)(cor v2) =
  --   Pair tagCode_axTreeRecNd
  --     (Pair fT (Pair sT (Pair (cor p)(Pair (cor v1)(cor v2)))))
  emit_parEncAxTreeRecNd : Fun2
  emit_parEncAxTreeRecNd =
    EmitPair (KT2 tagCode_axTreeRecNd)
             (EmitPair (KT2 fT)
                       (EmitPair (KT2 sT)
                                 (EmitPair emit_cor_p
                                           (EmitPair emit_cor_v1 emit_cor_v2))))

  -- parEncRuleTrans y1 y2 = Pair tagCode_ruleTrans (Pair y1 y2).
  emit_RuleTrans : Fun2 -> Fun2 -> Fun2
  emit_RuleTrans h1 h2 =
    EmitPair (KT2 tagCode_ruleTrans) (EmitPair h1 h2)

  -- The full chain.
  emit_chainDf : Fun2
  emit_chainDf =
    emit_RuleTrans emit_parEncAxTreeRecNd
      (emit_RuleTrans emit_step1_chain
        (emit_RuleTrans emit_step2_chain emit_Df_s_app))

  step_emitter : Fun2
  step_emitter = emit_chainDf

  ----------------------------------------------------------------------
  -- Step C: D2_treeRec_fs.

  D2_treeRec_fs : Fun2
  D2_treeRec_fs = treeRec lf_emitter step_emitter

  ----------------------------------------------------------------------
  -- Step D: leaf reduction at concrete (p, O).
  --
  -- ap2 D2_treeRec_fs p O =BRA ap1 lf_emitter p
  --                       =BRA parEncRuleTrans (parEncAxTreeRecLf fT sT (cor p))
  --                                            (ap1 Df_f p)

  -- ap1 lf_emitter p reduces to parEncRuleTrans (...) (Df_f p).
  lf_emitter_red : (p : Term) ->
    Deriv (atomic (eqn (ap1 lf_emitter p)
                       (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                        (ap1 Df_f p))))
  lf_emitter_red p =
    let
      -- ap1 lf_emitter p = ap1 (Comp2 Pair (KT tagCode_ruleTrans) inner_chain_pair) p
      --                 = Pair (ap1 (KT tagCode_ruleTrans) p) (ap1 inner_chain_pair p)
      e1 : Deriv (atomic (eqn (ap1 lf_emitter p)
                              (ap2 Pair (ap1 (KT tagCode_ruleTrans) p)
                                        (ap1 inner_chain_pair p))))
      e1 = axComp2 Pair (KT tagCode_ruleTrans) inner_chain_pair p

      -- ap1 (KT tagCode_ruleTrans) p = tagCode_ruleTrans
      e2 : Deriv (atomic (eqn (ap1 (KT tagCode_ruleTrans) p) tagCode_ruleTrans))
      e2 = axKT (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) p

      -- ap1 inner_chain_pair p = Pair (ap1 f_treeRec_part p) (ap1 Df_f p)
      e3 : Deriv (atomic (eqn (ap1 inner_chain_pair p)
                              (ap2 Pair (ap1 f_treeRec_part p)
                                        (ap1 Df_f p))))
      e3 = axComp2 Pair f_treeRec_part Df_f p

      -- ap1 f_treeRec_part p = Pair tagCode_axTreeRecLf (ap1 f_treeRec_payload p)
      e4 : Deriv (atomic (eqn (ap1 f_treeRec_part p)
                              (ap2 Pair (ap1 (KT tagCode_axTreeRecLf) p)
                                        (ap1 f_treeRec_payload p))))
      e4 = axComp2 Pair (KT tagCode_axTreeRecLf) f_treeRec_payload p

      e4kt : Deriv (atomic (eqn (ap1 (KT tagCode_axTreeRecLf) p) tagCode_axTreeRecLf))
      e4kt = axKT (natCode tagAxTreeRecLf) (natCode_isValue tagAxTreeRecLf) p

      -- ap1 f_treeRec_payload p = Pair fT (ap1 inner_payload p)
      e5 : Deriv (atomic (eqn (ap1 f_treeRec_payload p)
                              (ap2 Pair (ap1 (KT fT) p) (ap1 inner_payload p))))
      e5 = axComp2 Pair (KT fT) inner_payload p

      e5kt : Deriv (atomic (eqn (ap1 (KT fT) p) fT))
      e5kt = axKT (codeF1 f) (codeF1_isValue f) p

      -- ap1 inner_payload p = Pair sT (cor p)
      e6 : Deriv (atomic (eqn (ap1 inner_payload p)
                              (ap2 Pair (ap1 (KT sT) p) (ap1 cor p))))
      e6 = axComp2 Pair (KT sT) cor p

      e6kt : Deriv (atomic (eqn (ap1 (KT sT) p) sT))
      e6kt = axKT (codeF2 s) (codeF2_isValue s) p

      e6_full : Deriv (atomic (eqn (ap1 inner_payload p) (ap2 Pair sT (ap1 cor p))))
      e6_full = ruleTrans e6 (congL Pair (ap1 cor p) e6kt)

      e5_full : Deriv (atomic (eqn (ap1 f_treeRec_payload p)
                                   (ap2 Pair fT (ap2 Pair sT (ap1 cor p)))))
      e5_full = ruleTrans e5
                  (ruleTrans (congL Pair (ap1 inner_payload p) e5kt)
                             (congR Pair fT e6_full))

      e4_full : Deriv (atomic (eqn (ap1 f_treeRec_part p)
                                   (parEncAxTreeRecLf fT sT (ap1 cor p))))
      e4_full = ruleTrans e4
                  (ruleTrans (congL Pair (ap1 f_treeRec_payload p) e4kt)
                             (congR Pair tagCode_axTreeRecLf e5_full))

      e3_full : Deriv (atomic (eqn (ap1 inner_chain_pair p)
                                   (ap2 Pair (parEncAxTreeRecLf fT sT (ap1 cor p))
                                             (ap1 Df_f p))))
      e3_full = ruleTrans e3 (congL Pair (ap1 Df_f p) e4_full)

      e1_full : Deriv (atomic (eqn (ap1 lf_emitter p)
                                   (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                                    (ap1 Df_f p))))
      e1_full = ruleTrans e1
                  (ruleTrans (congL Pair (ap1 inner_chain_pair p) e2)
                             (congR Pair tagCode_ruleTrans e3_full))
    in e1_full

  -- ap2 D2_treeRec_fs p O reduces to lf_emitter p (via axTreeRecLf).
  D2_treeRec_fs_at_O : (p : Term) ->
    Deriv (atomic (eqn (ap2 D2_treeRec_fs p O)
                       (parEncRuleTrans (parEncAxTreeRecLf fT sT (ap1 cor p))
                                        (ap1 Df_f p))))
  D2_treeRec_fs_at_O p =
    ruleTrans (axTreeRecLf lf_emitter step_emitter p) (lf_emitter_red p)

  ----------------------------------------------------------------------
  -- Step G: leaf-case correctness.
  -- D_correct2_treeRec_fs_O : (p : Term) -> Deriv (...) at (p, O).
  --
  -- This mirrors  BRA/Thm12/Parts/TreeRec.agda 's existing
  -- D_correct2_treeRec_fs_O exactly, just at our new D2_treeRec_fs.

  ----------------------------------------------------------------------
  -- step_emitter runtime reductions.
  --
  -- Helper: at runtime (orig, recs), each Lift-Fun1 emitter reduces to
  -- the corresponding Fun1 applied to orig (axLift-style).

  -- Generic EmitPair reduction.
  EmitPair_red : (ha hb : Fun2) (orig recs a' b' : Term) ->
    Deriv (atomic (eqn (ap2 ha orig recs) a')) ->
    Deriv (atomic (eqn (ap2 hb orig recs) b')) ->
    Deriv (atomic (eqn (ap2 (EmitPair ha hb) orig recs) (ap2 Pair a' b')))
  EmitPair_red ha hb orig recs a' b' Da Db =
    let s1 = axFan ha hb Pair orig recs
        s2 = congL Pair (ap2 hb orig recs) Da
        s3 = congR Pair a' Db
    in ruleTrans s1 (ruleTrans s2 s3)

  -- KT2 reduction at any orig, recs: ap2 (KT2 (reify v)) orig recs = reify v.
  KT2_red : (v : Term) -> IsValue v -> (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (KT2 v) orig recs) v))
  KT2_red v iv orig recs =
    ruleTrans (axLift (KT v) orig recs) (axKT v iv orig)

  -- KT2 reduction for non-reified Trees (e.g. cf2_TR which is a constant
  -- Term but reify-equiv to some Tree).  We give it explicitly.
  KT2_eq_red : (t : Term) (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (KT2 t) orig recs) (ap1 (KT t) orig)))
  KT2_eq_red t orig recs = axLift (KT t) orig recs

  -- Lift-Fun1 reduction.
  Lift_red : (g : Fun1) (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (Lift g) orig recs) (ap1 g orig)))
  Lift_red g orig recs = axLift g orig recs

  -- Helpers at concrete orig = Pair p (Pair v1 v2).
  --   ap1 Fst1 (Pair p (Pair v1 v2)) = p.

  Fst1_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 Fst1 (ap2 Pair p (ap2 Pair v1 v2))) p))
  Fst1_red p v1 v2 = axFst p (ap2 Pair v1 v2)

  v1Fun1_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 v1Fun1 (ap2 Pair p (ap2 Pair v1 v2))) v1))
  v1Fun1_red p v1 v2 =
    let s1 = axComp Fst Snd (ap2 Pair p (ap2 Pair v1 v2))
        s2 = cong1 Fst (axSnd p (ap2 Pair v1 v2))
        s3 = axFst v1 v2
    in ruleTrans s1 (ruleTrans s2 s3)

  v2Fun1_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 v2Fun1 (ap2 Pair p (ap2 Pair v1 v2))) v2))
  v2Fun1_red p v1 v2 =
    let s1 = axComp Snd Snd (ap2 Pair p (ap2 Pair v1 v2))
        s2 = cong1 Snd (axSnd p (ap2 Pair v1 v2))
        s3 = axSnd v1 v2
    in ruleTrans s1 (ruleTrans s2 s3)

  cor_p_F_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 cor_p_F (ap2 Pair p (ap2 Pair v1 v2))) (ap1 cor p)))
  cor_p_F_red p v1 v2 =
    ruleTrans (axComp cor Fst1 (ap2 Pair p (ap2 Pair v1 v2)))
              (cong1 cor (Fst1_red p v1 v2))

  cor_v1_F_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 cor_v1_F (ap2 Pair p (ap2 Pair v1 v2))) (ap1 cor v1)))
  cor_v1_F_red p v1 v2 =
    ruleTrans (axComp cor v1Fun1 (ap2 Pair p (ap2 Pair v1 v2)))
              (cong1 cor (v1Fun1_red p v1 v2))

  cor_v2_F_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 cor_v2_F (ap2 Pair p (ap2 Pair v1 v2))) (ap1 cor v2)))
  cor_v2_F_red p v1 v2 =
    ruleTrans (axComp cor v2Fun1 (ap2 Pair p (ap2 Pair v1 v2)))
              (cong1 cor (v2Fun1_red p v1 v2))

  treeRec_p_v1_F_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 treeRec_p_v1_F (ap2 Pair p (ap2 Pair v1 v2)))
                       (ap2 (treeRec f s) p v1)))
  treeRec_p_v1_F_red p v1 v2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        s1 = axComp2 (treeRec f s) Fst1 v1Fun1 orig
        s2 = congL (treeRec f s) (ap1 v1Fun1 orig) (Fst1_red p v1 v2)
        s3 = congR (treeRec f s) p (v1Fun1_red p v1 v2)
    in ruleTrans s1 (ruleTrans s2 s3)

  treeRec_p_v2_F_red : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap1 treeRec_p_v2_F (ap2 Pair p (ap2 Pair v1 v2)))
                       (ap2 (treeRec f s) p v2)))
  treeRec_p_v2_F_red p v1 v2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        s1 = axComp2 (treeRec f s) Fst1 v2Fun1 orig
        s2 = congL (treeRec f s) (ap1 v2Fun1 orig) (Fst1_red p v1 v2)
        s3 = congR (treeRec f s) p (v2Fun1_red p v1 v2)
    in ruleTrans s1 (ruleTrans s2 s3)

  ----------------------------------------------------------------------
  -- Tier-2 emitters (Lift-Fun1) at concrete orig.

  emit_p_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_p (ap2 Pair p (ap2 Pair v1 v2)) recs) p))
  emit_p_red p v1 v2 recs =
    ruleTrans (Lift_red Fst1 (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (Fst1_red p v1 v2)

  emit_v1_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_v1 (ap2 Pair p (ap2 Pair v1 v2)) recs) v1))
  emit_v1_red p v1 v2 recs =
    ruleTrans (Lift_red v1Fun1 (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (v1Fun1_red p v1 v2)

  emit_v2_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_v2 (ap2 Pair p (ap2 Pair v1 v2)) recs) v2))
  emit_v2_red p v1 v2 recs =
    ruleTrans (Lift_red v2Fun1 (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (v2Fun1_red p v1 v2)

  emit_cor_p_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cor_p (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap1 cor p)))
  emit_cor_p_red p v1 v2 recs =
    ruleTrans (Lift_red cor_p_F (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (cor_p_F_red p v1 v2)

  emit_cor_v1_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cor_v1 (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap1 cor v1)))
  emit_cor_v1_red p v1 v2 recs =
    ruleTrans (Lift_red cor_v1_F (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (cor_v1_F_red p v1 v2)

  emit_cor_v2_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cor_v2 (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap1 cor v2)))
  emit_cor_v2_red p v1 v2 recs =
    ruleTrans (Lift_red cor_v2_F (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (cor_v2_F_red p v1 v2)

  emit_TR_p_v1_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_TR_p_v1 (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap2 (treeRec f s) p v1)))
  emit_TR_p_v1_red p v1 v2 recs =
    ruleTrans (Lift_red treeRec_p_v1_F (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (treeRec_p_v1_F_red p v1 v2)

  emit_TR_p_v2_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_TR_p_v2 (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap2 (treeRec f s) p v2)))
  emit_TR_p_v2_red p v1 v2 recs =
    ruleTrans (Lift_red treeRec_p_v2_F (ap2 Pair p (ap2 Pair v1 v2)) recs)
              (treeRec_p_v2_F_red p v1 v2)

  emit_r1_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_r1 (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2)) r1))
  emit_r1_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        s1 = axPost Fst (Post Snd Pair) orig recs
        s2 = cong1 Fst (axPost Snd Pair orig recs)
        s3 = cong1 Fst (axSnd orig recs)
        s4 = axFst r1 r2
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  emit_r2_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_r2 (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2)) r2))
  emit_r2_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        s1 = axPost Snd (Post Snd Pair) orig recs
        s2 = cong1 Snd (axPost Snd Pair orig recs)
        s3 = cong1 Snd (axSnd orig recs)
        s4 = axSnd r1 r2
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  ----------------------------------------------------------------------
  -- Tier-3 composite emitters: cor of treeRec applied.

  emit_cor_TR_p_v1_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cor_TR_p_v1 (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap1 cor (ap2 (treeRec f s) p v1))))
  emit_cor_TR_p_v1_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        s1 = Lift_red cor_TR_p_v1_F orig recs
        s2 = axComp cor treeRec_p_v1_F orig
        s3 = cong1 cor (treeRec_p_v1_F_red p v1 v2)
    in ruleTrans s1 (ruleTrans s2 s3)

  emit_cor_TR_p_v2_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_cor_TR_p_v2 (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap1 cor (ap2 (treeRec f s) p v2))))
  emit_cor_TR_p_v2_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        s1 = Lift_red cor_TR_p_v2_F orig recs
        s2 = axComp cor treeRec_p_v2_F orig
        s3 = cong1 cor (treeRec_p_v2_F_red p v1 v2)
    in ruleTrans s1 (ruleTrans s2 s3)

  ----------------------------------------------------------------------
  -- Composite Pair-shaped emitters.

  -- mkAp2T cf2_Pair (cor v1)(cor v2)
  emit_mkAp2T_Pair_corv1_corv2_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_mkAp2T_cf2_Pair_corv1_corv2
                              (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair cf2_Pair
                           (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))
  emit_mkAp2T_Pair_corv1_corv2_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        e_inner = EmitPair_red emit_cor_v1 emit_cor_v2 orig recs _ _
                    (emit_cor_v1_red p v1 v2 recs)
                    (emit_cor_v2_red p v1 v2 recs)
        e_mid   = EmitPair_red (KT2 cf2_Pair) (EmitPair emit_cor_v1 emit_cor_v2)
                    orig recs cf2_Pair _
                    (KT2_red (codeF2 Pair) (codeF2_isValue Pair) orig recs)
                    e_inner
    in EmitPair_red (KT2 (reify tagAp2))
                    (EmitPair (KT2 cf2_Pair) (EmitPair emit_cor_v1 emit_cor_v2))
                    orig recs (reify tagAp2) _
                    (KT2_red tagAp2 tagAp2_isValue orig recs)
                    e_mid

  -- enc_TR_v1 = mkAp2T cf2_TR (cor p)(cor v1).
  emit_enc_TR_v1_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_enc_TR_v1
                              (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair cf2_TR
                           (ap2 Pair (ap1 cor p) (ap1 cor v1))))))
  emit_enc_TR_v1_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        e_pair_cor = EmitPair_red emit_cor_p emit_cor_v1 orig recs _ _
                       (emit_cor_p_red p v1 v2 recs)
                       (emit_cor_v1_red p v1 v2 recs)
        e_mid = EmitPair_red (KT2 cf2_TR) (EmitPair emit_cor_p emit_cor_v1)
                  orig recs cf2_TR _
                  (KT2_red (codeF2 (treeRec f s)) (codeF2_isValue (treeRec f s)) orig recs)
                  e_pair_cor
    in EmitPair_red (KT2 (reify tagAp2))
                    (EmitPair (KT2 cf2_TR) (EmitPair emit_cor_p emit_cor_v1))
                    orig recs (reify tagAp2) _
                    (KT2_red tagAp2 tagAp2_isValue orig recs)
                    e_mid

  emit_enc_TR_v2_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_enc_TR_v2
                              (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair cf2_TR
                           (ap2 Pair (ap1 cor p) (ap1 cor v2))))))
  emit_enc_TR_v2_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        e_pair_cor = EmitPair_red emit_cor_p emit_cor_v2 orig recs _ _
                       (emit_cor_p_red p v1 v2 recs)
                       (emit_cor_v2_red p v1 v2 recs)
        e_mid = EmitPair_red (KT2 cf2_TR) (EmitPair emit_cor_p emit_cor_v2)
                  orig recs cf2_TR _
                  (KT2_red (codeF2 (treeRec f s)) (codeF2_isValue (treeRec f s)) orig recs)
                  e_pair_cor
    in EmitPair_red (KT2 (reify tagAp2))
                    (EmitPair (KT2 cf2_TR) (EmitPair emit_cor_p emit_cor_v2))
                    orig recs (reify tagAp2) _
                    (KT2_red tagAp2 tagAp2_isValue orig recs)
                    e_mid

  -- enc_X = mkAp2T cf2_Pair (cor p)(mkAp2T cf2_Pair (cor v1)(cor v2)).
  encX_canonical : (p v1 v2 : Term) -> Term
  encX_canonical p v1 v2 =
    ap2 Pair (reify tagAp2)
      (ap2 Pair cf2_Pair
        (ap2 Pair (ap1 cor p)
          (ap2 Pair (reify tagAp2)
            (ap2 Pair cf2_Pair
              (ap2 Pair (ap1 cor v1) (ap1 cor v2))))))

  emit_enc_X_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_enc_X (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (encX_canonical p v1 v2)))
  emit_enc_X_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        e_inner = emit_mkAp2T_Pair_corv1_corv2_red p v1 v2 recs
        e_pair_cor_p_inner =
          EmitPair_red emit_cor_p emit_mkAp2T_cf2_Pair_corv1_corv2
            orig recs _ _
            (emit_cor_p_red p v1 v2 recs)
            e_inner
        e_mid =
          EmitPair_red (KT2 cf2_Pair)
            (EmitPair emit_cor_p emit_mkAp2T_cf2_Pair_corv1_corv2)
            orig recs cf2_Pair _
            (KT2_red (codeF2 Pair) (codeF2_isValue Pair) orig recs)
            e_pair_cor_p_inner
    in EmitPair_red (KT2 (reify tagAp2))
                    (EmitPair (KT2 cf2_Pair)
                              (EmitPair emit_cor_p emit_mkAp2T_cf2_Pair_corv1_corv2))
                    orig recs (reify tagAp2) _
                    (KT2_red tagAp2 tagAp2_isValue orig recs)
                    e_mid

  ----------------------------------------------------------------------
  -- Chain emitters: parEncCongL Pair / parEncCongR Pair / etc.

  -- parEncCongL Pair r1 enc_TR_v2 = Pair tagCode_congL (Pair (Pair cf2_Pair enc_TR_v2) r1)
  emit_parEncCongL_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_parEncCongL_Pair_r1_enc_TR_v2
                              (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2))
                       (parEncCongL Pair r1
                         (ap2 Pair (reify tagAp2)
                           (ap2 Pair cf2_TR
                             (ap2 Pair (ap1 cor p) (ap1 cor v2)))))))
  emit_parEncCongL_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        e_inner_pair = EmitPair_red (KT2 cf2_Pair) emit_enc_TR_v2 orig recs cf2_Pair _
                         (KT2_red (codeF2 Pair) (codeF2_isValue Pair) orig recs)
                         (emit_enc_TR_v2_red p v1 v2 recs)
        e_outer_pair = EmitPair_red (EmitPair (KT2 cf2_Pair) emit_enc_TR_v2) emit_r1
                         orig recs _ _
                         e_inner_pair
                         (emit_r1_red p v1 v2 r1 r2)
    in EmitPair_red (KT2 tagCode_congL)
                    (EmitPair (EmitPair (KT2 cf2_Pair) emit_enc_TR_v2) emit_r1)
                    orig recs tagCode_congL _
                    (KT2_red (natCode tagCongL) (natCode_isValue tagCongL) orig recs)
                    e_outer_pair

  -- parEncCongR Pair r2 (cor (treeRec p v1)) = Pair tagCode_congR (Pair (Pair cf2_Pair (cor TR_v1)) r2)
  emit_parEncCongR_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_parEncCongR_Pair_r2_cor_TR_v1
                              (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2))
                       (parEncCongR Pair r2 (ap1 cor (ap2 (treeRec f s) p v1)))))
  emit_parEncCongR_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        e_inner_pair = EmitPair_red (KT2 cf2_Pair) emit_cor_TR_p_v1 orig recs cf2_Pair _
                         (KT2_red (codeF2 Pair) (codeF2_isValue Pair) orig recs)
                         (emit_cor_TR_p_v1_red p v1 v2 recs)
        e_outer_pair = EmitPair_red (EmitPair (KT2 cf2_Pair) emit_cor_TR_p_v1) emit_r2
                         orig recs _ _
                         e_inner_pair
                         (emit_r2_red p v1 v2 r1 r2)
    in EmitPair_red (KT2 tagCode_congR)
                    (EmitPair (EmitPair (KT2 cf2_Pair) emit_cor_TR_p_v1) emit_r2)
                    orig recs tagCode_congR _
                    (KT2_red (natCode tagCongR) (natCode_isValue tagCongR) orig recs)
                    e_outer_pair

  -- step1_chain = parEncCongR s (parEncCongL Pair r1 enc_TR_v2) enc_X
  emit_step1_chain_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_step1_chain
                              (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2))
                       (parEncCongR s
                         (parEncCongL Pair r1
                           (ap2 Pair (reify tagAp2)
                             (ap2 Pair cf2_TR
                               (ap2 Pair (ap1 cor p) (ap1 cor v2)))))
                         (encX_canonical p v1 v2))))
  emit_step1_chain_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        e_sT_X = EmitPair_red (KT2 sT) emit_enc_X orig recs sT _
                   (KT2_red (codeF2 s) (codeF2_isValue s) orig recs)
                   (emit_enc_X_red p v1 v2 recs)
        e_outer = EmitPair_red (EmitPair (KT2 sT) emit_enc_X)
                    emit_parEncCongL_Pair_r1_enc_TR_v2 orig recs _ _
                    e_sT_X
                    (emit_parEncCongL_red p v1 v2 r1 r2)
    in EmitPair_red (KT2 tagCode_congR)
                    (EmitPair (EmitPair (KT2 sT) emit_enc_X)
                              emit_parEncCongL_Pair_r1_enc_TR_v2)
                    orig recs tagCode_congR _
                    (KT2_red (natCode tagCongR) (natCode_isValue tagCongR) orig recs)
                    e_outer

  -- step2_chain = parEncCongR s (parEncCongR Pair r2 (cor TR_v1)) enc_X
  emit_step2_chain_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_step2_chain
                              (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2))
                       (parEncCongR s
                         (parEncCongR Pair r2 (ap1 cor (ap2 (treeRec f s) p v1)))
                         (encX_canonical p v1 v2))))
  emit_step2_chain_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        e_sT_X = EmitPair_red (KT2 sT) emit_enc_X orig recs sT _
                   (KT2_red (codeF2 s) (codeF2_isValue s) orig recs)
                   (emit_enc_X_red p v1 v2 recs)
        e_outer = EmitPair_red (EmitPair (KT2 sT) emit_enc_X)
                    emit_parEncCongR_Pair_r2_cor_TR_v1 orig recs _ _
                    e_sT_X
                    (emit_parEncCongR_red p v1 v2 r1 r2)
    in EmitPair_red (KT2 tagCode_congR)
                    (EmitPair (EmitPair (KT2 sT) emit_enc_X)
                              emit_parEncCongR_Pair_r2_cor_TR_v1)
                    orig recs tagCode_congR _
                    (KT2_red (natCode tagCongR) (natCode_isValue tagCongR) orig recs)
                    e_outer

  -- emit_Df_s_app: ap2 emit_Df_s_app orig recs = ap2 Df_s orig V (V = Pair (treeRec p v1)(treeRec p v2)).
  emit_Df_s_app_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_Df_s_app (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (ap2 Df_s (ap2 Pair p (ap2 Pair v1 v2))
                         (ap2 Pair (ap2 (treeRec f s) p v1)
                                   (ap2 (treeRec f s) p v2)))))
  emit_Df_s_app_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        s1 = Lift_red (Comp2 Df_s I (Comp2 Pair treeRec_p_v1_F treeRec_p_v2_F))
                       orig recs
        -- ap1 (Comp2 Df_s I V_F) orig = ap2 Df_s (ap1 I orig) (ap1 V_F orig)
        s2 = axComp2 Df_s I (Comp2 Pair treeRec_p_v1_F treeRec_p_v2_F) orig
        -- ap1 I orig = orig
        s3 = congL Df_s (ap1 (Comp2 Pair treeRec_p_v1_F treeRec_p_v2_F) orig)
                        (axI orig)
        -- ap1 V_F orig = Pair (treeRec p v1)(treeRec p v2)
        sV = axComp2 Pair treeRec_p_v1_F treeRec_p_v2_F orig
        sV1 = congL Pair (ap1 treeRec_p_v2_F orig) (treeRec_p_v1_F_red p v1 v2)
        sV2 = congR Pair (ap2 (treeRec f s) p v1) (treeRec_p_v2_F_red p v1 v2)
        sV_full = ruleTrans sV (ruleTrans sV1 sV2)
        s4 = congR Df_s orig sV_full
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

  -- emit_parEncAxTreeRecNd: ap2 ... orig recs = parEncAxTreeRecNd fT sT (cor p)(cor v1)(cor v2).
  emit_parEncAxTreeRecNd_red : (p v1 v2 recs : Term) ->
    Deriv (atomic (eqn (ap2 emit_parEncAxTreeRecNd
                              (ap2 Pair p (ap2 Pair v1 v2)) recs)
                       (parEncAxTreeRecNd fT sT (ap1 cor p) (ap1 cor v1) (ap1 cor v2))))
  emit_parEncAxTreeRecNd_red p v1 v2 recs =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        e_corv1v2 = EmitPair_red emit_cor_v1 emit_cor_v2 orig recs _ _
                      (emit_cor_v1_red p v1 v2 recs)
                      (emit_cor_v2_red p v1 v2 recs)
        e_corp_inner = EmitPair_red emit_cor_p (EmitPair emit_cor_v1 emit_cor_v2)
                         orig recs _ _
                         (emit_cor_p_red p v1 v2 recs)
                         e_corv1v2
        e_sT_inner = EmitPair_red (KT2 sT) (EmitPair emit_cor_p (EmitPair emit_cor_v1 emit_cor_v2))
                       orig recs sT _
                       (KT2_red (codeF2 s) (codeF2_isValue s) orig recs)
                       e_corp_inner
        e_fT_outer = EmitPair_red (KT2 fT) (EmitPair (KT2 sT) (EmitPair emit_cor_p (EmitPair emit_cor_v1 emit_cor_v2)))
                       orig recs fT _
                       (KT2_red (codeF1 f) (codeF1_isValue f) orig recs)
                       e_sT_inner
    in EmitPair_red (KT2 tagCode_axTreeRecNd)
                    (EmitPair (KT2 fT) (EmitPair (KT2 sT) (EmitPair emit_cor_p (EmitPair emit_cor_v1 emit_cor_v2))))
                    orig recs tagCode_axTreeRecNd _
                    (KT2_red (natCode tagAxTreeRecNd) (natCode_isValue tagAxTreeRecNd) orig recs)
                    e_fT_outer

  ----------------------------------------------------------------------
  -- Canonical chain Df term at concrete (p, v1, v2, r1, r2).

  Df_s_app_term : Term -> Term -> Term -> Term
  Df_s_app_term p v1 v2 =
    ap2 Df_s (ap2 Pair p (ap2 Pair v1 v2))
             (ap2 Pair (ap2 (treeRec f s) p v1) (ap2 (treeRec f s) p v2))

  step1_chain_term : Term -> Term -> Term -> Term -> Term
  step1_chain_term p v1 v2 r1 =
    parEncCongR s
      (parEncCongL Pair r1
        (ap2 Pair (reify tagAp2)
          (ap2 Pair cf2_TR
            (ap2 Pair (ap1 cor p) (ap1 cor v2)))))
      (encX_canonical p v1 v2)

  step2_chain_term : Term -> Term -> Term -> Term -> Term
  step2_chain_term p v1 v2 r2 =
    parEncCongR s
      (parEncCongR Pair r2 (ap1 cor (ap2 (treeRec f s) p v1)))
      (encX_canonical p v1 v2)

  chain_Df_term : Term -> Term -> Term -> Term -> Term -> Term
  chain_Df_term p v1 v2 r1 r2 =
    parEncRuleTrans
      (parEncAxTreeRecNd fT sT (ap1 cor p) (ap1 cor v1) (ap1 cor v2))
      (parEncRuleTrans (step1_chain_term p v1 v2 r1)
        (parEncRuleTrans (step2_chain_term p v1 v2 r2)
          (Df_s_app_term p v1 v2)))

  -- chainDf reduces at runtime.
  emit_chainDf_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 emit_chainDf
                              (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2))
                       (chain_Df_term p v1 v2 r1 r2)))
  emit_chainDf_red p v1 v2 r1 r2 =
    let orig = ap2 Pair p (ap2 Pair v1 v2)
        recs = ap2 Pair r1 r2
        -- innermost: parEncRuleTrans step2_chain Df_s_app
        e_inner =
          let e_pair = EmitPair_red emit_step2_chain emit_Df_s_app orig recs _ _
                        (emit_step2_chain_red p v1 v2 r1 r2)
                        (emit_Df_s_app_red p v1 v2 recs)
          in EmitPair_red (KT2 tagCode_ruleTrans)
                          (EmitPair emit_step2_chain emit_Df_s_app)
                          orig recs tagCode_ruleTrans _
                          (KT2_red (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) orig recs)
                          e_pair
        -- middle: parEncRuleTrans step1_chain (above)
        e_mid =
          let e_pair = EmitPair_red emit_step1_chain
                         (emit_RuleTrans emit_step2_chain emit_Df_s_app)
                         orig recs _ _
                         (emit_step1_chain_red p v1 v2 r1 r2)
                         e_inner
          in EmitPair_red (KT2 tagCode_ruleTrans)
                          (EmitPair emit_step1_chain
                            (emit_RuleTrans emit_step2_chain emit_Df_s_app))
                          orig recs tagCode_ruleTrans _
                          (KT2_red (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) orig recs)
                          e_pair
        -- outer: parEncRuleTrans parEncAxTreeRecNd middle
        e_outer_pair = EmitPair_red emit_parEncAxTreeRecNd
                         (emit_RuleTrans emit_step1_chain
                           (emit_RuleTrans emit_step2_chain emit_Df_s_app))
                         orig recs _ _
                         (emit_parEncAxTreeRecNd_red p v1 v2 recs)
                         e_mid
    in EmitPair_red (KT2 tagCode_ruleTrans)
                    (EmitPair emit_parEncAxTreeRecNd
                      (emit_RuleTrans emit_step1_chain
                        (emit_RuleTrans emit_step2_chain emit_Df_s_app)))
                    orig recs tagCode_ruleTrans _
                    (KT2_red (natCode tagRuleTrans) (natCode_isValue tagRuleTrans) orig recs)
                    e_outer_pair

  -- step_emitter = emit_chainDf, so this is the final step.
  step_emitter_red : (p v1 v2 r1 r2 : Term) ->
    Deriv (atomic (eqn (ap2 step_emitter
                              (ap2 Pair p (ap2 Pair v1 v2)) (ap2 Pair r1 r2))
                       (chain_Df_term p v1 v2 r1 r2)))
  step_emitter_red = emit_chainDf_red

  ----------------------------------------------------------------------
  -- D2_treeRec_fs at Pair input: combines axTreeRecNd with step_emitter_red.

  D2_treeRec_fs_at_Nd : (p v1 v2 : Term) ->
    Deriv (atomic (eqn (ap2 D2_treeRec_fs p (ap2 Pair v1 v2))
                       (chain_Df_term p v1 v2
                         (ap2 D2_treeRec_fs p v1)
                         (ap2 D2_treeRec_fs p v2))))
  D2_treeRec_fs_at_Nd p v1 v2 =
    ruleTrans (axTreeRecNd lf_emitter step_emitter p v1 v2)
              (step_emitter_red p v1 v2
                (ap2 D2_treeRec_fs p v1)
                (ap2 D2_treeRec_fs p v2))

  ----------------------------------------------------------------------
  -- D_correct2_treeRec_fs_O : leaf-case correctness.
  --
  -- Existing leaf-case proof (unchanged from prior session).

  D_correct2_treeRec_fs_O : (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p O))
                       (codeFTeq2_treeRec_fs f s p O)))
  D_correct2_treeRec_fs_O p =
    let
      r_thmT : Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p O))
                                  (ap1 thmT (parEncRuleTrans
                                              (parEncAxTreeRecLf fT sT (ap1 cor p))
                                              (ap1 Df_f p)))))
      r_thmT = cong1 thmT (D2_treeRec_fs_at_O p)

      u1_y1 : Term
      u1_y1 = ap2 Pair (reify tagAp2)
                (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                     (ap2 Pair fT sT))
                          (ap2 Pair (ap1 cor p) O))
      u2_y1 : Term
      u2_y1 = ap2 Pair (reify tagAp1) (ap2 Pair fT (ap1 cor p))

      d_y1 : Deriv (atomic (eqn (ap1 thmT (parEncAxTreeRecLf fT sT (ap1 cor p)))
                                  (ap2 Pair u1_y1 u2_y1)))
      d_y1 = parDispAxTreeRecLf fT sT (ap1 cor p)

      u1_Df : Term
      u1_Df = ap2 Pair (reify tagAp1) (ap2 Pair fT (ap1 cor p))
      u2_Df : Term
      u2_Df = ap1 cor (ap1 f p)

      d_Df : Deriv (atomic (eqn (ap1 thmT (ap1 Df_f p))
                                  (ap2 Pair u1_Df u2_Df)))
      d_Df = proof_f p

      y1_shape : Deriv (atomic (eqn (ap1 Fst (parEncAxTreeRecLf fT sT (ap1 cor p)))
                                      (ap2 Pair O _)))
      y1_shape = axFst tagCode_axTreeRecLf _

      d_chain : Deriv (atomic (eqn
            (ap1 thmT (parEncRuleTrans
                        (parEncAxTreeRecLf fT sT (ap1 cor p))
                        (ap1 Df_f p)))
            (ap2 Pair u1_y1 u2_Df)))
      d_chain = parDispRuleTrans
                  (parEncAxTreeRecLf fT sT (ap1 cor p))
                  (ap1 Df_f p)
                  u1_y1 u2_y1 u1_Df u2_Df
                  _ _
                  y1_shape d_y1 d_Df

      cor_O : Deriv (atomic (eqn (ap1 cor O) O))
      cor_O = axRecLf stepCor

      bL_innerPair : Deriv (atomic (eqn (ap2 Pair (ap1 cor p) O)
                                          (ap2 Pair (ap1 cor p) (ap1 cor O))))
      bL_innerPair = congR Pair (ap1 cor p) (ruleSym cor_O)

      bL_secondPair : Deriv (atomic (eqn
                (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                     (ap2 Pair fT sT))
                          (ap2 Pair (ap1 cor p) O))
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor p) (ap1 cor O)))))
      bL_secondPair = congR Pair (reify (codeF2 (treeRec f s))) bL_innerPair

      bL : Deriv (atomic (eqn u1_y1
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 (treeRec f s)))
                                    (ap2 Pair (ap1 cor p) (ap1 cor O))))))
      bL = congR Pair (reify tagAp2) bL_secondPair

      recLf_eq : Deriv (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))
      recLf_eq = axTreeRecLf f s p

      bR : Deriv (atomic (eqn u2_Df (ap1 cor (ap2 (treeRec f s) p O))))
      bR = ruleSym (cong1 cor recLf_eq)

      bridge1 : Deriv (atomic (eqn (ap2 Pair u1_y1 u2_Df)
                                     (ap2 Pair
                                       (ap2 Pair (reify tagAp2)
                                                 (ap2 Pair (reify (codeF2 (treeRec f s)))
                                                           (ap2 Pair (ap1 cor p) (ap1 cor O))))
                                       u2_Df)))
      bridge1 = congL Pair u2_Df bL

      bridge2 : Deriv (atomic (eqn
                (ap2 Pair
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 (treeRec f s)))
                                      (ap2 Pair (ap1 cor p) (ap1 cor O))))
                  u2_Df)
                (codeFTeq2_treeRec_fs f s p O)))
      bridge2 = congR Pair
                  (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 (treeRec f s)))
                                      (ap2 Pair (ap1 cor p) (ap1 cor O))))
                  bR
    in ruleTrans r_thmT (ruleTrans d_chain (ruleTrans bridge1 bridge2))

  ----------------------------------------------------------------------
  -- Step 3a: substitution-closure lemmas + formula_eq.
  --
  -- All structural; mirrors BRA/Thm12/Parts/TreeRec.agda lines 506-600.

  D2_treeRec_fs_closed : (k : Nat) (r : Term) ->
    Eq (substF2 k r D2_treeRec_fs) D2_treeRec_fs
  D2_treeRec_fs_closed k r = Fun2_closed k r D2_treeRec_fs

  treeRec_fs_closed : (k : Nat) (r : Term) ->
    Eq (substF2 k r (treeRec f s)) (treeRec f s)
  treeRec_fs_closed k r = Fun2_closed k r (treeRec f s)

  P_Th12_treeRec : Formula
  P_Th12_treeRec =
    atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) (var zero)))
                (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))

  P_concrete_at : Term -> Formula
  P_concrete_at r =
    atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) r))
                (codeFTeq2_treeRec_fs f s (var (suc zero)) r))

  private
    lhs_eq : (r : Term) ->
      Eq (subst zero r (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) (var zero))))
         (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) r))
    lhs_eq r =
      eqTrans (eqCong (\ F -> ap1 F (ap2 (substF2 zero r D2_treeRec_fs) (var (suc zero)) r))
                       (thClosed zero r))
              (eqCong (\ D -> ap1 thmT (ap2 D (var (suc zero)) r))
                       (D2_treeRec_fs_closed zero r))

    inner_corPair_eq : (r : Term) ->
      Eq (subst zero r (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor (var zero))))
         (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor r))
    inner_corPair_eq r =
      eqTrans (eqCong (\ C -> ap2 Pair (ap1 C (var (suc zero)))
                                        (ap1 (substF1 zero r cor) r))
                       (cor_closed zero r))
              (eqCong (\ C -> ap2 Pair (ap1 cor (var (suc zero))) (ap1 C r))
                       (cor_closed zero r))

    second_pair_eq : (r : Term) ->
      Eq (subst zero r (ap2 Pair (reify (codeF2 (treeRec f s)))
                                  (ap2 Pair (ap1 cor (var (suc zero)))
                                            (ap1 cor (var zero)))))
         (ap2 Pair (reify (codeF2 (treeRec f s)))
                   (ap2 Pair (ap1 cor (var (suc zero)))
                             (ap1 cor r)))
    second_pair_eq r =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst zero r
                                  (ap2 Pair (ap1 cor (var (suc zero)))
                                            (ap1 cor (var zero)))))
                       (subst_reify zero r (codeF2 (treeRec f s)) (codeF2_isValue (treeRec f s))))
              (eqCong (\ P -> ap2 Pair (reify (codeF2 (treeRec f s))) P)
                       (inner_corPair_eq r))

    encoded_lhs_eq : (r : Term) ->
      Eq (subst zero r (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor (var zero))))))
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                             (ap2 Pair (ap1 cor (var (suc zero)))
                                       (ap1 cor r))))
    encoded_lhs_eq r =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst zero r
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor (var zero))))))
                       (subst_reify zero r tagAp2 tagAp2_isValue))
              (eqCong (\ Q -> ap2 Pair (reify tagAp2) Q)
                       (second_pair_eq r))

    cor_treeRec_eq : (r : Term) ->
      Eq (subst zero r (ap1 cor (ap2 (treeRec f s) (var (suc zero)) (var zero))))
         (ap1 cor (ap2 (treeRec f s) (var (suc zero)) r))
    cor_treeRec_eq r =
      eqTrans (eqCong (\ C -> ap1 C (ap2 (substF2 zero r (treeRec f s))
                                          (var (suc zero)) r))
                       (cor_closed zero r))
              (eqCong (\ TR -> ap1 cor (ap2 TR (var (suc zero)) r))
                       (treeRec_fs_closed zero r))

    rhs_eq : (r : Term) ->
      Eq (subst zero r (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))
         (codeFTeq2_treeRec_fs f s (var (suc zero)) r)
    rhs_eq r =
      eqTrans (eqCong (\ X -> ap2 Pair X
                                (subst zero r
                                  (ap1 cor (ap2 (treeRec f s) (var (suc zero)) (var zero)))))
                       (encoded_lhs_eq r))
              (eqCong (\ Y -> ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor r))))
                                Y)
                       (cor_treeRec_eq r))

    formula_eq : (r : Term) ->
      Eq (substF zero r P_Th12_treeRec) (P_concrete_at r)
    formula_eq r =
      eqTrans (eqCong (\ L -> atomic (eqn L
                                (subst zero r
                                  (codeFTeq2_treeRec_fs f s (var (suc zero)) (var zero)))))
                       (lhs_eq r))
              (eqCong (\ R -> atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) r)) R))
                       (rhs_eq r))

    to_substF : (r : Term) -> Deriv (P_concrete_at r) ->
                Deriv (substF zero r P_Th12_treeRec)
    to_substF r prf = eqSubst Deriv (eqSym (formula_eq r)) prf

  ----------------------------------------------------------------------
  -- Step 3b: leaf-input subst form.

  private
    base_O_subst : Deriv (substF zero O P_Th12_treeRec)
    base_O_subst = to_substF O (D_correct2_treeRec_fs_O (var (suc zero)))

  ----------------------------------------------------------------------
  -- Step 3c: BasePair module.  Doubly-lifted Pair-case proof.
  --
  -- ruleIndBT's  step  obligation at v1IndNat = 2, v2IndNat = 3:
  --   Pv1 imp (Pv2 imp Ppair)
  -- where  Pv_i = substF zero (var i) P_Th12_treeRec  and
  --        Ppair = substF zero (Pair v1T v2T) P_Th12_treeRec.

  v1IndNat : Nat
  v1IndNat = suc (suc zero)

  v2IndNat : Nat
  v2IndNat = suc (suc (suc zero))

  axImpRefl : (Q : Formula) -> Deriv (Q imp Q)
  axImpRefl Q = mp (mp (axS Q (Q imp Q) Q) (axK Q (Q imp Q))) (axK Q Q)

  module BasePair where

    pT : Term
    pT = var (suc zero)

    v1T : Term
    v1T = var v1IndNat

    v2T : Term
    v2T = var v2IndNat

    pairT : Term
    pairT = ap2 Pair v1T v2T

    -- Concrete-form helper: codeFTeq2_TR f s pT v_i = (enc_TR_v_i, cor TR_v_i).

    enc_TR_pv1 : Term
    enc_TR_pv1 = ap2 Pair (reify tagAp2)
                   (ap2 Pair cf2_TR (ap2 Pair (ap1 cor pT) (ap1 cor v1T)))

    enc_TR_pv2 : Term
    enc_TR_pv2 = ap2 Pair (reify tagAp2)
                   (ap2 Pair cf2_TR (ap2 Pair (ap1 cor pT) (ap1 cor v2T)))

    cor_TR_pv1 : Term
    cor_TR_pv1 = ap1 cor (ap2 (treeRec f s) pT v1T)

    cor_TR_pv2 : Term
    cor_TR_pv2 = ap1 cor (ap2 (treeRec f s) pT v2T)

    -- enc_X = mkAp2T cf2_Pair (cor pT)(mkAp2T cf2_Pair (cor v1T)(cor v2T))
    enc_X : Term
    enc_X = ap2 Pair (reify tagAp2)
              (ap2 Pair cf2_Pair
                (ap2 Pair (ap1 cor pT)
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair cf2_Pair
                      (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))

    Pv1 : Formula
    Pv1 = substF zero v1T P_Th12_treeRec

    Pv2 : Formula
    Pv2 = substF zero v2T P_Th12_treeRec

    Ppair : Formula
    Ppair = substF zero pairT P_Th12_treeRec

    Pv1_concrete : Formula
    Pv1_concrete = P_concrete_at v1T

    Pv2_concrete : Formula
    Pv2_concrete = P_concrete_at v2T

    Ppair_concrete : Formula
    Ppair_concrete = P_concrete_at pairT

    --------------------------------------------------------------------
    -- IH-on-Pv1 / IH-on-Pv2 hypotheses (axK / axImpRefl).

    dl_Pv1 : Deriv (Pv1 imp (Pv2 imp Pv1))
    dl_Pv1 = axK Pv1 Pv2

    dl_Pv2 : Deriv (Pv1 imp (Pv2 imp Pv2))
    dl_Pv2 = mp (axK (Pv2 imp Pv2) Pv1) (axImpRefl Pv2)

    --------------------------------------------------------------------
    -- Cast Pv_i hypotheses to concrete-form via formula_eq.

    Pv1_to_concrete : Deriv (Pv1 imp Pv1_concrete)
    Pv1_to_concrete = eqSubst (\ Q -> Deriv (Pv1 imp Q))
                              (formula_eq v1T) (axImpRefl Pv1)

    Pv2_to_concrete : Deriv (Pv2 imp Pv2_concrete)
    Pv2_to_concrete = eqSubst (\ Q -> Deriv (Pv2 imp Q))
                              (formula_eq v2T) (axImpRefl Pv2)

    -- Concrete-form lifted IHs (via mp + B_combinator-style chaining).

    -- Helper: from D : P -> Q -> R and bridge R -> R',  build P -> Q -> R'.
    bridgeImp2 : (P Q R R' : Formula) ->
                 Deriv (P imp (Q imp R)) -> Deriv (R imp R') ->
                 Deriv (P imp (Q imp R'))
    bridgeImp2 P Q R R' d br =
      let stepQR' : Deriv ((Q imp R) imp (Q imp R'))
          stepQR' = mp (axS Q R R') (mp (axK (R imp R') Q) br)
      in mp (mp (axS P (Q imp R) (Q imp R')) (mp (axK ((Q imp R) imp (Q imp R')) P) stepQR')) d

    dl_Pv1_concrete : Deriv (Pv1 imp (Pv2 imp Pv1_concrete))
    dl_Pv1_concrete = bridgeImp2 Pv1 Pv2 Pv1 Pv1_concrete dl_Pv1 Pv1_to_concrete

    dl_Pv2_concrete : Deriv (Pv1 imp (Pv2 imp Pv2_concrete))
    dl_Pv2_concrete = bridgeImp2 Pv1 Pv2 Pv2 Pv2_concrete dl_Pv2 Pv2_to_concrete

    --------------------------------------------------------------------
    -- Atom-form: extract the inner eqn from the concrete formula.
    -- Pv_i_concrete = atomic (eqn (thmT (D2 pT v_iT)) (codeFTeq2_TR f s pT v_iT))
    -- which equals atomic (eqn (thmT (D2 pT v_iT)) (Pair enc_TR_pv_i cor_TR_pv_i)).
    -- These are definitionally equal (codeFTeq2 unfolds to a Pair).

    -- Pv1_concrete = atomic (eqn (thmT (D2 pT v1T)) (codeFTeq2_TR f s pT v1T))
    -- and codeFTeq2_TR ... pT v1T = Pair enc_TR_pv1 cor_TR_pv1 by definition.

    dl_Pv1_atom : Deriv (Pv1 imp (Pv2 imp atomic
                    (eqn (ap1 thmT (ap2 D2_treeRec_fs pT v1T))
                         (ap2 Pair enc_TR_pv1 cor_TR_pv1))))
    dl_Pv1_atom = dl_Pv1_concrete

    dl_Pv2_atom : Deriv (Pv1 imp (Pv2 imp atomic
                    (eqn (ap1 thmT (ap2 D2_treeRec_fs pT v2T))
                         (ap2 Pair enc_TR_pv2 cor_TR_pv2))))
    dl_Pv2_atom = dl_Pv2_concrete

    --------------------------------------------------------------------
    -- The chain pieces.
    --
    -- Y1  = parEncAxTreeRecNd fT sT (cor pT)(cor v1T)(cor v2T)
    -- Y2  = parEncCongR s (parEncCongL Pair (D2 pT v1T) enc_TR_pv2) enc_X
    -- Y3  = parEncCongR s (parEncCongR Pair (cor TR_pv1) (D2 pT v2T)) enc_X
    -- Y4  = ap2 Df_s X V  where X = Pair pT pairT, V = Pair TR_pv1 TR_pv2.

    Y1_term : Term
    Y1_term = parEncAxTreeRecNd fT sT (ap1 cor pT) (ap1 cor v1T) (ap1 cor v2T)

    Y2_inner_term : Term
    Y2_inner_term = parEncCongL Pair (ap2 D2_treeRec_fs pT v1T) enc_TR_pv2

    Y2_term : Term
    Y2_term = parEncCongR s Y2_inner_term enc_X

    Y3_inner_term : Term
    Y3_inner_term = parEncCongR Pair (ap2 D2_treeRec_fs pT v2T) cor_TR_pv1

    Y3_term : Term
    Y3_term = parEncCongR s Y3_inner_term enc_X

    XX : Term
    XX = ap2 Pair pT pairT

    VV : Term
    VV = ap2 Pair (ap2 (treeRec f s) pT v1T) (ap2 (treeRec f s) pT v2T)

    Y4_term : Term
    Y4_term = ap2 Df_s XX VV

    --------------------------------------------------------------------
    -- Y1 image via parDispAxTreeRecNd, lifted.

    u1_Y1 : Term
    u1_Y1 = ap2 Pair (reify tagAp2)
              (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                  (ap2 Pair fT sT))
                        (ap2 Pair (ap1 cor pT)
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                              (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))

    u2_Y1 : Term
    u2_Y1 = ap2 Pair (reify tagAp2)
              (ap2 Pair sT
                (ap2 Pair
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair (ap1 cor pT)
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Pair))
                            (ap2 Pair (ap1 cor v1T) (ap1 cor v2T)))))))
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                              (ap2 Pair fT sT))
                                    (ap2 Pair (ap1 cor pT) (ap1 cor v1T))))
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                              (ap2 Pair fT sT))
                                    (ap2 Pair (ap1 cor pT) (ap1 cor v2T)))))))))

    Y1_dl : Deriv (Pv1 imp (Pv2 imp atomic
              (eqn (ap1 thmT Y1_term) (ap2 Pair u1_Y1 u2_Y1))))
    Y1_dl = liftAxiomTwo Pv1 Pv2
              (parDispAxTreeRecNd fT sT (ap1 cor pT) (ap1 cor v1T) (ap1 cor v2T))

    --------------------------------------------------------------------
    -- Y2 image via doubly-lifted CongL then CongR.
    -- Inner: thmTDispCongL Pair enc_TR_pv2 (D2 pT v1T) enc_TR_pv1 cor_TR_pv1
    -- Output: thmT(parEncCongL Pair (D2 pT v1T) enc_TR_pv2)
    --       = (mkAp2T cf2_Pair enc_TR_pv1 enc_TR_pv2,
    --          mkAp2T cf2_Pair cor_TR_pv1 enc_TR_pv2)

    u1_Y2_inner : Term
    u1_Y2_inner = ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair enc_TR_pv1 enc_TR_pv2))

    u2_Y2_inner : Term
    u2_Y2_inner = ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair cor_TR_pv1 enc_TR_pv2))

    Y2_inner_dl : Deriv (Pv1 imp (Pv2 imp atomic
                    (eqn (ap1 thmT Y2_inner_term)
                         (ap2 Pair u1_Y2_inner u2_Y2_inner))))
    Y2_inner_dl = thmTDispCongL_param_doublelifted Pair enc_TR_pv2
                    (ap2 D2_treeRec_fs pT v1T)
                    enc_TR_pv1 cor_TR_pv1
                    Pv1 Pv2 dl_Pv1_atom

    -- Outer: thmTDispCongR s enc_X (Y2_inner) u1_Y2_inner u2_Y2_inner

    u1_Y2 : Term
    u1_Y2 = ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 s))
                (ap2 Pair enc_X u1_Y2_inner))

    u2_Y2 : Term
    u2_Y2 = ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 s))
                (ap2 Pair enc_X u2_Y2_inner))

    Y2_dl : Deriv (Pv1 imp (Pv2 imp atomic
              (eqn (ap1 thmT Y2_term) (ap2 Pair u1_Y2 u2_Y2))))
    Y2_dl = thmTDispCongR_param_doublelifted s enc_X Y2_inner_term
              u1_Y2_inner u2_Y2_inner Pv1 Pv2 Y2_inner_dl

    --------------------------------------------------------------------
    -- Y3 image: parEncCongR Pair (D2 pT v2T) cor_TR_pv1 inside, then CongR.

    u1_Y3_inner : Term
    u1_Y3_inner = ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair cor_TR_pv1 enc_TR_pv2))

    u2_Y3_inner : Term
    u2_Y3_inner = ap2 Pair (reify tagAp2)
                    (ap2 Pair (reify (codeF2 Pair))
                      (ap2 Pair cor_TR_pv1 cor_TR_pv2))

    Y3_inner_dl : Deriv (Pv1 imp (Pv2 imp atomic
                    (eqn (ap1 thmT Y3_inner_term)
                         (ap2 Pair u1_Y3_inner u2_Y3_inner))))
    Y3_inner_dl = thmTDispCongR_param_doublelifted Pair cor_TR_pv1
                    (ap2 D2_treeRec_fs pT v2T)
                    enc_TR_pv2 cor_TR_pv2
                    Pv1 Pv2 dl_Pv2_atom

    u1_Y3 : Term
    u1_Y3 = ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 s))
                (ap2 Pair enc_X u1_Y3_inner))

    u2_Y3 : Term
    u2_Y3 = ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 s))
                (ap2 Pair enc_X u2_Y3_inner))

    Y3_dl : Deriv (Pv1 imp (Pv2 imp atomic
              (eqn (ap1 thmT Y3_term) (ap2 Pair u1_Y3 u2_Y3))))
    Y3_dl = thmTDispCongR_param_doublelifted s enc_X Y3_inner_term
              u1_Y3_inner u2_Y3_inner Pv1 Pv2 Y3_inner_dl

    --------------------------------------------------------------------
    -- Y4 image via proof_s, lifted.
    -- proof_s X V : eqn (thmT (Df_s X V)) (codeFTeq2_gen s X V)
    --             = eqn ... (Pair (mkAp2T sT (cor X)(cor V)) (cor (s X V)))

    u1_Y4_raw : Term
    u1_Y4_raw = ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 s))
                    (ap2 Pair (ap1 cor XX) (ap1 cor VV)))

    u2_Y4_raw : Term
    u2_Y4_raw = ap1 cor (ap2 s XX VV)

    Y4_raw_dl : Deriv (Pv1 imp (Pv2 imp atomic
                  (eqn (ap1 thmT Y4_term) (ap2 Pair u1_Y4_raw u2_Y4_raw))))
    Y4_raw_dl = liftAxiomTwo Pv1 Pv2 (proof_s XX VV)

    --------------------------------------------------------------------
    -- Bridge Y4 image: u1_Y4_raw -> u2_Y3 (the chain hand-off LHS).
    -- u2_Y3 = mkAp2T sT enc_X (mkAp2T cf2_Pair cor_TR_pv1 cor_TR_pv2).
    -- u1_Y4_raw = mkAp2T sT (cor XX) (cor VV).
    -- Need: cor XX -> enc_X  and  cor VV -> mkAp2T cf2_Pair cor_TR_pv1 cor_TR_pv2.

    bridge_corVV : Deriv (atomic (eqn (ap1 cor VV)
                          (ap2 Pair (reify tagAp2)
                            (ap2 Pair (reify (codeF2 Pair))
                              (ap2 Pair cor_TR_pv1 cor_TR_pv2)))))
    bridge_corVV = corOfPair (ap2 (treeRec f s) pT v1T) (ap2 (treeRec f s) pT v2T)

    bridge_corPairv1v2 : Deriv (atomic (eqn (ap1 cor pairT)
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 Pair))
                                    (ap2 Pair (ap1 cor v1T) (ap1 cor v2T))))))
    bridge_corPairv1v2 = corOfPair v1T v2T

    bridge_corXX_step1 : Deriv (atomic (eqn (ap1 cor XX)
                                  (ap2 Pair (reify tagAp2)
                                    (ap2 Pair (reify (codeF2 Pair))
                                      (ap2 Pair (ap1 cor pT) (ap1 cor pairT))))))
    bridge_corXX_step1 = corOfPair pT pairT

    bridge_corXX : Deriv (atomic (eqn (ap1 cor XX) enc_X))
    bridge_corXX =
      ruleTrans bridge_corXX_step1
        (congR Pair (reify tagAp2)
          (congR Pair (reify (codeF2 Pair))
            (congR Pair (ap1 cor pT) bridge_corPairv1v2)))

    -- u1_Y4_raw -> u2_Y3 (= mkAp2T sT enc_X (mkAp2T cf2_Pair cor_TR_pv1 cor_TR_pv2)).
    bridge_u1_Y4 : Deriv (atomic (eqn u1_Y4_raw u2_Y3))
    bridge_u1_Y4 =
      ruleTrans
        (congR Pair (reify tagAp2)
          (congR Pair (reify (codeF2 s))
            (congL Pair (ap1 cor VV) bridge_corXX)))
        (congR Pair (reify tagAp2)
          (congR Pair (reify (codeF2 s))
            (congR Pair enc_X bridge_corVV)))

    -- Bridge Y4's RHS u2_Y4_raw to cor (TR pT pairT) (final RHS of codeFTeq2).
    cor_TR_pair : Term
    cor_TR_pair = ap1 cor (ap2 (treeRec f s) pT pairT)

    bridge_u2_Y4 : Deriv (atomic (eqn u2_Y4_raw cor_TR_pair))
    bridge_u2_Y4 = cong1 cor (ruleSym (axTreeRecNd f s pT v1T v2T))

    -- Lift bridges and apply to Y4_raw_dl.
    Y4_dl : Deriv (Pv1 imp (Pv2 imp atomic
              (eqn (ap1 thmT Y4_term) (ap2 Pair u2_Y3 cor_TR_pair))))
    Y4_dl =
      let
        eq_pair : Deriv (atomic (eqn (ap2 Pair u1_Y4_raw u2_Y4_raw)
                                     (ap2 Pair u2_Y3 cor_TR_pair)))
        eq_pair = ruleTrans (congL Pair u2_Y4_raw bridge_u1_Y4)
                            (congR Pair u2_Y3 bridge_u2_Y4)
        lifted_eq : Deriv (Pv1 imp (Pv2 imp atomic
                      (eqn (ap2 Pair u1_Y4_raw u2_Y4_raw)
                           (ap2 Pair u2_Y3 cor_TR_pair))))
        lifted_eq = liftAxiomTwo Pv1 Pv2 eq_pair
      in liftedRuleTransTwo Pv1 Pv2
           (ap1 thmT Y4_term) (ap2 Pair u1_Y4_raw u2_Y4_raw) (ap2 Pair u2_Y3 cor_TR_pair)
           Y4_raw_dl lifted_eq

    --------------------------------------------------------------------
    -- Chain Y3-Y4 via thmTDispRuleTrans_param_doublelifted.

    Y3Y4_term : Term
    Y3Y4_term = parEncRuleTrans Y3_term Y4_term

    Y3_shape : Deriv (atomic (eqn (ap1 Fst Y3_term) (ap2 Pair O _)))
    Y3_shape = axFst tagCode_congR _

    Y3Y4_dl : Deriv (Pv1 imp (Pv2 imp atomic
                (eqn (ap1 thmT Y3Y4_term) (ap2 Pair u1_Y3 cor_TR_pair))))
    Y3Y4_dl = thmTDispRuleTrans_param_doublelifted
                Y3_term Y4_term
                u1_Y3 u2_Y3 u2_Y3 cor_TR_pair
                _ _
                Pv1 Pv2
                Y3_shape Y3_dl Y4_dl

    --------------------------------------------------------------------
    -- Chain Y2-Y3Y4.

    Y2Y3Y4_term : Term
    Y2Y3Y4_term = parEncRuleTrans Y2_term Y3Y4_term

    Y2_shape : Deriv (atomic (eqn (ap1 Fst Y2_term) (ap2 Pair O _)))
    Y2_shape = axFst tagCode_congR _

    -- u2_Y2 must equal u1_Y3 syntactically for the dispatch to be sound.
    -- u2_Y2 = mkAp2T sT enc_X (mkAp2T cf2_Pair cor_TR_pv1 enc_TR_pv2)
    -- u1_Y3 = mkAp2T sT enc_X (mkAp2T cf2_Pair cor_TR_pv1 enc_TR_pv2)
    -- Yes — same structure, both built from u2_Y2_inner = u1_Y3_inner.

    Y2Y3Y4_dl : Deriv (Pv1 imp (Pv2 imp atomic
                  (eqn (ap1 thmT Y2Y3Y4_term) (ap2 Pair u1_Y2 cor_TR_pair))))
    Y2Y3Y4_dl = thmTDispRuleTrans_param_doublelifted
                  Y2_term Y3Y4_term
                  u1_Y2 u2_Y2 u1_Y3 cor_TR_pair
                  _ _
                  Pv1 Pv2
                  Y2_shape Y2_dl Y3Y4_dl

    --------------------------------------------------------------------
    -- Chain Y1-Y2Y3Y4.

    Y1Y2Y3Y4_term : Term
    Y1Y2Y3Y4_term = parEncRuleTrans Y1_term Y2Y3Y4_term

    Y1_shape : Deriv (atomic (eqn (ap1 Fst Y1_term) (ap2 Pair O _)))
    Y1_shape = axFst tagCode_axTreeRecNd _

    -- u2_Y1 must equal u1_Y2 syntactically.
    -- u2_Y1 = mkAp2T sT enc_X__viaParOutAxTreeRecNd
    --                   (mkAp2T cf2_Pair enc_TR_pv1 enc_TR_pv2)
    -- u1_Y2 = mkAp2T sT enc_X (mkAp2T cf2_Pair enc_TR_pv1 enc_TR_pv2)
    -- where enc_X__viaParOutAxTreeRecNd = mkAp2T cf2_Pair (cor pT) (mkAp2T cf2_Pair (cor v1T)(cor v2T))
    --                                  = enc_X by definition.
    -- Both should be definitionally equal.

    Y1Y2Y3Y4_dl : Deriv (Pv1 imp (Pv2 imp atomic
                    (eqn (ap1 thmT Y1Y2Y3Y4_term) (ap2 Pair u1_Y1 cor_TR_pair))))
    Y1Y2Y3Y4_dl = thmTDispRuleTrans_param_doublelifted
                    Y1_term Y2Y3Y4_term
                    u1_Y1 u2_Y1 u1_Y2 cor_TR_pair
                    _ _
                    Pv1 Pv2
                    Y1_shape Y1_dl Y2Y3Y4_dl

    --------------------------------------------------------------------
    -- Bridge u1_Y1 to encoded LHS of codeFTeq2_TR f s pT pairT.
    --
    -- u1_Y1 = mkAp2T (Pair K (Pair fT sT)) (cor pT)
    --                (mkAp2T cf2_Pair (cor v1T)(cor v2T))
    -- codeFTeq2_TR-LHS = mkAp2T cf2_TR (cor pT)(cor pairT)
    -- Note (Pair K (Pair fT sT)) = cf2_TR definitionally.
    -- Need: mkAp2T cf2_Pair (cor v1T)(cor v2T) -> cor pairT (one corOfPair).

    enc_LHS_TR : Term
    enc_LHS_TR = ap2 Pair (reify tagAp2)
                   (ap2 Pair cf2_TR
                     (ap2 Pair (ap1 cor pT) (ap1 cor pairT)))

    bridge_u1_Y1_to_LHS : Deriv (atomic (eqn u1_Y1 enc_LHS_TR))
    bridge_u1_Y1_to_LHS =
      congR Pair (reify tagAp2)
        (congR Pair cf2_TR
          (congR Pair (ap1 cor pT) (ruleSym bridge_corPairv1v2)))

    --------------------------------------------------------------------
    -- Final image: bridge u1_Y1 to enc_LHS_TR; the result equals
    -- codeFTeq2_TR f s pT pairT.

    chain_dl : Deriv (Pv1 imp (Pv2 imp atomic
                 (eqn (ap1 thmT Y1Y2Y3Y4_term)
                      (ap2 Pair enc_LHS_TR cor_TR_pair))))
    chain_dl =
      let bridge_pair : Deriv (atomic (eqn (ap2 Pair u1_Y1 cor_TR_pair)
                                           (ap2 Pair enc_LHS_TR cor_TR_pair)))
          bridge_pair = congL Pair cor_TR_pair bridge_u1_Y1_to_LHS
          lifted_bridge = liftAxiomTwo Pv1 Pv2 bridge_pair
      in liftedRuleTransTwo Pv1 Pv2
           (ap1 thmT Y1Y2Y3Y4_term)
           (ap2 Pair u1_Y1 cor_TR_pair)
           (ap2 Pair enc_LHS_TR cor_TR_pair)
           Y1Y2Y3Y4_dl lifted_bridge

    --------------------------------------------------------------------
    -- Bridge from thmT(Y1Y2Y3Y4_term) to thmT(D2 pT pairT) via
    -- D2_treeRec_fs_at_Nd.  D2_treeRec_fs_at_Nd gives:
    --   eqn (D2 pT (Pair v1T v2T)) (chain_Df_term pT v1T v2T (D2 pT v1T)(D2 pT v2T))
    -- where chain_Df_term = parEncRuleTrans Y1 (parEncRuleTrans Y2 (parEncRuleTrans Y3 Y4))
    -- = Y1Y2Y3Y4_term (at v1=v1T, v2=v2T, r1=D2 pT v1T, r2=D2 pT v2T).

    chainDf_eq_at_v1v2 : Deriv (atomic (eqn (ap2 D2_treeRec_fs pT pairT)
                                            Y1Y2Y3Y4_term))
    chainDf_eq_at_v1v2 = D2_treeRec_fs_at_Nd pT v1T v2T

    bridge_thmT_LHS : Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs pT pairT))
                                         (ap1 thmT Y1Y2Y3Y4_term)))
    bridge_thmT_LHS = cong1 thmT chainDf_eq_at_v1v2

    chain_at_D2 : Deriv (Pv1 imp (Pv2 imp atomic
                    (eqn (ap1 thmT (ap2 D2_treeRec_fs pT pairT))
                         (ap2 Pair enc_LHS_TR cor_TR_pair))))
    chain_at_D2 =
      liftedRuleTransTwo Pv1 Pv2
        (ap1 thmT (ap2 D2_treeRec_fs pT pairT))
        (ap1 thmT Y1Y2Y3Y4_term)
        (ap2 Pair enc_LHS_TR cor_TR_pair)
        (liftAxiomTwo Pv1 Pv2 bridge_thmT_LHS)
        chain_dl

    --------------------------------------------------------------------
    -- Final: cast atom-form to Ppair via formula_eq.
    -- chain_at_D2 has shape  Pv1 imp (Pv2 imp atomic (eqn (thmT (D2 pT pairT))
    --   (Pair enc_LHS_TR cor_TR_pair))).
    --
    -- (Pair enc_LHS_TR cor_TR_pair) = codeFTeq2_TR f s pT pairT by definition.
    -- So chain_at_D2 : Pv1 imp (Pv2 imp Ppair_concrete).

    chain_concrete : Deriv (Pv1 imp (Pv2 imp Ppair_concrete))
    chain_concrete = chain_at_D2

    -- Cast back: Ppair_concrete = substF zero pairT P_Th12_treeRec via formula_eq.

    basePair_proof : Deriv (Pv1 imp (Pv2 imp Ppair))
    basePair_proof =
      eqSubst (\ Q -> Deriv (Pv1 imp (Pv2 imp Q)))
              (eqSym (formula_eq pairT)) chain_concrete

  ----------------------------------------------------------------------
  -- Step 4: universal closure via ruleIndBT.

  D_correct2_treeRec_fs_univ : Deriv P_Th12_treeRec
  D_correct2_treeRec_fs_univ =
    ruleIndBT P_Th12_treeRec v1IndNat v2IndNat
              base_O_subst BasePair.basePair_proof

  ----------------------------------------------------------------------
  -- Step 5: universal wrapper via Pair-encoding ruleInst trick.
  -- Mirrors BRA/Thm12/Parts/TreeRec.agda lines 660-1046.

  private
    bigNat : Nat
    bigNat = suc (suc zero)

    bigT : Term
    bigT = var bigNat

    fstBigT : Term
    fstBigT = ap1 Fst bigT

    sndBigT : Term
    sndBigT = ap1 Snd bigT

    P_pair_at : Term -> Term -> Formula
    P_pair_at pT' xT' =
      atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs pT' xT'))
                  (codeFTeq2_treeRec_fs f s pT' xT'))

    -- Step 2 substF eq: subst (suc zero) fstBigT (P_concrete_at sndBigT) = P_pair_at fstBigT sndBigT.

    step2_lhs_eq :
      Eq (subst (suc zero) fstBigT
            (ap1 thmT (ap2 D2_treeRec_fs (var (suc zero)) sndBigT)))
         (ap1 thmT (ap2 D2_treeRec_fs fstBigT sndBigT))
    step2_lhs_eq =
      eqTrans (eqCong (\ F -> ap1 F (ap2 (substF2 (suc zero) fstBigT D2_treeRec_fs)
                                          fstBigT sndBigT))
                       (thClosed (suc zero) fstBigT))
              (eqCong (\ D -> ap1 thmT (ap2 D fstBigT sndBigT))
                       (D2_treeRec_fs_closed (suc zero) fstBigT))

    step2_corPair_eq :
      Eq (subst (suc zero) fstBigT
            (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor sndBigT)))
         (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))
    step2_corPair_eq =
      eqTrans (eqCong (\ C -> ap2 Pair (ap1 C fstBigT)
                                        (ap1 (substF1 (suc zero) fstBigT cor) sndBigT))
                       (cor_closed (suc zero) fstBigT))
              (eqCong (\ C -> ap2 Pair (ap1 cor fstBigT) (ap1 C sndBigT))
                       (cor_closed (suc zero) fstBigT))

    step2_secondPair_eq :
      Eq (subst (suc zero) fstBigT
            (ap2 Pair (reify (codeF2 (treeRec f s)))
                      (ap2 Pair (ap1 cor (var (suc zero))) (ap1 cor sndBigT))))
         (ap2 Pair (reify (codeF2 (treeRec f s)))
                   (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT)))
    step2_secondPair_eq =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst (suc zero) fstBigT
                                  (ap2 Pair (ap1 cor (var (suc zero)))
                                            (ap1 cor sndBigT))))
                       (subst_reify (suc zero) fstBigT (codeF2 (treeRec f s)) (codeF2_isValue (treeRec f s))))
              (eqCong (\ Q -> ap2 Pair (reify (codeF2 (treeRec f s))) Q)
                       step2_corPair_eq)

    step2_encoded_lhs_eq :
      Eq (subst (suc zero) fstBigT
            (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 (treeRec f s)))
                                (ap2 Pair (ap1 cor (var (suc zero)))
                                          (ap1 cor sndBigT)))))
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                             (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
    step2_encoded_lhs_eq =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst (suc zero) fstBigT
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (var (suc zero)))
                                                      (ap1 cor sndBigT)))))
                       (subst_reify (suc zero) fstBigT tagAp2 tagAp2_isValue))
              (eqCong (\ Q -> ap2 Pair (reify tagAp2) Q) step2_secondPair_eq)

    step2_corTreeRec_eq :
      Eq (subst (suc zero) fstBigT
            (ap1 cor (ap2 (treeRec f s) (var (suc zero)) sndBigT)))
         (ap1 cor (ap2 (treeRec f s) fstBigT sndBigT))
    step2_corTreeRec_eq =
      eqTrans (eqCong (\ C -> ap1 C (ap2 (substF2 (suc zero) fstBigT (treeRec f s))
                                          fstBigT sndBigT))
                       (cor_closed (suc zero) fstBigT))
              (eqCong (\ TR -> ap1 cor (ap2 TR fstBigT sndBigT))
                       (treeRec_fs_closed (suc zero) fstBigT))

    step2_rhs_eq :
      Eq (subst (suc zero) fstBigT
            (codeFTeq2_treeRec_fs f s (var (suc zero)) sndBigT))
         (codeFTeq2_treeRec_fs f s fstBigT sndBigT)
    step2_rhs_eq =
      eqTrans (eqCong (\ X -> ap2 Pair X
                                (subst (suc zero) fstBigT
                                  (ap1 cor (ap2 (treeRec f s) (var (suc zero)) sndBigT))))
                       step2_encoded_lhs_eq)
              (eqCong (\ Y -> ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
                                Y)
                       step2_corTreeRec_eq)

    step2_formula_eq :
      Eq (substF (suc zero) fstBigT (P_concrete_at sndBigT))
         (P_pair_at fstBigT sndBigT)
    step2_formula_eq =
      eqTrans (eqCong (\ L -> atomic (eqn L
                                (subst (suc zero) fstBigT
                                  (codeFTeq2_treeRec_fs f s (var (suc zero)) sndBigT))))
                       step2_lhs_eq)
              (eqCong (\ R -> atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs fstBigT sndBigT)) R))
                       step2_rhs_eq)

  -- Step 3 substF eq: subst bigNat pT (P_pair_at fstBigT sndBigT) = P_pair_at (Fst pT)(Snd pT).

  private
    step3_FstBig_eq : (pT' : Term) ->
      Eq (subst bigNat pT' fstBigT) (ap1 Fst pT')
    step3_FstBig_eq pT' =
      eqCong (\ F -> ap1 F pT') (Fun1_closed bigNat pT' Fst)

    step3_SndBig_eq : (pT' : Term) ->
      Eq (subst bigNat pT' sndBigT) (ap1 Snd pT')
    step3_SndBig_eq pT' =
      eqCong (\ F -> ap1 F pT') (Fun1_closed bigNat pT' Snd)

    step3_lhs_eq : (pT' : Term) ->
      Eq (subst bigNat pT' (ap1 thmT (ap2 D2_treeRec_fs fstBigT sndBigT)))
         (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pT') (ap1 Snd pT')))
    step3_lhs_eq pT' =
      eqTrans (eqCong (\ F -> ap1 F (ap2 (substF2 bigNat pT' D2_treeRec_fs)
                                          (subst bigNat pT' fstBigT)
                                          (subst bigNat pT' sndBigT)))
                       (thClosed bigNat pT'))
              (eqTrans (eqCong (\ D -> ap1 thmT (ap2 D
                                          (subst bigNat pT' fstBigT)
                                          (subst bigNat pT' sndBigT)))
                                (D2_treeRec_fs_closed bigNat pT'))
                       (eqTrans (eqCong (\ A -> ap1 thmT (ap2 D2_treeRec_fs A
                                                  (subst bigNat pT' sndBigT)))
                                          (step3_FstBig_eq pT'))
                                (eqCong (\ B -> ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pT') B))
                                          (step3_SndBig_eq pT'))))

    step3_corPair_eq : (pT' : Term) ->
      Eq (subst bigNat pT' (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT)))
         (ap2 Pair (ap1 cor (ap1 Fst pT')) (ap1 cor (ap1 Snd pT')))
    step3_corPair_eq pT' =
      eqTrans (eqCong (\ C -> ap2 Pair (ap1 C (subst bigNat pT' fstBigT))
                                        (ap1 (substF1 bigNat pT' cor) (subst bigNat pT' sndBigT)))
                       (cor_closed bigNat pT'))
              (eqTrans (eqCong (\ C -> ap2 Pair (ap1 cor (subst bigNat pT' fstBigT))
                                                  (ap1 C (subst bigNat pT' sndBigT)))
                                (cor_closed bigNat pT'))
                       (eqTrans (eqCong (\ A -> ap2 Pair (ap1 cor A)
                                                          (ap1 cor (subst bigNat pT' sndBigT)))
                                          (step3_FstBig_eq pT'))
                                (eqCong (\ B -> ap2 Pair (ap1 cor (ap1 Fst pT')) (ap1 cor B))
                                          (step3_SndBig_eq pT'))))

    step3_secondPair_eq : (pT' : Term) ->
      Eq (subst bigNat pT'
            (ap2 Pair (reify (codeF2 (treeRec f s)))
                      (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
         (ap2 Pair (reify (codeF2 (treeRec f s)))
                   (ap2 Pair (ap1 cor (ap1 Fst pT')) (ap1 cor (ap1 Snd pT'))))
    step3_secondPair_eq pT' =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst bigNat pT'
                                  (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT))))
                       (subst_reify bigNat pT' (codeF2 (treeRec f s)) (codeF2_isValue (treeRec f s))))
              (eqCong (\ Q -> ap2 Pair (reify (codeF2 (treeRec f s))) Q)
                       (step3_corPair_eq pT'))

    step3_encoded_lhs_eq : (pT' : Term) ->
      Eq (subst bigNat pT'
            (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 (treeRec f s)))
                                (ap2 Pair (ap1 cor fstBigT) (ap1 cor sndBigT)))))
         (ap2 Pair (reify tagAp2)
                   (ap2 Pair (reify (codeF2 (treeRec f s)))
                             (ap2 Pair (ap1 cor (ap1 Fst pT')) (ap1 cor (ap1 Snd pT')))))
    step3_encoded_lhs_eq pT' =
      eqTrans (eqCong (\ T -> ap2 Pair T
                                (subst bigNat pT'
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor fstBigT)
                                                      (ap1 cor sndBigT)))))
                       (subst_reify bigNat pT' tagAp2 tagAp2_isValue))
              (eqCong (\ Q -> ap2 Pair (reify tagAp2) Q) (step3_secondPair_eq pT'))

    step3_corTreeRec_eq : (pT' : Term) ->
      Eq (subst bigNat pT' (ap1 cor (ap2 (treeRec f s) fstBigT sndBigT)))
         (ap1 cor (ap2 (treeRec f s) (ap1 Fst pT') (ap1 Snd pT')))
    step3_corTreeRec_eq pT' =
      eqTrans (eqCong (\ C -> ap1 C (ap2 (substF2 bigNat pT' (treeRec f s))
                                          (subst bigNat pT' fstBigT)
                                          (subst bigNat pT' sndBigT)))
                       (cor_closed bigNat pT'))
              (eqTrans (eqCong (\ TR -> ap1 cor (ap2 TR
                                          (subst bigNat pT' fstBigT)
                                          (subst bigNat pT' sndBigT)))
                                (treeRec_fs_closed bigNat pT'))
                       (eqTrans (eqCong (\ A -> ap1 cor (ap2 (treeRec f s) A
                                                  (subst bigNat pT' sndBigT)))
                                          (step3_FstBig_eq pT'))
                                (eqCong (\ B -> ap1 cor (ap2 (treeRec f s) (ap1 Fst pT') B))
                                          (step3_SndBig_eq pT'))))

    step3_rhs_eq : (pT' : Term) ->
      Eq (subst bigNat pT' (codeFTeq2_treeRec_fs f s fstBigT sndBigT))
         (codeFTeq2_treeRec_fs f s (ap1 Fst pT') (ap1 Snd pT'))
    step3_rhs_eq pT' =
      eqTrans (eqCong (\ X -> ap2 Pair X
                                (subst bigNat pT'
                                  (ap1 cor (ap2 (treeRec f s) fstBigT sndBigT))))
                       (step3_encoded_lhs_eq pT'))
              (eqCong (\ Y -> ap2 Pair
                                (ap2 Pair (reify tagAp2)
                                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                                            (ap2 Pair (ap1 cor (ap1 Fst pT'))
                                                      (ap1 cor (ap1 Snd pT')))))
                                Y)
                       (step3_corTreeRec_eq pT'))

    step3_formula_eq : (pT' : Term) ->
      Eq (substF bigNat pT' (P_pair_at fstBigT sndBigT))
         (P_pair_at (ap1 Fst pT') (ap1 Snd pT'))
    step3_formula_eq pT' =
      eqTrans (eqCong (\ L -> atomic (eqn L
                                (subst bigNat pT'
                                  (codeFTeq2_treeRec_fs f s fstBigT sndBigT))))
                       (step3_lhs_eq pT'))
              (eqCong (\ R -> atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pT')
                                                                       (ap1 Snd pT'))) R))
                       (step3_rhs_eq pT'))

  -- Final Deriv-level bridge: P_pair_at (Fst (Pair p x))(Snd (Pair p x)) ~~> P_pair_at p x.

  private
    pairBridgeEqLHS : (p x : Term) ->
      Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst (ap2 Pair p x))
                                                        (ap1 Snd (ap2 Pair p x))))
                          (ap1 thmT (ap2 D2_treeRec_fs p x))))
    pairBridgeEqLHS p x =
      cong1 thmT
        (ruleTrans (congL D2_treeRec_fs (ap1 Snd (ap2 Pair p x)) (axFst p x))
                   (congR D2_treeRec_fs p (axSnd p x)))

    pairBridgeEqCorP : (p x : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair p x))) (ap1 cor p)))
    pairBridgeEqCorP p x = cong1 cor (axFst p x)

    pairBridgeEqCorX : (p x : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap1 Snd (ap2 Pair p x))) (ap1 cor x)))
    pairBridgeEqCorX p x = cong1 cor (axSnd p x)

    pairBridgeEqCorTR : (p x : Term) ->
      Deriv (atomic (eqn (ap1 cor (ap2 (treeRec f s) (ap1 Fst (ap2 Pair p x))
                                                       (ap1 Snd (ap2 Pair p x))))
                          (ap1 cor (ap2 (treeRec f s) p x))))
    pairBridgeEqCorTR p x =
      cong1 cor
        (ruleTrans (congL (treeRec f s) (ap1 Snd (ap2 Pair p x)) (axFst p x))
                   (congR (treeRec f s) p (axSnd p x)))

    pairBridgeEncoded : (p x : Term) ->
      Deriv (atomic (eqn
        (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                            (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair p x)))
                                      (ap1 cor (ap1 Snd (ap2 Pair p x))))))
        (ap2 Pair (reify tagAp2)
                  (ap2 Pair (reify (codeF2 (treeRec f s)))
                            (ap2 Pair (ap1 cor p) (ap1 cor x))))))
    pairBridgeEncoded p x =
      let inner_corPair :
              Deriv (atomic (eqn
                (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair p x)))
                          (ap1 cor (ap1 Snd (ap2 Pair p x))))
                (ap2 Pair (ap1 cor p) (ap1 cor x))))
          inner_corPair =
            ruleTrans (congL Pair (ap1 cor (ap1 Snd (ap2 Pair p x))) (pairBridgeEqCorP p x))
                      (congR Pair (ap1 cor p) (pairBridgeEqCorX p x))

          second_pair :
              Deriv (atomic (eqn
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor (ap1 Fst (ap2 Pair p x)))
                                    (ap1 cor (ap1 Snd (ap2 Pair p x)))))
                (ap2 Pair (reify (codeF2 (treeRec f s)))
                          (ap2 Pair (ap1 cor p) (ap1 cor x)))))
          second_pair = congR Pair (reify (codeF2 (treeRec f s))) inner_corPair
      in congR Pair (reify tagAp2) second_pair

    pairBridgeRHS : (p x : Term) ->
      Deriv (atomic (eqn (codeFTeq2_treeRec_fs f s
                            (ap1 Fst (ap2 Pair p x)) (ap1 Snd (ap2 Pair p x)))
                          (codeFTeq2_treeRec_fs f s p x)))
    pairBridgeRHS p x =
      ruleTrans (congL Pair
                   (ap1 cor (ap2 (treeRec f s) (ap1 Fst (ap2 Pair p x))
                                                 (ap1 Snd (ap2 Pair p x))))
                   (pairBridgeEncoded p x))
                (congR Pair
                   (ap2 Pair (reify tagAp2)
                             (ap2 Pair (reify (codeF2 (treeRec f s)))
                                       (ap2 Pair (ap1 cor p) (ap1 cor x))))
                   (pairBridgeEqCorTR p x))

  D_correct2_treeRec_fs : (p x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 D2_treeRec_fs p x))
                       (codeFTeq2_treeRec_fs f s p x)))
  D_correct2_treeRec_fs p x =
    let
        -- Stage 1: ruleInst zero -> sndBigT.
        stage1_raw : Deriv (substF zero sndBigT P_Th12_treeRec)
        stage1_raw = ruleInst zero sndBigT D_correct2_treeRec_fs_univ

        stage1 : Deriv (P_concrete_at sndBigT)
        stage1 = eqSubst Deriv (formula_eq sndBigT) stage1_raw

        -- Stage 2: ruleInst (suc zero) -> fstBigT.
        stage2_raw : Deriv (substF (suc zero) fstBigT (P_concrete_at sndBigT))
        stage2_raw = ruleInst (suc zero) fstBigT stage1

        stage2 : Deriv (P_pair_at fstBigT sndBigT)
        stage2 = eqSubst Deriv step2_formula_eq stage2_raw

        -- Stage 3: ruleInst bigNat -> Pair p x.
        pairPX : Term
        pairPX = ap2 Pair p x

        stage3_raw : Deriv (substF bigNat pairPX (P_pair_at fstBigT sndBigT))
        stage3_raw = ruleInst bigNat pairPX stage2

        stage3 : Deriv (P_pair_at (ap1 Fst pairPX) (ap1 Snd pairPX))
        stage3 = eqSubst Deriv (step3_formula_eq pairPX) stage3_raw

        bridge_lhs_back : Deriv (atomic (eqn
          (ap1 thmT (ap2 D2_treeRec_fs p x))
          (ap1 thmT (ap2 D2_treeRec_fs (ap1 Fst pairPX) (ap1 Snd pairPX)))))
        bridge_lhs_back = ruleSym (pairBridgeEqLHS p x)

        bridge_rhs_forward : Deriv (atomic (eqn
          (codeFTeq2_treeRec_fs f s (ap1 Fst pairPX) (ap1 Snd pairPX))
          (codeFTeq2_treeRec_fs f s p x)))
        bridge_rhs_forward = pairBridgeRHS p x

    in ruleTrans bridge_lhs_back (ruleTrans stage3 bridge_rhs_forward)
