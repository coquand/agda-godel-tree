{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.RecV2
--
-- Phase 7c proof-of-concept refactor of Parts/Rec.Construction.
--
-- New design uses BRA's Rec primitive to define D_Rec_zs:
--   D_Rec_zs = Rec (parEncAxRecLf zT sT) D_Rec_zs_step
--
-- This avoids the Phase 7c structural circularity that affected the
-- old design's parametric D_Rec_NN_fun.  The step Fun2 has no
-- structural reference to D_Rec_zs; cross-IH Term values flow via
-- axRecNd's runtime  recs  argument.
--
-- This file demonstrates:
--   (a) D_Rec_zs is a closed Fun1 (no parameters beyond z, s).
--   (b) The leaf-case correctness proof works directly.
--   (c) The successor-case ConstructionV2 takes cross-IH Derivs as
--       Agda-level parameters (not as Fun1/Fun2 sub-trees), which the
--       Phase 7 mutual recursion supplies via recursive D_correct calls
--       at sub-Term args.
--
-- Successor-case full proof construction (the chain) is deferred --
-- this file proves the LL case + sets up the NN case signature.

module BRA2.Thm12.Parts.RecV2 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxRecLf ; tagAxRecNd
                              ; tagRuleTrans ; tagCongL ; tagCongR)
open import BRA2.Thm.ThmT
  using (thmT ; tagCode_axRecNd ; tagCode_ruleTrans
       ; tagCode_congL ; tagCode_congR)
open import BRA2.Thm12.Param.AxRecLf
  using (parEncAxRecLf ; parOutAxRecLf ; parDispAxRecLf)
open import BRA2.Thm12.Param.AxRecNd
  using (parEncAxRecNd ; parOutAxRecNd ; parDispAxRecNd)
open import BRA2.Thm12.Param.RuleTrans
  using (parEncRuleTrans ; parDispRuleTrans)
open import BRA2.Thm12.Param.CongL
  using (parEncCongL ; parOutCongL ; parDispCongL)
open import BRA2.Thm12.Param.CongR
  using (parEncCongR ; parOutCongR ; parDispCongR)

------------------------------------------------------------------------
-- The codeFTeq1 spec for Rec z s.

codeFTeq1_Rec_zs : (z : Term) (s : Fun2) -> Term -> Term
codeFTeq1_Rec_zs z s x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 (Rec z s))) (ap1 cor x)))
    (ap1 cor (ap1 (Rec z s) x))

------------------------------------------------------------------------
-- New Construction module.
--
-- Parameters: z : Term, s : Fun2, plus z_corLemma (same as old design).
-- Output: D_Rec_zs as a Rec-primitive expression, plus the leaf
-- correctness lemma.
--
-- Successor-case correctness (with cross-IH parameters) shown as a
-- type signature only -- the chain proof construction is the next step.

module ConstructionV2
  (z : Term)
  (s : Fun2)
  (D2_s : Fun2)
  (z_corLemma : Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))
  where

  private
    zT : Term
    zT = reify (code z)

    sT : Term
    sT = reify (codeF2 s)

    ----------------------------------------------------------------
    -- Step Fun2 building blocks.
    --
    -- D_Rec_zs_step takes (orig, recs) where:
    --   orig = Pair a b   (the input pair to D_Rec_zs)
    --   recs = Pair recA recB
    --     with  recA = ap1 D_Rec_zs a , recB = ap1 D_Rec_zs b
    -- (supplied by axRecNd's runtime evaluation).
    --
    -- The step has NO STRUCTURAL REFERENCE TO D_Rec_zs; cross-IH Term
    -- values flow via the recs slot.

    -- Projection helpers (each is a Fun2 returning a specific value).
    cor_a : Fun2
    cor_a = Lift (Comp cor Fst)            -- cor(Fst orig) = cor a

    cor_b : Fun2
    cor_b = Lift (Comp cor Snd)            -- cor(Snd orig) = cor b

    proj_recA : Fun2
    proj_recA = Post (Comp Fst Snd) Pair    -- Fst recs = recA

    proj_recB : Fun2
    proj_recB = Post (Comp Snd Snd) Pair    -- Snd recs = recB

    -- (Rec z s) a / (Rec z s) b   : actual Rec-evaluations on a/b.
    -- Used in y4's V argument.
    rec_a : Fun2
    rec_a = Lift (Comp (Rec z s) Fst)       -- (Rec z s) a

    rec_b : Fun2
    rec_b = Lift (Comp (Rec z s) Snd)       -- (Rec z s) b

    -- Generic Pair-builder and constant-Fun2 helpers.
    kConst : Term -> Fun2
    kConst K = Lift (KT K)

    pairBld : Fun2 -> Fun2 -> Fun2
    pairBld f g = Fan f g Pair

    ----------------------------------------------------------------
    -- y1 = parEncAxRecNd zT sT (cor a) (cor b)
    --    = Pair tagCode_axRecNd (Pair zT (Pair sT (Pair (cor a) (cor b))))

    y1_part : Fun2
    y1_part = pairBld (kConst tagCode_axRecNd)
                (pairBld (kConst zT)
                  (pairBld (kConst sT)
                    (pairBld cor_a cor_b)))

    ----------------------------------------------------------------
    -- Sub-builders for V_enc rewriting.

    -- enc_rec_a : encoded form of (Rec z s)(cor a) used as encRec_a
    --           = Pair tagAp1 (Pair codeF1_(Rec z s) (cor a))
    enc_rec_a : Fun2
    enc_rec_a = pairBld (kConst (reify tagAp1))
                  (pairBld (kConst (reify (codeF1 (Rec z s))))
                    cor_a)

    enc_rec_b : Fun2
    enc_rec_b = pairBld (kConst (reify tagAp1))
                  (pairBld (kConst (reify (codeF1 (Rec z s))))
                    cor_b)

    -- X_enc = encoded form of "Pair (cor a) (cor b)"
    --       = Pair tagAp2 (Pair codeF2_Pair (Pair (cor a) (cor b)))
    X_enc_part : Fun2
    X_enc_part = pairBld (kConst (reify tagAp2))
                   (pairBld (kConst (reify (codeF2 Pair)))
                     (pairBld cor_a cor_b))

    -- cor_Rec_a : cor((Rec z s) a)  -- the RHS of recA's spec.
    cor_Rec_a : Fun2
    cor_Rec_a = Lift (Comp cor (Comp (Rec z s) Fst))

    cor_Rec_b : Fun2
    cor_Rec_b = Lift (Comp cor (Comp (Rec z s) Snd))

    ----------------------------------------------------------------
    -- y2: rewrite encRec_a -> cor_Rec_a inside V_enc, then lift through
    --     s-encoding via parEncCongR s.
    --
    -- y_v_y2_layer1 = parEncCongL Pair recA enc_rec_b
    --   proves Pair encRec_a encRec_b = Pair cor_Rec_a encRec_b
    y_v_y2_layer1 : Fun2
    y_v_y2_layer1 = pairBld (kConst tagCode_congL)
                      (pairBld (kConst (reify (codeF2 Pair)))
                        (pairBld proj_recA enc_rec_b))

    -- y_v_y2_layer2 = parEncCongR Pair Layer1 codeF2_Pair
    y_v_y2_layer2 : Fun2
    y_v_y2_layer2 = pairBld (kConst tagCode_congR)
                      (pairBld (kConst (reify (codeF2 Pair)))
                        (pairBld y_v_y2_layer1
                                 (kConst (reify (codeF2 Pair)))))

    -- y_v_y2_layer3 = parEncCongR Pair Layer2 tagAp2
    --   proves V_enc_old = V_enc_y2 (after a-rewrite)
    y_v_y2_layer3 : Fun2
    y_v_y2_layer3 = pairBld (kConst tagCode_congR)
                      (pairBld (kConst (reify (codeF2 Pair)))
                        (pairBld y_v_y2_layer2
                                 (kConst (reify tagAp2))))

    -- y2 = parEncCongR s y_v_y2_layer3 X_enc
    --   proves s(X, V_enc_old) = s(X, V_enc_y2)  encoded.
    y2_part : Fun2
    y2_part = pairBld (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 s)))
                  (pairBld y_v_y2_layer3 X_enc_part))

    ----------------------------------------------------------------
    -- y3: rewrite encRec_b -> cor_Rec_b inside V_enc (with first slot
    -- already cor_Rec_a), then lift through s-encoding.
    --
    -- y_v_y3_layer1 = parEncCongR Pair recB cor_Rec_a
    --   proves Pair cor_Rec_a encRec_b = Pair cor_Rec_a cor_Rec_b
    y_v_y3_layer1 : Fun2
    y_v_y3_layer1 = pairBld (kConst tagCode_congR)
                      (pairBld (kConst (reify (codeF2 Pair)))
                        (pairBld proj_recB cor_Rec_a))

    y_v_y3_layer2 : Fun2
    y_v_y3_layer2 = pairBld (kConst tagCode_congR)
                      (pairBld (kConst (reify (codeF2 Pair)))
                        (pairBld y_v_y3_layer1
                                 (kConst (reify (codeF2 Pair)))))

    y_v_y3_layer3 : Fun2
    y_v_y3_layer3 = pairBld (kConst tagCode_congR)
                      (pairBld (kConst (reify (codeF2 Pair)))
                        (pairBld y_v_y3_layer2
                                 (kConst (reify tagAp2))))

    y3_part : Fun2
    y3_part = pairBld (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 s)))
                  (pairBld y_v_y3_layer3 X_enc_part))

    ----------------------------------------------------------------
    -- y4: D2_s applied at (orig, Pair (Rec a) (Rec b)).
    --   Runtime: ap2 D2_s orig (Pair (Rec a) (Rec b))
    --
    -- Built as Fan (orig-projector) (V-builder) D2_s, where:
    --   orig-projector returns orig  (use Lift I)
    --   V-builder returns Pair (Rec a) (Rec b)  (pairBld rec_a rec_b)

    y4_part : Fun2
    y4_part = Fan (Lift I) (pairBld rec_a rec_b) D2_s

    ----------------------------------------------------------------
    -- Compose: chain_term = parEncRuleTrans y1 (parEncRuleTrans y2
    --                         (parEncRuleTrans y3 y4))

    inner_rt2_part : Fun2
    inner_rt2_part = pairBld (kConst tagCode_ruleTrans)
                       (pairBld y3_part y4_part)

    inner_rt1_part : Fun2
    inner_rt1_part = pairBld (kConst tagCode_ruleTrans)
                       (pairBld y2_part inner_rt2_part)

    D_Rec_zs_step : Fun2
    D_Rec_zs_step = pairBld (kConst tagCode_ruleTrans)
                      (pairBld y1_part inner_rt1_part)

  D_Rec_zs : Fun1
  D_Rec_zs = Rec (parEncAxRecLf zT sT) D_Rec_zs_step

  ------------------------------------------------------------------
  -- Leaf-case reduction.  By  axRecLf : (Rec z' s')(O) = z' .

  D_Rec_zs_reduce_O : Deriv (atomic (eqn (ap1 D_Rec_zs O)
                                          (parEncAxRecLf zT sT)))
  D_Rec_zs_reduce_O = axRecLf (parEncAxRecLf zT sT) D_Rec_zs_step

  ------------------------------------------------------------------
  -- Bridge at O: parOutAxRecLf zT sT  ->  codeFTeq1_Rec_zs z s O .
  -- Same as old Construction.bridgeO, copied here for completeness.

  bridgeO : Deriv (atomic (eqn (parOutAxRecLf zT sT) (codeFTeq1_Rec_zs z s O)))
  bridgeO =
    let cor_O : Deriv (atomic (eqn (ap1 cor O) O))
        cor_O = axRecLf stepCor
        recLf_eq : Deriv (atomic (eqn (ap1 (Rec z s) O) z))
        recLf_eq = axRecLf z s
        cor_recLf_zT : Deriv (atomic (eqn (ap1 cor (ap1 (Rec z s) O)) zT))
        cor_recLf_zT = ruleTrans (cong1 cor recLf_eq) z_corLemma

        step1 : Deriv (atomic (eqn (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                       (ap2 Pair zT sT))
                                              O)
                                    (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                         (ap2 Pair zT sT))
                                              (ap1 cor O))))
        step1 = congR Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                      (ap2 Pair zT sT))
                          (ruleSym cor_O)

        step2 : Deriv (atomic (eqn (ap2 Pair (reify tagAp1)
                                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                          (ap2 Pair zT sT))
                                                O))
                                    (ap2 Pair (reify tagAp1)
                                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                          (ap2 Pair zT sT))
                                                (ap1 cor O)))))
        step2 = congR Pair (reify tagAp1) step1

        step3 : Deriv (atomic (eqn (parOutAxRecLf zT sT)
                                    (ap2 Pair
                                      (ap2 Pair (reify tagAp1)
                                        (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                            (ap2 Pair zT sT))
                                                  (ap1 cor O)))
                                      zT)))
        step3 = congL Pair zT step2

        step4 : Deriv (atomic (eqn (ap2 Pair
                                      (ap2 Pair (reify tagAp1)
                                        (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                            (ap2 Pair zT sT))
                                                  (ap1 cor O)))
                                      zT)
                                    (codeFTeq1_Rec_zs z s O)))
        step4 = congR Pair _ (ruleSym cor_recLf_zT)

    in ruleTrans step3 step4

  ------------------------------------------------------------------
  -- Leaf-case correctness.  Combines reduction + dispatch + bridge.

  D_correct_Rec_zs_O : Deriv (atomic (eqn (ap1 thmT (ap1 D_Rec_zs O))
                                           (codeFTeq1_Rec_zs z s O)))
  D_correct_Rec_zs_O =
    let r_thmT = cong1 thmT D_Rec_zs_reduce_O
        r_disp = parDispAxRecLf zT sT
    in ruleTrans r_thmT (ruleTrans r_disp bridgeO)

  ------------------------------------------------------------------
  -- Successor-case correctness signature (cross-IH parametric).
  --
  -- The Pair-case proof takes:
  --   a, b : Term  (the sub-pair components)
  --   cross_IH_a : Deriv (D_correct at a)
  --   cross_IH_b : Deriv (D_correct at b)
  --   cross_IH_s : (x v : Term) -> Deriv (D_correct2 s at x v)
  --       (the IH on the "step" Fun2 supplied by Phase 7's mutual recursion
  --        via D_correct2 s)
  --
  -- These cross-IHs are AGDA-LEVEL Deriv values supplied by the Phase 7
  -- consumer's mutual recursion, NOT Hilbert-level imp-elim.  No
  -- deduction theorem needed.
  --
  -- The actual proof construction uses parDispRuleTrans + parDispCongL/
  -- parDispCongR + cross-IH Deriv applications to match the chain
  -- produced by D_Rec_zs_step.  This is the ~200 LoC body deferred.

  ------------------------------------------------------------------
  -- Step 3 helper: outer reduction of D_Rec_zs at Pair a b.
  --
  -- By axRecNd, D_Rec_zs (Pair a b) reduces to D_Rec_zs_step applied
  -- at runtime (orig, recs) where recs = Pair (D_Rec_zs a) (D_Rec_zs b).
  -- This is just one axRecNd invocation.

  D_Rec_zs_outer_red : (a b : Term) ->
    Deriv (atomic (eqn (ap1 D_Rec_zs (ap2 Pair a b))
                       (ap2 D_Rec_zs_step (ap2 Pair a b)
                          (ap2 Pair (ap1 D_Rec_zs a) (ap1 D_Rec_zs b)))))
  D_Rec_zs_outer_red a b = axRecNd (parEncAxRecLf zT sT) D_Rec_zs_step a b

  ------------------------------------------------------------------
  -- Step 3 helper: kConst reduction.
  --
  -- ap2 (kConst (reify v)) orig recs = reify v.
  -- Used pervasively in reducing the chain Fun2's combinator structure.

  kConst_red : (v : Tree) (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (kConst (reify v)) orig recs) (reify v)))
  kConst_red v orig recs =
    ruleTrans (axLift (KT (reify v)) orig recs) (axKT v orig)

  ------------------------------------------------------------------
  -- Step 3 helper: pairBld reduction.
  --
  -- ap2 (pairBld f g) orig recs = Pair (ap2 f orig recs) (ap2 g orig recs).

  pairBld_red : (f g : Fun2) (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 (pairBld f g) orig recs)
                       (ap2 Pair (ap2 f orig recs) (ap2 g orig recs))))
  pairBld_red f g orig recs = axFan f g Pair orig recs

  ------------------------------------------------------------------
  -- Step 3 helper: outer-shell reduction of D_Rec_zs_step.
  --
  -- ap2 D_Rec_zs_step orig recs
  --   = Pair tagCode_ruleTrans (Pair (ap2 y1_part orig recs)
  --                                  (ap2 inner_rt1_part orig recs))
  --
  -- Just unfolds the outermost pairBld; doesn't unfold y1_part etc.

  D_Rec_zs_step_outer : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 D_Rec_zs_step orig recs)
                       (ap2 Pair tagCode_ruleTrans
                          (ap2 Pair (ap2 y1_part orig recs)
                                    (ap2 inner_rt1_part orig recs)))))
  D_Rec_zs_step_outer orig recs =
    let r1 = pairBld_red (kConst tagCode_ruleTrans)
                         (pairBld y1_part inner_rt1_part) orig recs
        r2 = kConst_red (natCode tagRuleTrans) orig recs
        r3 = pairBld_red y1_part inner_rt1_part orig recs
    in ruleTrans r1
         (ruleTrans (congL Pair (ap2 (pairBld y1_part inner_rt1_part) orig recs)
                                r2)
                    (congR Pair tagCode_ruleTrans r3))

  ------------------------------------------------------------------
  -- Step 3 helper: outer-shell reduction of inner_rt1_part.

  inner_rt1_outer : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 inner_rt1_part orig recs)
                       (ap2 Pair tagCode_ruleTrans
                          (ap2 Pair (ap2 y2_part orig recs)
                                    (ap2 inner_rt2_part orig recs)))))
  inner_rt1_outer orig recs =
    let r1 = pairBld_red (kConst tagCode_ruleTrans)
                         (pairBld y2_part inner_rt2_part) orig recs
        r2 = kConst_red (natCode tagRuleTrans) orig recs
        r3 = pairBld_red y2_part inner_rt2_part orig recs
    in ruleTrans r1
         (ruleTrans (congL Pair (ap2 (pairBld y2_part inner_rt2_part) orig recs)
                                r2)
                    (congR Pair tagCode_ruleTrans r3))

  ------------------------------------------------------------------
  -- Step 3 helper: outer-shell reduction of inner_rt2_part.

  inner_rt2_outer : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 inner_rt2_part orig recs)
                       (ap2 Pair tagCode_ruleTrans
                          (ap2 Pair (ap2 y3_part orig recs)
                                    (ap2 y4_part orig recs)))))
  inner_rt2_outer orig recs =
    let r1 = pairBld_red (kConst tagCode_ruleTrans)
                         (pairBld y3_part y4_part) orig recs
        r2 = kConst_red (natCode tagRuleTrans) orig recs
        r3 = pairBld_red y3_part y4_part orig recs
    in ruleTrans r1
         (ruleTrans (congL Pair (ap2 (pairBld y3_part y4_part) orig recs)
                                r2)
                    (congR Pair tagCode_ruleTrans r3))

  ------------------------------------------------------------------
  -- Step 3 helper: full chain unfolding of D_Rec_zs_step.
  --
  -- ap2 D_Rec_zs_step orig recs
  --   = parEncRuleTrans y1_runtime
  --       (parEncRuleTrans y2_runtime
  --         (parEncRuleTrans y3_runtime y4_runtime))
  -- where y_i_runtime = ap2 y_i_part orig recs.
  --
  -- Combines D_Rec_zs_step_outer + inner_rt1_outer + inner_rt2_outer
  -- via congR-Pair lifts.

  D_Rec_zs_step_chain : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 D_Rec_zs_step orig recs)
                       (ap2 Pair tagCode_ruleTrans
                         (ap2 Pair (ap2 y1_part orig recs)
                           (ap2 Pair tagCode_ruleTrans
                             (ap2 Pair (ap2 y2_part orig recs)
                               (ap2 Pair tagCode_ruleTrans
                                 (ap2 Pair (ap2 y3_part orig recs)
                                           (ap2 y4_part orig recs)))))))))
  D_Rec_zs_step_chain orig recs =
    let r_outer = D_Rec_zs_step_outer orig recs
        r_rt1   = inner_rt1_outer orig recs
        r_rt2   = inner_rt2_outer orig recs
        lift_rt1 : Deriv (atomic (eqn
                    (ap2 Pair tagCode_ruleTrans
                       (ap2 Pair (ap2 y1_part orig recs)
                                 (ap2 inner_rt1_part orig recs)))
                    (ap2 Pair tagCode_ruleTrans
                       (ap2 Pair (ap2 y1_part orig recs)
                          (ap2 Pair tagCode_ruleTrans
                             (ap2 Pair (ap2 y2_part orig recs)
                                       (ap2 inner_rt2_part orig recs)))))))
        lift_rt1 = congR Pair tagCode_ruleTrans
                    (congR Pair (ap2 y1_part orig recs) r_rt1)
        lift_rt2 : Deriv (atomic (eqn
                    (ap2 Pair tagCode_ruleTrans
                       (ap2 Pair (ap2 y1_part orig recs)
                          (ap2 Pair tagCode_ruleTrans
                             (ap2 Pair (ap2 y2_part orig recs)
                                       (ap2 inner_rt2_part orig recs)))))
                    (ap2 Pair tagCode_ruleTrans
                       (ap2 Pair (ap2 y1_part orig recs)
                          (ap2 Pair tagCode_ruleTrans
                             (ap2 Pair (ap2 y2_part orig recs)
                                (ap2 Pair tagCode_ruleTrans
                                   (ap2 Pair (ap2 y3_part orig recs)
                                             (ap2 y4_part orig recs)))))))))
        lift_rt2 = congR Pair tagCode_ruleTrans
                    (congR Pair (ap2 y1_part orig recs)
                      (congR Pair tagCode_ruleTrans
                        (congR Pair (ap2 y2_part orig recs) r_rt2)))
    in ruleTrans r_outer (ruleTrans lift_rt1 lift_rt2)

  ------------------------------------------------------------------
  -- Step 3 helper: combined outer + chain reduction at Pair a b.
  --
  -- ap1 D_Rec_zs (Pair a b) = chain Term (with y_i opaque)
  -- where the recs slot is Pair (D_Rec_zs a) (D_Rec_zs b).

  D_Rec_zs_Nd_full : (a b : Term) ->
    let orig = ap2 Pair a b
        recs = ap2 Pair (ap1 D_Rec_zs a) (ap1 D_Rec_zs b)
    in Deriv (atomic (eqn (ap1 D_Rec_zs orig)
                          (ap2 Pair tagCode_ruleTrans
                            (ap2 Pair (ap2 y1_part orig recs)
                              (ap2 Pair tagCode_ruleTrans
                                (ap2 Pair (ap2 y2_part orig recs)
                                  (ap2 Pair tagCode_ruleTrans
                                    (ap2 Pair (ap2 y3_part orig recs)
                                              (ap2 y4_part orig recs)))))))))
  D_Rec_zs_Nd_full a b =
    let orig = ap2 Pair a b
        recs = ap2 Pair (ap1 D_Rec_zs a) (ap1 D_Rec_zs b)
    in ruleTrans (D_Rec_zs_outer_red a b) (D_Rec_zs_step_chain orig recs)

  ------------------------------------------------------------------
  -- y1_part runtime reduction.
  --
  -- ap2 y1_part orig recs
  --   = parEncAxRecNd zT sT (ap2 cor_a orig recs) (ap2 cor_b orig recs)
  --   = Pair tagCode_axRecNd (Pair zT (Pair sT (Pair <cora> <corb>)))
  -- where <cora> = ap2 cor_a orig recs, <corb> = ap2 cor_b orig recs.

  y1_part_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y1_part orig recs)
                       (ap2 Pair tagCode_axRecNd
                         (ap2 Pair zT
                           (ap2 Pair sT
                             (ap2 Pair (ap2 cor_a orig recs)
                                       (ap2 cor_b orig recs)))))))
  y1_part_red orig recs =
    let b4 = pairBld_red cor_a cor_b orig recs
        l3a = pairBld_red (kConst sT) (pairBld cor_a cor_b) orig recs
        l3b = kConst_red (codeF2 s) orig recs
        l3 = ruleTrans l3a
              (ruleTrans (congL Pair (ap2 (pairBld cor_a cor_b) orig recs) l3b)
                         (congR Pair sT b4))
        l2a = pairBld_red (kConst zT)
                          (pairBld (kConst sT) (pairBld cor_a cor_b)) orig recs
        l2b = kConst_red (code z) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair (ap2 (pairBld (kConst sT)
                                            (pairBld cor_a cor_b)) orig recs)
                                    l2b)
                         (congR Pair zT l3))
        l1a = pairBld_red (kConst tagCode_axRecNd)
                          (pairBld (kConst zT)
                            (pairBld (kConst sT) (pairBld cor_a cor_b))) orig recs
        l1b = kConst_red (natCode tagAxRecNd) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair (ap2 (pairBld (kConst zT)
                                       (pairBld (kConst sT)
                                         (pairBld cor_a cor_b))) orig recs)
                              l1b)
                    (congR Pair tagCode_axRecNd l2))

  ------------------------------------------------------------------
  -- y4_part runtime reduction.

  y4_part_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y4_part orig recs)
                       (ap2 D2_s orig
                         (ap2 Pair (ap2 rec_a orig recs)
                                   (ap2 rec_b orig recs)))))
  y4_part_red orig recs =
    let r1 = axFan (Lift I) (pairBld rec_a rec_b) D2_s orig recs
        r2 = axLift I orig recs
        r3 = axI orig
        r_first = ruleTrans r2 r3
        r_second = pairBld_red rec_a rec_b orig recs
        step1 = congL D2_s (ap2 (pairBld rec_a rec_b) orig recs) r_first
        step2 = congR D2_s orig r_second
    in ruleTrans r1 (ruleTrans step1 step2)

  ------------------------------------------------------------------
  -- enc_rec_a / enc_rec_b runtime reductions.
  --
  -- ap2 enc_rec_a orig recs
  --   = Pair (reify tagAp1) (Pair (reify (codeF1 (Rec z s)))
  --                               (ap2 cor_a orig recs))
  -- (and analog for b).

  enc_rec_a_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 enc_rec_a orig recs)
                       (ap2 Pair (reify tagAp1)
                         (ap2 Pair (reify (codeF1 (Rec z s)))
                                   (ap2 cor_a orig recs)))))
  enc_rec_a_red orig recs =
    let l2a = pairBld_red (kConst (reify (codeF1 (Rec z s)))) cor_a orig recs
        l2b = kConst_red (codeF1 (Rec z s)) orig recs
        l2 = ruleTrans l2a (congL Pair (ap2 cor_a orig recs) l2b)
        l1a = pairBld_red (kConst (reify tagAp1))
                          (pairBld (kConst (reify (codeF1 (Rec z s)))) cor_a) orig recs
        l1b = kConst_red tagAp1 orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair (ap2 (pairBld (kConst (reify (codeF1 (Rec z s))))
                                              cor_a) orig recs) l1b)
                    (congR Pair (reify tagAp1) l2))

  enc_rec_b_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 enc_rec_b orig recs)
                       (ap2 Pair (reify tagAp1)
                         (ap2 Pair (reify (codeF1 (Rec z s)))
                                   (ap2 cor_b orig recs)))))
  enc_rec_b_red orig recs =
    let l2a = pairBld_red (kConst (reify (codeF1 (Rec z s)))) cor_b orig recs
        l2b = kConst_red (codeF1 (Rec z s)) orig recs
        l2 = ruleTrans l2a (congL Pair (ap2 cor_b orig recs) l2b)
        l1a = pairBld_red (kConst (reify tagAp1))
                          (pairBld (kConst (reify (codeF1 (Rec z s)))) cor_b) orig recs
        l1b = kConst_red tagAp1 orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair (ap2 (pairBld (kConst (reify (codeF1 (Rec z s))))
                                              cor_b) orig recs) l1b)
                    (congR Pair (reify tagAp1) l2))

  ------------------------------------------------------------------
  -- X_enc_part runtime reduction.
  --
  -- ap2 X_enc_part orig recs
  --   = Pair (reify tagAp2) (Pair (reify (codeF2 Pair))
  --                               (Pair <cora> <corb>))

  X_enc_part_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 X_enc_part orig recs)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 cor_a orig recs)
                                     (ap2 cor_b orig recs))))))
  X_enc_part_red orig recs =
    let bot = pairBld_red cor_a cor_b orig recs
        l2a = pairBld_red (kConst (reify (codeF2 Pair))) (pairBld cor_a cor_b) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair (ap2 (pairBld cor_a cor_b) orig recs) l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst (reify tagAp2))
                          (pairBld (kConst (reify (codeF2 Pair))) (pairBld cor_a cor_b))
                          orig recs
        l1b = kConst_red tagAp2 orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                                       (pairBld cor_a cor_b)) orig recs) l1b)
                    (congR Pair (reify tagAp2) l2))

  ------------------------------------------------------------------
  -- y_v_y2 layer reductions.

  y_v_y2_layer1_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y_v_y2_layer1 orig recs)
                       (ap2 Pair tagCode_congL
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 proj_recA orig recs)
                                     (ap2 enc_rec_b orig recs))))))
  y_v_y2_layer1_red orig recs =
    let bot = pairBld_red proj_recA enc_rec_b orig recs
        l2a = pairBld_red (kConst (reify (codeF2 Pair)))
                          (pairBld proj_recA enc_rec_b) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair (ap2 (pairBld proj_recA enc_rec_b) orig recs) l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst tagCode_congL)
                (pairBld (kConst (reify (codeF2 Pair)))
                  (pairBld proj_recA enc_rec_b)) orig recs
        l1b = kConst_red (natCode tagCongL) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                   (pairBld proj_recA enc_rec_b)) orig recs) l1b)
                    (congR Pair tagCode_congL l2))

  y_v_y2_layer2_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y_v_y2_layer2 orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 y_v_y2_layer1 orig recs)
                                     (reify (codeF2 Pair)))))))
  y_v_y2_layer2_red orig recs =
    let bot_a = pairBld_red y_v_y2_layer1 (kConst (reify (codeF2 Pair))) orig recs
        bot_b = kConst_red (codeF2 Pair) orig recs
        bot = ruleTrans bot_a
                (congR Pair (ap2 y_v_y2_layer1 orig recs) bot_b)
        l2a = pairBld_red (kConst (reify (codeF2 Pair)))
                (pairBld y_v_y2_layer1 (kConst (reify (codeF2 Pair)))) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair
                 (ap2 (pairBld y_v_y2_layer1 (kConst (reify (codeF2 Pair)))) orig recs)
                 l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 Pair)))
                  (pairBld y_v_y2_layer1 (kConst (reify (codeF2 Pair))))) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                   (pairBld y_v_y2_layer1 (kConst (reify (codeF2 Pair))))) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  y_v_y2_layer3_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y_v_y2_layer3 orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 y_v_y2_layer2 orig recs)
                                     (reify tagAp2))))))
  y_v_y2_layer3_red orig recs =
    let bot_a = pairBld_red y_v_y2_layer2 (kConst (reify tagAp2)) orig recs
        bot_b = kConst_red tagAp2 orig recs
        bot = ruleTrans bot_a
                (congR Pair (ap2 y_v_y2_layer2 orig recs) bot_b)
        l2a = pairBld_red (kConst (reify (codeF2 Pair)))
                (pairBld y_v_y2_layer2 (kConst (reify tagAp2))) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair
                 (ap2 (pairBld y_v_y2_layer2 (kConst (reify tagAp2))) orig recs) l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 Pair)))
                  (pairBld y_v_y2_layer2 (kConst (reify tagAp2)))) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                   (pairBld y_v_y2_layer2 (kConst (reify tagAp2)))) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  ------------------------------------------------------------------
  -- y2_part runtime reduction.

  y2_part_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y2_part orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 s))
                           (ap2 Pair (ap2 y_v_y2_layer3 orig recs)
                                     (ap2 X_enc_part orig recs))))))
  y2_part_red orig recs =
    let bot = pairBld_red y_v_y2_layer3 X_enc_part orig recs
        l2a = pairBld_red (kConst (reify (codeF2 s)))
                          (pairBld y_v_y2_layer3 X_enc_part) orig recs
        l2b = kConst_red (codeF2 s) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair
                 (ap2 (pairBld y_v_y2_layer3 X_enc_part) orig recs) l2b)
                         (congR Pair (reify (codeF2 s)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 s)))
                  (pairBld y_v_y2_layer3 X_enc_part)) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 s)))
                   (pairBld y_v_y2_layer3 X_enc_part)) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  ------------------------------------------------------------------
  -- y_v_y3 layer reductions (mirror y_v_y2 structure but with proj_recB
  -- and cor_Rec_a as the innermost slots).

  y_v_y3_layer1_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y_v_y3_layer1 orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 proj_recB orig recs)
                                     (ap2 cor_Rec_a orig recs))))))
  y_v_y3_layer1_red orig recs =
    let bot = pairBld_red proj_recB cor_Rec_a orig recs
        l2a = pairBld_red (kConst (reify (codeF2 Pair)))
                          (pairBld proj_recB cor_Rec_a) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair (ap2 (pairBld proj_recB cor_Rec_a) orig recs) l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 Pair)))
                  (pairBld proj_recB cor_Rec_a)) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                   (pairBld proj_recB cor_Rec_a)) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  y_v_y3_layer2_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y_v_y3_layer2 orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 y_v_y3_layer1 orig recs)
                                     (reify (codeF2 Pair)))))))
  y_v_y3_layer2_red orig recs =
    let bot_a = pairBld_red y_v_y3_layer1 (kConst (reify (codeF2 Pair))) orig recs
        bot_b = kConst_red (codeF2 Pair) orig recs
        bot = ruleTrans bot_a
                (congR Pair (ap2 y_v_y3_layer1 orig recs) bot_b)
        l2a = pairBld_red (kConst (reify (codeF2 Pair)))
                (pairBld y_v_y3_layer1 (kConst (reify (codeF2 Pair)))) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair
                 (ap2 (pairBld y_v_y3_layer1 (kConst (reify (codeF2 Pair)))) orig recs)
                 l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 Pair)))
                  (pairBld y_v_y3_layer1 (kConst (reify (codeF2 Pair))))) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                   (pairBld y_v_y3_layer1 (kConst (reify (codeF2 Pair))))) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  y_v_y3_layer3_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y_v_y3_layer3 orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap2 y_v_y3_layer2 orig recs)
                                     (reify tagAp2))))))
  y_v_y3_layer3_red orig recs =
    let bot_a = pairBld_red y_v_y3_layer2 (kConst (reify tagAp2)) orig recs
        bot_b = kConst_red tagAp2 orig recs
        bot = ruleTrans bot_a
                (congR Pair (ap2 y_v_y3_layer2 orig recs) bot_b)
        l2a = pairBld_red (kConst (reify (codeF2 Pair)))
                (pairBld y_v_y3_layer2 (kConst (reify tagAp2))) orig recs
        l2b = kConst_red (codeF2 Pair) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair
                 (ap2 (pairBld y_v_y3_layer2 (kConst (reify tagAp2))) orig recs) l2b)
                         (congR Pair (reify (codeF2 Pair)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 Pair)))
                  (pairBld y_v_y3_layer2 (kConst (reify tagAp2)))) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 Pair)))
                   (pairBld y_v_y3_layer2 (kConst (reify tagAp2)))) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  ------------------------------------------------------------------
  -- y3_part runtime reduction.

  y3_part_red : (orig recs : Term) ->
    Deriv (atomic (eqn (ap2 y3_part orig recs)
                       (ap2 Pair tagCode_congR
                         (ap2 Pair (reify (codeF2 s))
                           (ap2 Pair (ap2 y_v_y3_layer3 orig recs)
                                     (ap2 X_enc_part orig recs))))))
  y3_part_red orig recs =
    let bot = pairBld_red y_v_y3_layer3 X_enc_part orig recs
        l2a = pairBld_red (kConst (reify (codeF2 s)))
                          (pairBld y_v_y3_layer3 X_enc_part) orig recs
        l2b = kConst_red (codeF2 s) orig recs
        l2 = ruleTrans l2a
              (ruleTrans (congL Pair
                 (ap2 (pairBld y_v_y3_layer3 X_enc_part) orig recs) l2b)
                         (congR Pair (reify (codeF2 s)) bot))
        l1a = pairBld_red (kConst tagCode_congR)
                (pairBld (kConst (reify (codeF2 s)))
                  (pairBld y_v_y3_layer3 X_enc_part)) orig recs
        l1b = kConst_red (natCode tagCongR) orig recs
    in ruleTrans l1a
         (ruleTrans (congL Pair
            (ap2 (pairBld (kConst (reify (codeF2 s)))
                   (pairBld y_v_y3_layer3 X_enc_part)) orig recs) l1b)
                    (congR Pair tagCode_congR l2))

  ------------------------------------------------------------------
  -- At-runtime simplifications: when orig = Pair a b, the projections
  -- reduce to a/b/cor a/etc.

  cor_a_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 cor_a (ap2 Pair a b) recs) (ap1 cor a)))
  cor_a_at a b recs =
    let orig = ap2 Pair a b
        r1 = axLift (Comp cor Fst) orig recs
        r2 = axComp cor Fst orig
        r3 = axFst a b
    in ruleTrans r1 (ruleTrans r2 (cong1 cor r3))

  cor_b_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 cor_b (ap2 Pair a b) recs) (ap1 cor b)))
  cor_b_at a b recs =
    let orig = ap2 Pair a b
        r1 = axLift (Comp cor Snd) orig recs
        r2 = axComp cor Snd orig
        r3 = axSnd a b
    in ruleTrans r1 (ruleTrans r2 (cong1 cor r3))

  rec_a_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 rec_a (ap2 Pair a b) recs) (ap1 (Rec z s) a)))
  rec_a_at a b recs =
    let orig = ap2 Pair a b
        r1 = axLift (Comp (Rec z s) Fst) orig recs
        r2 = axComp (Rec z s) Fst orig
        r3 = axFst a b
    in ruleTrans r1 (ruleTrans r2 (cong1 (Rec z s) r3))

  rec_b_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 rec_b (ap2 Pair a b) recs) (ap1 (Rec z s) b)))
  rec_b_at a b recs =
    let orig = ap2 Pair a b
        r1 = axLift (Comp (Rec z s) Snd) orig recs
        r2 = axComp (Rec z s) Snd orig
        r3 = axSnd a b
    in ruleTrans r1 (ruleTrans r2 (cong1 (Rec z s) r3))

  cor_Rec_a_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 cor_Rec_a (ap2 Pair a b) recs)
                       (ap1 cor (ap1 (Rec z s) a))))
  cor_Rec_a_at a b recs =
    let orig = ap2 Pair a b
        r1 = axLift (Comp cor (Comp (Rec z s) Fst)) orig recs
        r2 = axComp cor (Comp (Rec z s) Fst) orig
        r3 = axComp (Rec z s) Fst orig
        r4 = axFst a b
    in ruleTrans r1 (ruleTrans r2
         (cong1 cor (ruleTrans r3 (cong1 (Rec z s) r4))))

  cor_Rec_b_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 cor_Rec_b (ap2 Pair a b) recs)
                       (ap1 cor (ap1 (Rec z s) b))))
  cor_Rec_b_at a b recs =
    let orig = ap2 Pair a b
        r1 = axLift (Comp cor (Comp (Rec z s) Snd)) orig recs
        r2 = axComp cor (Comp (Rec z s) Snd) orig
        r3 = axComp (Rec z s) Snd orig
        r4 = axSnd a b
    in ruleTrans r1 (ruleTrans r2
         (cong1 cor (ruleTrans r3 (cong1 (Rec z s) r4))))

  proj_recA_at : (orig recA_t recB_t : Term) ->
    Deriv (atomic (eqn (ap2 proj_recA orig (ap2 Pair recA_t recB_t)) recA_t))
  proj_recA_at orig recA_t recB_t =
    let recs = ap2 Pair recA_t recB_t
        r1 = axPost (Comp Fst Snd) Pair orig recs
        r2 = axComp Fst Snd (ap2 Pair orig recs)
        r3 = axSnd orig recs
        r4 = axFst recA_t recB_t
    in ruleTrans r1 (ruleTrans r2 (ruleTrans (cong1 Fst r3) r4))

  proj_recB_at : (orig recA_t recB_t : Term) ->
    Deriv (atomic (eqn (ap2 proj_recB orig (ap2 Pair recA_t recB_t)) recB_t))
  proj_recB_at orig recA_t recB_t =
    let recs = ap2 Pair recA_t recB_t
        r1 = axPost (Comp Snd Snd) Pair orig recs
        r2 = axComp Snd Snd (ap2 Pair orig recs)
        r3 = axSnd orig recs
        r4 = axSnd recA_t recB_t
    in ruleTrans r1 (ruleTrans r2 (ruleTrans (cong1 Snd r3) r4))

  ------------------------------------------------------------------
  -- enc_rec_b at runtime (orig = Pair a b):
  --   ap2 enc_rec_b (Pair a b) recs
  --     = Pair (reify tagAp1) (Pair (reify (codeF1 (Rec z s))) (cor b))

  enc_rec_b_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 enc_rec_b (ap2 Pair a b) recs)
                       (ap2 Pair (reify tagAp1)
                         (ap2 Pair (reify (codeF1 (Rec z s)))
                                   (ap1 cor b)))))
  enc_rec_b_at a b recs =
    let red = enc_rec_b_red (ap2 Pair a b) recs
        corb = cor_b_at a b recs
    in ruleTrans red (congR Pair (reify tagAp1)
                       (congR Pair (reify (codeF1 (Rec z s))) corb))

  ------------------------------------------------------------------
  -- X_enc_part at runtime (orig = Pair a b):
  --   ap2 X_enc_part (Pair a b) recs
  --     = Pair (reify tagAp2) (Pair (reify (codeF2 Pair))
  --                                  (Pair (cor a) (cor b)))

  X_enc_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap2 X_enc_part (ap2 Pair a b) recs)
                       (ap2 Pair (reify tagAp2)
                         (ap2 Pair (reify (codeF2 Pair))
                           (ap2 Pair (ap1 cor a) (ap1 cor b))))))
  X_enc_at a b recs =
    let red = X_enc_part_red (ap2 Pair a b) recs
        cora = cor_a_at a b recs
        corb = cor_b_at a b recs
        inner_pair = ruleTrans (congL Pair (ap2 cor_b (ap2 Pair a b) recs) cora)
                               (congR Pair (ap1 cor a) corb)
        lifted = congR Pair (reify tagAp2)
                   (congR Pair (reify (codeF2 Pair)) inner_pair)
    in ruleTrans red lifted

  ------------------------------------------------------------------
  -- y1 thmT: at orig = Pair a b, ap1 thmT (ap2 y1_part orig recs)
  --   = parOutAxRecNd zT sT (cor a) (cor b).

  y1_thmT_at : (a b recs : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 y1_part (ap2 Pair a b) recs))
                       (parOutAxRecNd zT sT (ap1 cor a) (ap1 cor b))))
  y1_thmT_at a b recs =
    let red = y1_part_red (ap2 Pair a b) recs
        cora = cor_a_at a b recs
        corb = cor_b_at a b recs
        inner_pair = ruleTrans (congL Pair (ap2 cor_b (ap2 Pair a b) recs) cora)
                               (congR Pair (ap1 cor a) corb)
        red_simpl = ruleTrans red
                      (congR Pair tagCode_axRecNd
                        (congR Pair zT
                          (congR Pair sT inner_pair)))
        disp = parDispAxRecNd zT sT (ap1 cor a) (ap1 cor b)
    in ruleTrans (cong1 thmT red_simpl) disp
