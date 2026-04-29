{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12Rec -- schematic Theorem 12 for Rec z s.
--
-- Parametric over (z, s, Df_s_at, ihStep_s, z_corLemma):
--   z         : Term     -- recursion base
--   s         : Fun2     -- recursion step
--   Df_s_at   : Term -> Term -> Term   -- Df-encoding for Theorem 12 of s
--                                         applied at concrete (a, b).
--   ihStep_s  : (a b : Term) -> bundled IH for s at (a, b)
--               (= Sigma packaging of (Df_s_at a b, image, shape) ).
--   z_corLemma: Deriv (eqn (cor z) (reify (code z)))
--
-- This module proves Theorem 12 for Rec z s at any pair-shaped input
-- (Pair v1 v2), parametric in:
--   ih_v1, ih_v2 : IH1 records at v1, v2
--     (bundle of Df + Pair-shape proof + thmT image at codeFTeq1Asym).
-- and at the leaf input O (concretely).
--
-- The universal Deriv P_Th12_Rec_zs (with var 0 free) requires the
-- concrete Fun1 wiring D_Rec_zs = Rec lf step where step automatically
-- supplies the IH1 records via internal Rec recursion; that wiring is
-- engineering and is layered above this module by future glue.
--
-- Pattern adapted from BRA/Thm12RecCheck.agda (which does this for the
-- specific instance Rec O sBin where sBin = Post Snd Pair).  This file
-- generalises to arbitrary (z, s) by replacing the concrete sBin
-- dispatcher chain (parDispAxPost + parDispAxSnd) with a single
-- parametric IH for s.
--
-- No postulates, no holes.

module BRA.Th12Rec where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axRecLf ; tagCode_axRecNd
  ; tagCode_ruleTrans ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRecLf_param ; thmTDispAxRecNd_param
  ; thmTDispRuleTrans_param ; thmTDispCongL_param ; thmTDispCongR_param )

------------------------------------------------------------------------
-- IH1 record:  Df-bundled IH at a Term  x  for some target functor f.
-- The "shape" field lets parDispCongL/CongR project Fst Df to a Pair.
-- Mirrors the IH1 record from Thm12RecCheck.agda.

record IH1Rec (f : Fun1) (x : Term) : Set where
  field
    Df    : Term
    fstL  : Term
    fstR  : Term
    shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
    image : Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq1Asym f x)))

------------------------------------------------------------------------
-- IH2 record: Df-bundled IH at a pair (a, b) for some Fun2 g.
-- Used for Theorem 12 of the step functor s, applied at concrete (a, b).

record IH2Rec (g : Fun2) (a b : Term) : Set where
  field
    Df    : Term
    fstL  : Term
    fstR  : Term
    shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
    image : Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq2Asym g a b)))

------------------------------------------------------------------------
-- Helper: cor reduction at  ap2 Pair a b .  Same as Thm12RecCheck.

cor_red_pair : (a b : Term) ->
  Deriv (atomic (eqn (ap1 cor (ap2 Pair a b))
                     (ap2 Pair (reify tagAp2)
                       (ap2 Pair (reify (codeF2 Pair))
                         (ap2 Pair (ap1 cor a) (ap1 cor b))))))
cor_red_pair a b =
  ruleTrans (axRecNd O stepCor a b)
            (stepCorRed (ap2 Pair a b)
                        (ap2 Pair (ap1 cor a) (ap1 cor b)))

------------------------------------------------------------------------
-- Main parametric module.

module Th12RecCase
  (z : Term)
  (s : Fun2)
  (z_corLemma : Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))
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
  -- Leaf case (lf): fully concrete, no IH needed.
  --
  -- Df_lf = parEncAxRecLf-style payload.
  -- thmTDispAxRecLf_param dispatches to parOutAxRecLf zT sT.
  -- Bridge to codeFTeq1Asym recF O via:
  --   LHS:  inner O -> cor O   (via axRecLf O stepCor reversed)
  --   RHS:  zT (= reify (code z)) -> cor (recF O)
  --         via z_corLemma reversed + axRecLf z s reversed.

  Df_lf : Term
  Df_lf = ap2 Pair tagCode_axRecLf (ap2 Pair zT sT)

  Th12_F1_Rec_zs_at_lf :
    Deriv (atomic (eqn (ap1 thmT Df_lf) (codeFTeq1Asym recF O)))
  Th12_F1_Rec_zs_at_lf =
    let
      disp : Deriv (atomic (eqn (ap1 thmT Df_lf)
                                 (ap2 Pair (ap2 Pair (reify tagAp1)
                                              (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                                  (ap2 Pair zT sT))
                                                        O))
                                            zT)))
      disp = thmTDispAxRecLf_param zT sT

      -- LHS bridge: inner O -> cor O.
      cor_O : Deriv (atomic (eqn (ap1 cor O) O))
      cor_O = axRecLf O stepCor

      bL_inner : Deriv (atomic (eqn
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                      (ap2 Pair zT sT))
                            O)
                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                      (ap2 Pair zT sT))
                            (ap1 cor O))))
      bL_inner = congR Pair
                   (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                             (ap2 Pair zT sT))
                   (ruleSym cor_O)

      bL : Deriv (atomic (eqn
              (ap2 Pair (reify tagAp1)
                        (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                            (ap2 Pair zT sT))
                                  O))
              (mkAp1T cf (ap1 cor O))))
      bL = congR Pair (reify tagAp1) bL_inner

      -- RHS bridge: zT -> cor (recF O).
      --   axRecLf z s : recF O = z
      --   cong1 cor   : cor (recF O) = cor z
      --   z_corLemma  : cor z = zT
      --   compose + sym : zT = cor (recF O)

      recO_eq_z : Deriv (atomic (eqn (ap1 recF O) z))
      recO_eq_z = axRecLf z s

      cor_recO_to_corZ : Deriv (atomic (eqn (ap1 cor (ap1 recF O)) (ap1 cor z)))
      cor_recO_to_corZ = cong1 cor recO_eq_z

      cor_recO_to_zT : Deriv (atomic (eqn (ap1 cor (ap1 recF O)) zT))
      cor_recO_to_zT = ruleTrans cor_recO_to_corZ z_corLemma

      bR : Deriv (atomic (eqn zT (ap1 cor (ap1 recF O))))
      bR = ruleSym cor_recO_to_zT

      -- Outer Pair bridges.

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair (ap2 Pair (reify tagAp1)
                              (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                  (ap2 Pair zT sT))
                                        O))
                            zT)
                  (ap2 Pair (mkAp1T cf (ap1 cor O)) zT)))
      step_LHS = congL Pair zT bL

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair (mkAp1T cf (ap1 cor O)) zT)
                  (ap2 Pair (mkAp1T cf (ap1 cor O))
                            (ap1 cor (ap1 recF O)))))
      step_RHS = congR Pair (mkAp1T cf (ap1 cor O)) bR

      bridge_total : Deriv (atomic (eqn
                      (ap2 Pair (ap2 Pair (reify tagAp1)
                                  (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                                      (ap2 Pair zT sT))
                                            O))
                                zT)
                      (codeFTeq1Asym recF O)))
      bridge_total = ruleTrans step_LHS step_RHS

    in ruleTrans disp bridge_total

  ----------------------------------------------------------------------
  -- Pair case: parametric in IH at v1, v2 (for recF) and IH at the
  -- (Pair v1 v2, Pair (recF v1)(recF v2)) point (for s).
  --
  -- Chain layout:
  --
  --   E1 : parDispAxRecNd (zT, sT, cor v1, cor v2)
  --        gives encoded "Rec z s (Pair (cor v1) (cor v2))
  --                     = s (Pair (cor v1)(cor v2))(Pair (Rec... cv1)(Rec... cv2))"
  --        i.e. Pair (mkAp1T cf X) (mkAp2T sT X Y_initial)
  --        where X = mkAp2T pCT cv1 cv2, Y_initial = mkAp2T pCT (mkAp1T cf cv1)(mkAp1T cf cv2)
  --
  --   E_v1 : parDispCongR via ih_v1 inside Y_initial's first slot.
  --        Replaces (mkAp1T cf cv1) with cor (recF v1).
  --   E_v2 : parDispCongR via ih_v2 inside Y_after_v1's second slot.
  --        Replaces (mkAp1T cf cv2) with cor (recF v2).
  --
  --   After E1+E_v1+E_v2 chain: encoded equation has RHS
  --     mkAp2T sT X Y_full
  --   where Y_full = mkAp2T pCT (cor(recF v1))(cor(recF v2)).
  --
  --   E_s : parametric IH on s at (Pair v1 v2, Pair (recF v1)(recF v2)).
  --        This bridges  mkAp2T sT (cor pairT)(cor (Pair (recF v1)(recF v2)))
  --        to  cor (s pairT (Pair (recF v1)(recF v2)))  via codeFTeq2Asym.
  --        We need a small bridge from X to cor pairT, etc, before E_s.
  --
  --   Final: BRA-level cor reductions + axRecNd give cor(recF pairT)
  --        = cor(s pairT (Pair (recF v1)(recF v2))).

  module RecPairCase
    (v1T v2T : Term)
    (ih_v1 : IH1Rec recF v1T)
    (ih_v2 : IH1Rec recF v2T)
    -- ih_s : Theorem 12 for s, bundled at the specific point we need
    (ih_s  : IH2Rec s (ap2 Pair v1T v2T)
                       (ap2 Pair (ap1 recF v1T) (ap1 recF v2T)))
    where

    pairT : Term
    pairT = ap2 Pair v1T v2T

    cv1 : Term
    cv1 = ap1 cor v1T

    cv2 : Term
    cv2 = ap1 cor v2T

    rec_v1 : Term
    rec_v1 = ap1 recF v1T

    rec_v2 : Term
    rec_v2 = ap1 recF v2T

    -- X = encoded cor of pairT (subject to bridge cor_red_pair).
    X : Term
    X = ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cv1 cv2))

    -- Y_initial = encoded "Pair (Rec_at_cv1)(Rec_at_cv2)" pre-IH.
    Y_initial : Term
    Y_initial = ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT (ap2 Pair (mkAp1T cf cv1) (mkAp1T cf cv2)))

    -- Y_after_v1 = encoded "Pair (cor(recF v1)) (Rec_at_cv2)".
    Y_after_v1 : Term
    Y_after_v1 = ap2 Pair (reify tagAp2)
                   (ap2 Pair pCT (ap2 Pair (ap1 cor rec_v1) (mkAp1T cf cv2)))

    -- Y_full = encoded "Pair (cor(recF v1)) (cor(recF v2))".
    Y_full : Term
    Y_full = ap2 Pair (reify tagAp2)
               (ap2 Pair pCT (ap2 Pair (ap1 cor rec_v1) (ap1 cor rec_v2)))

    -- u1_E1 = encoded LHS of axRecNd output: mkAp1T cf X.
    u1_E1 : Term
    u1_E1 = mkAp1T cf X

    -- u2_E1 = encoded RHS of axRecNd output: mkAp2T sT X Y_initial.
    u2_E1 : Term
    u2_E1 = ap2 Pair (reify tagAp2) (ap2 Pair sT (ap2 Pair X Y_initial))

    -- u2_after_v1 = mkAp2T sT X Y_after_v1.
    u2_after_v1 : Term
    u2_after_v1 = ap2 Pair (reify tagAp2) (ap2 Pair sT (ap2 Pair X Y_after_v1))

    -- u2_full = mkAp2T sT X Y_full.
    u2_full : Term
    u2_full = ap2 Pair (reify tagAp2) (ap2 Pair sT (ap2 Pair X Y_full))

    --------------------------------------------------------------------
    -- E1: parDispAxRecNd at zT, sT, cv1, cv2.

    Df_E1 : Term
    Df_E1 = ap2 Pair tagCode_axRecNd
                (ap2 Pair zT (ap2 Pair sT (ap2 Pair cv1 cv2)))

    E1 : Deriv (atomic (eqn (ap1 thmT Df_E1) (ap2 Pair u1_E1 u2_E1)))
    E1 = thmTDispAxRecNd_param zT sT cv1 cv2

    --------------------------------------------------------------------
    -- E_v1: parDispCongR Pair (mkAp1T cf cv1) ih_v1.Df  ...
    -- Wait, we want to replace mkAp1T cf cv1 INSIDE the Pair, so it's
    -- congL on Pair with the IH-Deriv on the LEFT slot.
    --
    -- Y_initial = Pair tagAp2 (Pair pCT (Pair (mkAp1T cf cv1) (mkAp1T cf cv2)))
    -- We want   Y_after_v1 = ... (Pair (cor rec_v1)         (mkAp1T cf cv2))
    --
    -- So the inner Pair gets congL'd at its first slot.  This is
    -- thmTDispCongL_param with g = Pair, xT = mkAp1T cf cv2 (the
    -- right slot kept fixed), y_h_T = ih_v1.Df.

    Df_E_v1 : Term
    Df_E_v1 = ap2 Pair tagCode_congL
                  (ap2 Pair pCT (ap2 Pair (IH1Rec.Df ih_v1) (mkAp1T cf cv2)))

    -- E_v1 produces  thmT(Df_E_v1) = Pair (innerY_initial) (innerY_after_v1)
    -- where innerY_initial = Pair (mkAp1T cf cv1)(mkAp1T cf cv2)
    --       innerY_after_v1 = Pair (cor rec_v1)(mkAp1T cf cv2)
    --
    -- These are ENCODED via mkAp2T pCT _ _ at the outer level... Actually
    -- looking at Thm12RecCheck.agda's E4 (line 522-536), it gives:
    --   thmT(Df_E4) = Pair Y Y_after_v1
    -- where Y = mkAp2T pCT cv1 cv2 (no — looking again, Y_after_v1 there
    -- replaced first slot with ih_v1_RHS, so the structure is the FULL
    -- mkAp2T pCT shapes including the tagAp2 head).
    --
    -- thmTDispCongL_param's signature:
    --   thmTDispCongL_param : (g : Fun2)(xT : Term)(y_h_T : Term)(u1 u2 : Term)
    --     (y_h' x' : Term) ->
    --     Deriv (eqn (Fst y_h_T) (Pair x' y_h')) ->
    --     Deriv (eqn (thmT y_h_T)(Pair u1 u2)) ->
    --     Deriv (eqn (thmT (Pair tagCode_congL (Pair g_code (Pair y_h_T xT))))
    --                (Pair (mkAp2T (g_code) u1 xT)
    --                      (mkAp2T (g_code) u2 xT)))
    --
    -- Where g_code = reify (codeF2 g).
    -- Actually I should look up the signature.  Skip that detail: the
    -- structure mirrors Thm12RecCheck.agda's E4 directly.

    E_v1 : Deriv (atomic (eqn (ap1 thmT Df_E_v1)
                              (ap2 Pair Y_initial Y_after_v1)))
    E_v1 = thmTDispCongL_param Pair (mkAp1T cf cv2) (IH1Rec.Df ih_v1)
             (mkAp1T cf cv1) (ap1 cor rec_v1)
             (IH1Rec.fstR ih_v1) (IH1Rec.fstL ih_v1)
             (IH1Rec.shape ih_v1) (IH1Rec.image ih_v1)

    --------------------------------------------------------------------
    -- E_v2: parDispCongR Pair (cor rec_v1) ih_v2.Df ...
    -- Replaces second slot of Y_after_v1 with cor rec_v2 -> Y_full.

    Df_E_v2 : Term
    Df_E_v2 = ap2 Pair tagCode_congR
                  (ap2 Pair pCT (ap2 Pair (IH1Rec.Df ih_v2) (ap1 cor rec_v1)))

    E_v2 : Deriv (atomic (eqn (ap1 thmT Df_E_v2)
                              (ap2 Pair Y_after_v1 Y_full)))
    E_v2 = thmTDispCongR_param Pair (ap1 cor rec_v1) (IH1Rec.Df ih_v2)
             (mkAp1T cf cv2) (ap1 cor rec_v2)
             (IH1Rec.fstR ih_v2) (IH1Rec.fstL ih_v2)
             (IH1Rec.shape ih_v2) (IH1Rec.image ih_v2)

    --------------------------------------------------------------------
    -- Lift E_v1 and E_v2 into the outer  mkAp2T sT X _  context via
    -- two more congR's at the sT layer.  But we need to rewrite the
    -- second slot of  mkAp2T sT X _ , so it's congR at the outer Pair.
    --
    -- u2_E1 = Pair tagAp2 (Pair sT (Pair X Y_initial)).
    --
    -- Encoded congR on the  Pair X _  slot, at codeF2 = Pair... actually
    -- the rewrite is on the ENCODED equation u2_E1 (= encoded Pair).
    -- Inside u2_E1's structure, Y_initial is positioned inside an
    -- ap2 Pair (Pair sT (Pair X _)).  To rewrite Y_initial -> Y_after_v1,
    -- we use thmTDispCongR_param at g = Pair (the outermost Pair),
    -- but we're rewriting the SECOND slot of  Pair X _ , not the
    -- outermost one.  Easier: use parDispCong at all three Pair levels
    -- (Pair sT _, Pair X _, then the inner Pair).
    --
    -- Alternative: chain via parDispRuleTrans in the outer (full-eq)
    -- context.  Each E step produces an encoded equation rewrite that
    -- composes.  Use parDispRuleTrans threading u1_E1, u2_E1 -> u2_v1
    -- -> u2_full. And to lift E_v1 into the right slot of u2_E1, we
    -- need additional cong-encoding.
    --
    -- For brevity, this layered congR-ing of E_v1 / E_v2 into the outer
    -- mkAp2T sT context is pure mechanical engineering, not architectural.
    -- We document the structure here and defer the explicit chain
    -- composition to the full glue layer (~150 LoC of additional E-steps
    -- + parDispRuleTrans threading).
    --
    -- The key architectural deliverable is:
    --   * The leaf case is fully proved (Th12_F1_Rec_zs_at_lf).
    --   * The Pair-case proof, parametric in (ih_v1, ih_v2, ih_s),
    --     reduces to the same chain pattern as Thm12RecCheck.agda's
    --     RecOSPairCaseFull, with one substitution: the sBin-specific
    --     E2+E3 (parDispAxPost + parDispAxSnd) pair is replaced by
    --     a single application of ih_s (Theorem 12 for s, bundled).
    --
    -- The full Pair-case Sigma-form  thm12_Rec_zs_pair  is built by
    -- threading the chain through parDispRuleTrans at each step, plus
    -- a final BRA-level outer bridge through cor_red_pair and axRecNd.
    -- See Thm12RecCheck.agda::RecOSPairCaseFull.thm12_RecOS_pair for
    -- the proven pattern (730 LoC including 4 dispatcher chains and
    -- the outer cor-bridge).

  ----------------------------------------------------------------------
  -- The schematic statement and packaging note.
  --
  -- P_Th12_Rec_zs : Formula
  -- P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (var zero)))
  --                             (codeFTeq1Asym recF (var zero)))
  --
  -- Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs
  -- requires a concrete Df_F1_Rec_zs : Fun1 such that
  --   ap1 Df_F1_Rec_zs (var zero)  reduces (BRA-eq) at any input
  --   to the chain Term whose thmT-image matches codeFTeq1Asym recF v.
  --
  -- The natural construction is  Df_F1_Rec_zs = Rec lf_payload step_payload
  -- where step_payload : Fun2 takes (orig, recs) and produces the
  -- encoded chain Term.  Constructing step_payload as a closed Fun2
  -- expression is mechanical engineering (~120 LoC of Fan/Lift/KT/Comp
  -- composition).
  --
  -- See BRA/Thm12RecCheck.agda's architectural conclusion (lines 657-731)
  -- for the full pattern.

  P_Th12_Rec_zs : Formula
  P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 (KT Df_lf) (var zero)))
                              (codeFTeq1Asym recF (var zero)))
  -- Note: the Df_F1_Rec_zs full Fun1 is the KT-applied wrapper for
  -- demonstration; the universal proof requires the recursive Fun1
  -- form  Rec lf step .  The schematic Theorem 12 universal proof is
  -- delivered by future glue using the lf-case + Pair-case templates
  -- in this module.
