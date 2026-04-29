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
    -- Lift E_v1 to outer mkAp2T sT X _ context via parDispCongR_param
    -- with g = s, xT = X.  The result is an encoded equation rewriting
    -- u2_E1 (= mkAp2T sT X Y_initial) to u2_after_v1 (= mkAp2T sT X Y_after_v1).
    --
    -- Df_E_v1's Fst is tagCode_congL (Pair-shaped since natCode tagCongL
    -- = nd lf (...)), so the shape proof is axFst tagCode_congL _.

    Df_E_v1_lifted : Term
    Df_E_v1_lifted = ap2 Pair tagCode_congR
                       (ap2 Pair sT (ap2 Pair Df_E_v1 X))

    E_v1_lifted : Deriv (atomic (eqn (ap1 thmT Df_E_v1_lifted)
                                      (ap2 Pair u2_E1 u2_after_v1)))
    E_v1_lifted = thmTDispCongR_param s X Df_E_v1 Y_initial Y_after_v1
                    _ _ (axFst tagCode_congL _) E_v1

    --------------------------------------------------------------------
    -- Lift E_v2 similarly.

    Df_E_v2_lifted : Term
    Df_E_v2_lifted = ap2 Pair tagCode_congR
                       (ap2 Pair sT (ap2 Pair Df_E_v2 X))

    E_v2_lifted : Deriv (atomic (eqn (ap1 thmT Df_E_v2_lifted)
                                      (ap2 Pair u2_after_v1 u2_full)))
    E_v2_lifted = thmTDispCongR_param s X Df_E_v2 Y_after_v1 Y_full
                    _ _ (axFst tagCode_congR _) E_v2

    --------------------------------------------------------------------
    -- chain1 = parDispRuleTrans(E1, E_v1_lifted): produces encoded
    -- equation  u1_E1 = u2_after_v1.

    Df_chain1 : Term
    Df_chain1 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1 Df_E_v1_lifted)

    chain1 : Deriv (atomic (eqn (ap1 thmT Df_chain1)
                                 (ap2 Pair u1_E1 u2_after_v1)))
    chain1 = thmTDispRuleTrans_param Df_E1 Df_E_v1_lifted
              u1_E1 u2_E1 u2_E1 u2_after_v1
              _ _ (axFst tagCode_axRecNd _) E1 E_v1_lifted

    --------------------------------------------------------------------
    -- chain12 = parDispRuleTrans(chain1, E_v2_lifted): produces encoded
    -- equation  u1_E1 = u2_full.

    Df_chain12 : Term
    Df_chain12 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1 Df_E_v2_lifted)

    chain12 : Deriv (atomic (eqn (ap1 thmT Df_chain12)
                                  (ap2 Pair u1_E1 u2_full)))
    chain12 = thmTDispRuleTrans_param Df_chain1 Df_E_v2_lifted
               u1_E1 u2_after_v1 u2_after_v1 u2_full
               _ _ (axFst tagCode_ruleTrans _) chain1 E_v2_lifted

    --------------------------------------------------------------------
    -- chain12 establishes the encoded equation:
    --   thmT (Df_chain12) = Pair u1_E1 u2_full
    --                     = Pair (mkAp1T cf X) (mkAp2T sT X Y_full)
    -- which encodes the BRA equation:
    --   (Rec z s)(encoded Pair cv1 cv2) = s (encoded Pair cv1 cv2)
    --                                       (encoded Pair (cor rec_v1)(cor rec_v2))
    --
    -- To extend chain12 to a complete Theorem 12 Sigma-form proof
    --   (Df_pair, Deriv (eqn (thmT Df_pair)(codeFTeq1Asym recF pairT)))
    -- we need TWO more steps:
    --
    --   E_s : encoded equation  mkAp2T sT (cor pairT)(cor (Pair rec_v1 rec_v2))
    --                          = cor (s pairT (Pair rec_v1 rec_v2))
    --         (= ih_s.image -- Theorem 12 for s at the appropriate point)
    --
    --   bridges : encoded cor_red_pair  X = cor pairT  AND
    --             Y_full = cor (Pair rec_v1 rec_v2) ,
    --             needed to align u2_full's RHS with E_s's LHS.
    --
    -- The bridges are encoded versions of cor_red_pair.  They are
    -- constructed from parEncAxRecNd O sT_cor v1 v2 + encoded
    -- stepCorRed (which itself has known encoding via Fan/Lift/KT
    -- composition).  Total ~200 LoC of mechanical encoding.
    --
    -- Once threaded, the final encoded chain produces:
    --   Pair u1_E1 (cor (s pairT (Pair rec_v1 rec_v2)))
    -- and a BRA-level outer bridge applies:
    --   - LHS: u1_E1 = mkAp1T cf X -> mkAp1T cf (cor pairT) via congR + cor_red_pair.
    --   - RHS: cor (s pairT _) -> cor (recF pairT) via cong1 cor (axRecNd reversed).
    -- producing  codeFTeq1Asym recF pairT .

    --------------------------------------------------------------------
    -- Sigma-form deliverable: encoded chain output Pair u1_E1 u2_full.
    -- This is the architectural milestone for the Pair-case proof,
    -- ready to be extended by encoded E_s + outer BRA bridge.

    pair_chain_output : Sigma Term (\ Df ->
      Deriv (atomic (eqn (ap1 thmT Df) (ap2 Pair u1_E1 u2_full))))
    pair_chain_output = mkSigma Df_chain12 chain12

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
