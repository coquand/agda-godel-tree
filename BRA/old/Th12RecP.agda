{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12RecP -- schematic Theorem 12 for RecP s (binary recursive Fun2).
--
-- Parametric over s : Fun2.
--
-- RecP s : Fun2 with axRecPLf and axRecPNd:
--   axRecPLf s p           : ap2 (RecP s) p O = O
--   axRecPNd s p a b       : ap2 (RecP s) p (Pair a b)
--                              = ap2 s (Pair p (Pair a b))
--                                      (Pair (ap2 (RecP s) p a)
--                                            (ap2 (RecP s) p b))
--
-- This module proves Theorem 12 for RecP s at any leaf-input (p, O)
-- concretely, and Pair-case  (p, Pair v1 v2)  parametric in IH records
-- at v1, v2 plus IH for s applied at the appropriate point.
--
-- Variable convention: this file follows the encoding-trick suggestion
-- from BRA/NEXT-SESSION-RECP-TREEEQ.md: x at var 0 (recursion variable),
-- p at var 1 (parameter, kept fresh). With this layout, ruleIndBT on var 0
-- inducts on x (the tree being recursed) while keeping p free.
--
-- Pattern adapted from BRA/Th12Rec.agda (which does the same for Fun1
-- Rec z s).  Generalises to binary; the encoding-trick lets us reuse
-- the existing sbt2 / thmTDispRuleInst2_param infrastructure (no sbt3
-- needed).
--
-- No postulates, no holes.

module BRA.Th12RecP where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Th12Rec using (IH1Rec ; IH2Rec ; cor_red_pair)
open import BRA.CorOfPair    using (corOfPair)
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axRecPLf ; tagCode_axRecPNd
  ; tagCode_ruleTrans ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRecPLf_param ; thmTDispAxRecPNd_param
  ; thmTDispRuleTrans_param ; thmTDispCongL_param ; thmTDispCongR_param
  ; thmTDispCongL_param_doublelifted
  ; thmTDispCongR_param_doublelifted
  ; thmTDispRuleTrans_param_doublelifted
  ; liftAxiomTwo ; liftedRuleTransTwo
  ; liftedCongLTwo ; liftedCongRTwo )
open import BRA.Thm.Parts.AxRecPLf using (encAxRecPLf ; outAxRecPLf)

------------------------------------------------------------------------
-- IH record for binary recursive Fun2 at a (p, x) point.

record IH2RecP (g : Fun2) (p x : Term) : Set where
  field
    Df    : Term
    fstL  : Term
    fstR  : Term
    shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
    image : Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq2Asym g p x)))

-- Doubly-lifted variant: image at depth 2 (under P1 imp (P2 imp ...)).
-- Used by the Carneiro-style basePair_param construction for Theorem 12
-- of RecP s at universal closure.

record IH2RecP_doublelifted (P1 P2 : Formula) (g : Fun2) (p x : Term) : Set where
  field
    Df    : Term
    fstL  : Term
    fstR  : Term
    shape : Deriv (atomic (eqn (ap1 Fst Df) (ap2 Pair fstL fstR)))
    image : Deriv (P1 imp (P2 imp atomic
              (eqn (ap1 thmT Df) (codeFTeq2Asym g p x))))

------------------------------------------------------------------------
-- Main parametric module.

module Th12RecPCase
  (s : Fun2)
  where

  sT : Term
  sT = reify (codeF2 s)

  recPF : Fun2
  recPF = RecP s

  cf2 : Term
  cf2 = reify (codeF2 recPF)

  pCT : Term
  pCT = reify (codeF2 Pair)

  ----------------------------------------------------------------------
  -- Leaf case (lf): fully concrete, no IH needed.
  --
  -- Df_lf at p = parEncAxRecPLf-style payload (paramaterised by p).
  -- thmTDispAxRecPLf_param dispatches to parOutAxRecPLf sT (cor p).
  -- Bridge to codeFTeq2Asym recPF p O via:
  --   LHS: payload tail (sT, cor p, O) -> the canonical mkAp2T form
  --        with cor p, cor O at variable positions
  --   RHS: O -> cor (recPF p O) via axRecPLf s p + cong1 cor + axRecLf O stepCor

  Df_lf : Term -> Term
  Df_lf p = ap2 Pair tagCode_axRecPLf (ap2 Pair sT (ap1 cor p))

  Th12_F2_RecP_s_at_lf : (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (Df_lf p)) (codeFTeq2Asym recPF p O)))
  Th12_F2_RecP_s_at_lf p =
    let
      cp : Term
      cp = ap1 cor p

      disp : Deriv (atomic (eqn (ap1 thmT (Df_lf p))
                                 (ap2 Pair
                                   (ap2 Pair (reify tagAp2)
                                     (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                               (ap2 Pair cp O)))
                                   O)))
      disp = thmTDispAxRecPLf_param sT cp

      -- LHS bridge: inner O -> cor O.
      cor_O : Deriv (atomic (eqn (ap1 cor O) O))
      cor_O = axRecLf O stepCor

      -- The encoded LHS subterm:
      --   Pair tagAp2 (Pair (Pair (recPCodeHead) sT) (Pair cp O))
      -- equals (after bridge of inner O -> cor O):
      --   Pair tagAp2 (Pair (Pair (recPCodeHead) sT) (Pair cp (cor O)))
      --   which is mkAp2T cf2 cp (cor O).
      --
      -- Specifically  (Pair (recPCodeHead) sT) = reify (codeF2 (RecP s))
      -- by structural unfolding of codeF2.
      --
      -- We bridge the inner O in the (Pair cp O) to (ap1 cor O) via
      -- congR Pair cp (ruleSym cor_O).

      bL_inner : Deriv (atomic (eqn
                  (ap2 Pair cp O) (ap2 Pair cp (ap1 cor O))))
      bL_inner = congR Pair cp (ruleSym cor_O)

      bL : Deriv (atomic (eqn
              (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                        (ap2 Pair cp O))
              (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                        (ap2 Pair cp (ap1 cor O)))))
      bL = congR Pair
              (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
              bL_inner

      bL_outer : Deriv (atomic (eqn
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                              (ap2 Pair cp O)))
                  (mkAp2T cf2 cp (ap1 cor O))))
      bL_outer = congR Pair (reify tagAp2) bL

      -- RHS bridge: O -> cor (recPF p O).
      --   axRecPLf s p : recPF p O = O
      --   cong1 cor    : cor (recPF p O) = cor O
      --   cor_O        : cor O = O
      --   compose + sym: O = cor (recPF p O)

      cor_recP_lf : Deriv (atomic (eqn (ap1 cor (ap2 recPF p O)) O))
      cor_recP_lf = ruleTrans (cong1 cor (axRecPLf s p)) cor_O

      bR : Deriv (atomic (eqn O (ap1 cor (ap2 recPF p O))))
      bR = ruleSym cor_recP_lf

      -- Outer Pair bridges.

      step_LHS : Deriv (atomic (eqn
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                (ap2 Pair cp O)))
                    O)
                  (ap2 Pair (mkAp2T cf2 cp (ap1 cor O)) O)))
      step_LHS = congL Pair O bL_outer

      step_RHS : Deriv (atomic (eqn
                  (ap2 Pair (mkAp2T cf2 cp (ap1 cor O)) O)
                  (ap2 Pair (mkAp2T cf2 cp (ap1 cor O))
                            (ap1 cor (ap2 recPF p O)))))
      step_RHS = congR Pair (mkAp2T cf2 cp (ap1 cor O)) bR

      bridge_total : Deriv (atomic (eqn
                      (ap2 Pair
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                    (ap2 Pair cp O)))
                        O)
                      (codeFTeq2Asym recPF p O)))
      bridge_total = ruleTrans step_LHS step_RHS

    in ruleTrans disp bridge_total

  ----------------------------------------------------------------------
  -- Pair-case overview (parametric in IH records).
  --
  -- For RecP s at (p, Pair v1 v2):
  --
  --   axRecPNd s p v1 v2  gives in BRA:
  --     recPF p (Pair v1 v2) = s (Pair p (Pair v1 v2))
  --                              (Pair (recPF p v1) (recPF p v2))
  --
  -- The encoded form, after applying thmTDispAxRecPNd-style dispatch:
  --   thmT(Df_E1) = Pair u1 u2
  -- where
  --   u1 = mkAp2T cf2 (cor p) (cor (Pair v1 v2))
  --   u2 = mkAp2T sT (mkAp2T pCT (cor p) (cor (Pair v1 v2)))
  --                  (mkAp2T pCT u1_v1 u1_v2)
  --   u1_vi = mkAp2T cf2 (cor p) (cor vi)   -- the encoded recPF at (p, vi)
  --
  -- IHs at v1, v2 (IH2RecP records) bridge u1_vi -> cor (recPF p vi).
  -- IH for s at (Pair p (Pair v1 v2), Pair (recPF p v1)(recPF p v2))
  -- bridges  mkAp2T sT _ _  to  cor (s _ _) .
  -- BRA-level cor reductions via cor_red_pair (imported from Th12Rec)
  -- give the final  cor (recPF p (Pair v1 v2))  using axRecPNd reversed.
  --
  -- This Pair-case construction is structurally identical to Th12Rec's
  -- RecPairCase, with two differences:
  --   1.  Binary form:  Df_lf and Df_E1 take p as an extra runtime arg.
  --   2.  No  zT  (RecP has only the s step, recursing to O at lf).
  --
  -- The full chain composition (~600 LoC) is mechanical engineering
  -- analogous to Thm12RecCheck.agda::RecOSPairCaseFull.thm12_RecOS_pair.
  -- Layered above this module by future glue once the shape proofs and
  -- thmTDispAxRecPNd_param (Term-version) are exported from ThmT.

  ----------------------------------------------------------------------
  -- Pair-case Sigma deliverable, parametric in:
  --   ih_p_v1   : IH2RecP at (p, v1T)  -- the recursive call at v1.
  --   ih_p_v2   : IH2RecP at (p, v2T)  -- the recursive call at v2.
  --   ih_s_bra  : BRA-Deriv form of Theorem 12 for s.
  --   parDispAxRecPNd_param : the missing Term-form dispatcher
  --     (see "Missing infrastructure" note below).
  --
  -- Mirror of BRA.Th12Rec.Th12RecCase.RecPairCase exactly.

  ----------------------------------------------------------------------
  -- Pair case (proved): mirrors Th12Rec.RecPairCase with binary
  -- modifications.  Uses the new thmTDispAxRecPNd_param dispatcher
  -- (now exported from ThmT.agda).

  module RecPPairCase
    (p v1T v2T : Term)
    (ih_p_v1 : IH2RecP recPF p v1T)
    (ih_p_v2 : IH2RecP recPF p v2T)
    (ih_s_bra : (a b : Term) ->
       Deriv (atomic (eqn (mkAp2T sT (ap1 cor a) (ap1 cor b))
                          (ap1 cor (ap2 s a b)))))
    where

    ppairT : Term
    ppairT = ap2 Pair v1T v2T

    cv1 : Term
    cv1 = ap1 cor v1T

    cv2 : Term
    cv2 = ap1 cor v2T

    rec_pv1 : Term
    rec_pv1 = ap2 recPF p v1T

    rec_pv2 : Term
    rec_pv2 = ap2 recPF p v2T

    cp : Term
    cp = ap1 cor p

    -- Encoded forms.
    -- X = encoded cor of (Pair v1 v2) = mkAp2T pCT (cor v1)(cor v2).
    X : Term
    X = ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cv1 cv2))

    -- ppCorPairForm = encoded "Pair p (Pair v1 v2)".
    ppCorPairForm : Term
    ppCorPairForm = ap2 Pair (reify tagAp2)
                      (ap2 Pair pCT (ap2 Pair cp X))

    -- Y_initial = encoded "Pair (RecP s p (cor v1))(RecP s p (cor v2))" pre-IH.
    Y_initial : Term
    Y_initial = ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT (ap2 Pair (mkAp2T cf2 cp cv1) (mkAp2T cf2 cp cv2)))

    -- Y_after_v1 / Y_full as in Rec, but binary IH-encoded.
    Y_after_v1 : Term
    Y_after_v1 = ap2 Pair (reify tagAp2)
                   (ap2 Pair pCT (ap2 Pair (ap1 cor rec_pv1) (mkAp2T cf2 cp cv2)))

    Y_full : Term
    Y_full = ap2 Pair (reify tagAp2)
               (ap2 Pair pCT (ap2 Pair (ap1 cor rec_pv1) (ap1 cor rec_pv2)))

    -- u1_E1 = encoded LHS of axRecPNd output: mkAp2T cf2 cp (mkAp2T pCT cv1 cv2)
    --       = encoded "RecP s (cor p) (Pair v1 v2)".  Note we use cp=cor p
    --       as the pT slot so the chain aligns with codeFTeq2Asym's (cor p).
    u1_E1 : Term
    u1_E1 = ap2 Pair (reify tagAp2)
              (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                (ap2 Pair cp (ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT (ap2 Pair cv1 cv2)))))

    u2_E1 : Term
    u2_E1 = ap2 Pair (reify tagAp2)
              (ap2 Pair sT
                (ap2 Pair
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair pCT (ap2 Pair cp
                      (ap2 Pair (reify tagAp2)
                        (ap2 Pair pCT (ap2 Pair cv1 cv2))))))
                  Y_initial))

    u2_after_v1 : Term
    u2_after_v1 = ap2 Pair (reify tagAp2)
                    (ap2 Pair sT
                      (ap2 Pair
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT (ap2 Pair cp
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair pCT (ap2 Pair cv1 cv2))))))
                        Y_after_v1))

    u2_full : Term
    u2_full = ap2 Pair (reify tagAp2)
                (ap2 Pair sT
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair pCT (ap2 Pair cp
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT (ap2 Pair cv1 cv2))))))
                    Y_full))

    --------------------------------------------------------------------
    -- E1: parDispAxRecPNd at sT, p, cv1, cv2.

    Df_E1 : Term
    Df_E1 = ap2 Pair tagCode_axRecPNd
                (ap2 Pair sT (ap2 Pair cp (ap2 Pair cv1 cv2)))

    E1 : Deriv (atomic (eqn (ap1 thmT Df_E1) (ap2 Pair u1_E1 u2_E1)))
    E1 = thmTDispAxRecPNd_param sT cp cv1 cv2

    --------------------------------------------------------------------
    -- E_v1: parDispCongL on Pair, replaces (mkAp2T cf2 cp cv1) -> (cor rec_pv1).

    Df_E_v1 : Term
    Df_E_v1 = ap2 Pair tagCode_congL
                  (ap2 Pair pCT (ap2 Pair (IH2RecP.Df ih_p_v1) (mkAp2T cf2 cp cv2)))

    E_v1 : Deriv (atomic (eqn (ap1 thmT Df_E_v1)
                              (ap2 Pair Y_initial Y_after_v1)))
    E_v1 = thmTDispCongL_param Pair (mkAp2T cf2 cp cv2) (IH2RecP.Df ih_p_v1)
             (mkAp2T cf2 cp cv1) (ap1 cor rec_pv1)
             (IH2RecP.fstR ih_p_v1) (IH2RecP.fstL ih_p_v1)
             (IH2RecP.shape ih_p_v1) (IH2RecP.image ih_p_v1)

    --------------------------------------------------------------------
    -- E_v2: parDispCongR on Pair, replaces (mkAp2T cf2 cp cv2) -> (cor rec_pv2).

    Df_E_v2 : Term
    Df_E_v2 = ap2 Pair tagCode_congR
                  (ap2 Pair pCT (ap2 Pair (IH2RecP.Df ih_p_v2) (ap1 cor rec_pv1)))

    E_v2 : Deriv (atomic (eqn (ap1 thmT Df_E_v2)
                              (ap2 Pair Y_after_v1 Y_full)))
    E_v2 = thmTDispCongR_param Pair (ap1 cor rec_pv1) (IH2RecP.Df ih_p_v2)
             (mkAp2T cf2 cp cv2) (ap1 cor rec_pv2)
             (IH2RecP.fstR ih_p_v2) (IH2RecP.fstL ih_p_v2)
             (IH2RecP.shape ih_p_v2) (IH2RecP.image ih_p_v2)

    --------------------------------------------------------------------
    -- Lifted versions through outer mkAp2T sT (encoded ppCorPair) _.

    Df_E_v1_lifted : Term
    Df_E_v1_lifted = ap2 Pair tagCode_congR
                       (ap2 Pair sT (ap2 Pair Df_E_v1 ppCorPairForm))

    E_v1_lifted : Deriv (atomic (eqn (ap1 thmT Df_E_v1_lifted)
                                      (ap2 Pair u2_E1 u2_after_v1)))
    E_v1_lifted = thmTDispCongR_param s ppCorPairForm
                    Df_E_v1 Y_initial Y_after_v1
                    _ _ (axFst tagCode_congL _) E_v1

    Df_E_v2_lifted : Term
    Df_E_v2_lifted = ap2 Pair tagCode_congR
                       (ap2 Pair sT (ap2 Pair Df_E_v2 ppCorPairForm))

    E_v2_lifted : Deriv (atomic (eqn (ap1 thmT Df_E_v2_lifted)
                                      (ap2 Pair u2_after_v1 u2_full)))
    E_v2_lifted = thmTDispCongR_param s ppCorPairForm
                    Df_E_v2 Y_after_v1 Y_full
                    _ _ (axFst tagCode_congR _) E_v2

    --------------------------------------------------------------------
    -- chain1, chain12: encoded chain composition.

    Df_chain1 : Term
    Df_chain1 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1 Df_E_v1_lifted)

    chain1 : Deriv (atomic (eqn (ap1 thmT Df_chain1)
                                 (ap2 Pair u1_E1 u2_after_v1)))
    chain1 = thmTDispRuleTrans_param Df_E1 Df_E_v1_lifted
              u1_E1 u2_E1 u2_E1 u2_after_v1
              _ _ (axFst tagCode_axRecPNd _) E1 E_v1_lifted

    Df_chain12 : Term
    Df_chain12 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1 Df_E_v2_lifted)

    chain12 : Deriv (atomic (eqn (ap1 thmT Df_chain12)
                                  (ap2 Pair u1_E1 u2_full)))
    chain12 = thmTDispRuleTrans_param Df_chain1 Df_E_v2_lifted
               u1_E1 u2_after_v1 u2_after_v1 u2_full
               _ _ (axFst tagCode_ruleTrans _) chain1 E_v2_lifted

    --------------------------------------------------------------------
    -- BRA-level outer bridge to codeFTeq2Asym recPF p ppairT.
    --
    -- LHS: u1_E1 = mkAp2T cf2 cp X -> mkAp2T cf2 cp (cor ppairT)
    --   via congR + ruleSym (corOfPair v1T v2T)  to bridge X = cor ppairT.
    -- RHS: u2_full = mkAp2T sT ppCorPair Y_full -> cor (recPF p ppairT) via:
    --   step a:  ppCorPair = mkAp2T pCT cp X -> cor (Pair p ppairT)
    --     via ruleSym corOfPair on the inner X part, then ruleSym corOfPair on Pair cp _.
    --   step b:  Y_full = mkAp2T pCT (cor rec_pv1)(cor rec_pv2) -> cor (Pair rec_pv1 rec_pv2)
    --     via ruleSym corOfPair.
    --   step c:  mkAp2T sT (cor(Pair p ppairT))(cor(Pair rec_pv1 rec_pv2))
    --              -> cor (s (Pair p ppairT)(Pair rec_pv1 rec_pv2))   [ih_s_bra]
    --   step d:  cor (s (Pair p ppairT)(Pair rec_pv1 rec_pv2)) -> cor (recPF p ppairT)
    --     via cong1 cor (ruleSym (axRecPNd s p v1T v2T)).

    bridge_X_to_corPpairT : Deriv (atomic (eqn X (ap1 cor ppairT)))
    bridge_X_to_corPpairT = ruleSym (corOfPair v1T v2T)

    bridge_u1_E1 : Deriv (atomic (eqn u1_E1
                                   (mkAp2T cf2 cp (ap1 cor ppairT))))
    bridge_u1_E1 =
      congR Pair (reify tagAp2)
        (congR Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
          (congR Pair cp bridge_X_to_corPpairT))

    -- ppCorPair = mkAp2T pCT cp X.  Bridge to cor (Pair p ppairT):
    --   step1: X -> cor ppairT, giving mkAp2T pCT cp (cor ppairT) = mkAp2T pCT (cor p)(cor ppairT).
    --   step2: ruleSym (corOfPair p ppairT) gives mkAp2T pCT (cor p)(cor ppairT) = cor (Pair p ppairT).

    bridge_ppCorPair_a : Deriv (atomic (eqn
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp X)))
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp (ap1 cor ppairT))))))
    bridge_ppCorPair_a =
      congR Pair (reify tagAp2)
        (congR Pair pCT
          (congR Pair cp bridge_X_to_corPpairT))

    bridge_ppCorPair_to_cor : Deriv (atomic (eqn
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp (ap1 cor ppairT))))
       (ap1 cor (ap2 Pair p ppairT))))
    bridge_ppCorPair_to_cor = ruleSym (corOfPair p ppairT)

    bridge_ppCorPair : Deriv (atomic (eqn
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp X)))
       (ap1 cor (ap2 Pair p ppairT))))
    bridge_ppCorPair = ruleTrans bridge_ppCorPair_a bridge_ppCorPair_to_cor

    -- Bridge Y_full to cor (Pair rec_pv1 rec_pv2) via ruleSym corOfPair.
    bridge_Y_full : Deriv (atomic (eqn Y_full
                                    (ap1 cor (ap2 Pair rec_pv1 rec_pv2))))
    bridge_Y_full = ruleSym (corOfPair rec_pv1 rec_pv2)

    -- Bridge u2_full's first arg (encoded ppCorPair) to cor (Pair p ppairT).
    u2_after_first : Term
    u2_after_first = ap2 Pair (reify tagAp2)
                       (ap2 Pair sT
                         (ap2 Pair (ap1 cor (ap2 Pair p ppairT)) Y_full))

    bridge_u2_a : Deriv (atomic (eqn u2_full u2_after_first))
    bridge_u2_a =
      congR Pair (reify tagAp2)
        (congR Pair sT
          (congL Pair Y_full bridge_ppCorPair))

    -- Bridge Y_full -> cor (Pair rec_pv1 rec_pv2).
    u2_after_both : Term
    u2_after_both = ap2 Pair (reify tagAp2)
                      (ap2 Pair sT
                        (ap2 Pair (ap1 cor (ap2 Pair p ppairT))
                                  (ap1 cor (ap2 Pair rec_pv1 rec_pv2))))

    bridge_u2_b : Deriv (atomic (eqn u2_after_first u2_after_both))
    bridge_u2_b =
      congR Pair (reify tagAp2)
        (congR Pair sT
          (congR Pair (ap1 cor (ap2 Pair p ppairT)) bridge_Y_full))

    -- u2_after_both = mkAp2T sT (cor(Pair p ppairT))(cor(Pair rec_pv1 rec_pv2)).
    -- Apply ih_s_bra at (Pair p ppairT, Pair rec_pv1 rec_pv2):

    bridge_u2_c : Deriv (atomic (eqn u2_after_both
                                    (ap1 cor (ap2 s (ap2 Pair p ppairT)
                                                    (ap2 Pair rec_pv1 rec_pv2)))))
    bridge_u2_c = ih_s_bra (ap2 Pair p ppairT) (ap2 Pair rec_pv1 rec_pv2)

    -- Final step: cor (s (Pair p ppairT)(Pair rec_pv1 rec_pv2)) -> cor (recPF p ppairT)
    -- via cong1 cor (ruleSym (axRecPNd s p v1T v2T)).

    recP_unfold : Deriv (atomic (eqn (ap2 recPF p ppairT)
                                     (ap2 s (ap2 Pair p ppairT)
                                            (ap2 Pair rec_pv1 rec_pv2))))
    recP_unfold = axRecPNd s p v1T v2T

    bridge_u2_d : Deriv (atomic (eqn (ap1 cor (ap2 s (ap2 Pair p ppairT)
                                                     (ap2 Pair rec_pv1 rec_pv2)))
                                      (ap1 cor (ap2 recPF p ppairT))))
    bridge_u2_d = cong1 cor (ruleSym recP_unfold)

    bridge_u2_full : Deriv (atomic (eqn u2_full (ap1 cor (ap2 recPF p ppairT))))
    bridge_u2_full =
      ruleTrans bridge_u2_a
        (ruleTrans bridge_u2_b (ruleTrans bridge_u2_c bridge_u2_d))

    --------------------------------------------------------------------
    -- Final outer bridge: combine LHS and RHS bridges.

    bridge_outer : Deriv (atomic (eqn (ap2 Pair u1_E1 u2_full)
                                       (codeFTeq2Asym recPF p ppairT)))
    bridge_outer =
      ruleTrans (congL Pair u2_full bridge_u1_E1)
                (congR Pair (mkAp2T cf2 cp (ap1 cor ppairT)) bridge_u2_full)

    thm12_RecP_s_pair :
      Sigma Term (\ Df ->
        Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq2Asym recPF p ppairT))))
    thm12_RecP_s_pair =
      mkSigma Df_chain12 (ruleTrans chain12 bridge_outer)

  ----------------------------------------------------------------------
  -- Doubly-lifted Pair-case Sigma (mirror of RecPPairCase, lifted under
  -- P1 imp (P2 imp ...)).  Used by the Carneiro-style basePair_param
  -- construction for Theorem 12 of RecP s at universal closure.
  --
  -- All non-IH dispatchers (axRecPNd, axiom-only equational rules) lift
  -- via liftAxiomTwo.  IH-using dispatchers use _doublelifted variants.
  -- ih_s_bra is axiom-only (per s) and lifts via liftAxiomTwo.

  module RecPPairCase_doublelifted
    (P1 P2 : Formula)
    (p v1T v2T : Term)
    (ih_p_v1_dl : IH2RecP_doublelifted P1 P2 recPF p v1T)
    (ih_p_v2_dl : IH2RecP_doublelifted P1 P2 recPF p v2T)
    (ih_s_bra : (a b : Term) ->
       Deriv (atomic (eqn (mkAp2T sT (ap1 cor a) (ap1 cor b))
                          (ap1 cor (ap2 s a b)))))
    where

    -- Term-level shorthands (same as RecPPairCase).

    ppairT : Term
    ppairT = ap2 Pair v1T v2T

    cv1 : Term
    cv1 = ap1 cor v1T

    cv2 : Term
    cv2 = ap1 cor v2T

    rec_pv1 : Term
    rec_pv1 = ap2 recPF p v1T

    rec_pv2 : Term
    rec_pv2 = ap2 recPF p v2T

    cp : Term
    cp = ap1 cor p

    X : Term
    X = ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cv1 cv2))

    Y_initial : Term
    Y_initial = ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT (ap2 Pair (mkAp2T cf2 cp cv1) (mkAp2T cf2 cp cv2)))

    Y_after_v1 : Term
    Y_after_v1 = ap2 Pair (reify tagAp2)
                   (ap2 Pair pCT (ap2 Pair (ap1 cor rec_pv1) (mkAp2T cf2 cp cv2)))

    Y_full : Term
    Y_full = ap2 Pair (reify tagAp2)
               (ap2 Pair pCT (ap2 Pair (ap1 cor rec_pv1) (ap1 cor rec_pv2)))

    u1_E1 : Term
    u1_E1 = ap2 Pair (reify tagAp2)
              (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                (ap2 Pair cp (ap2 Pair (reify tagAp2)
                  (ap2 Pair pCT (ap2 Pair cv1 cv2)))))

    u2_E1 : Term
    u2_E1 = ap2 Pair (reify tagAp2)
              (ap2 Pair sT
                (ap2 Pair
                  (ap2 Pair (reify tagAp2)
                    (ap2 Pair pCT (ap2 Pair cp
                      (ap2 Pair (reify tagAp2)
                        (ap2 Pair pCT (ap2 Pair cv1 cv2))))))
                  Y_initial))

    u2_after_v1 : Term
    u2_after_v1 = ap2 Pair (reify tagAp2)
                    (ap2 Pair sT
                      (ap2 Pair
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT (ap2 Pair cp
                            (ap2 Pair (reify tagAp2)
                              (ap2 Pair pCT (ap2 Pair cv1 cv2))))))
                        Y_after_v1))

    u2_full : Term
    u2_full = ap2 Pair (reify tagAp2)
                (ap2 Pair sT
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair pCT (ap2 Pair cp
                        (ap2 Pair (reify tagAp2)
                          (ap2 Pair pCT (ap2 Pair cv1 cv2))))))
                    Y_full))

    Df_E1 : Term
    Df_E1 = ap2 Pair tagCode_axRecPNd
                (ap2 Pair sT (ap2 Pair cp (ap2 Pair cv1 cv2)))

    Df_E_v1 : Term
    Df_E_v1 = ap2 Pair tagCode_congL
                  (ap2 Pair pCT (ap2 Pair (IH2RecP_doublelifted.Df ih_p_v1_dl)
                                          (mkAp2T cf2 cp cv2)))

    Df_E_v2 : Term
    Df_E_v2 = ap2 Pair tagCode_congR
                  (ap2 Pair pCT (ap2 Pair (IH2RecP_doublelifted.Df ih_p_v2_dl)
                                          (ap1 cor rec_pv1)))

    ppCorPairForm : Term
    ppCorPairForm = ap2 Pair (reify tagAp2)
                      (ap2 Pair pCT (ap2 Pair cp X))

    ----------------------------------------------------------------
    -- Doubly-lifted dispatcher chain.

    E1_dl : Deriv (P1 imp (P2 imp atomic
              (eqn (ap1 thmT Df_E1) (ap2 Pair u1_E1 u2_E1))))
    E1_dl = liftAxiomTwo P1 P2 (thmTDispAxRecPNd_param sT cp cv1 cv2)

    E_v1_dl : Deriv (P1 imp (P2 imp atomic
                (eqn (ap1 thmT Df_E_v1) (ap2 Pair Y_initial Y_after_v1))))
    E_v1_dl = thmTDispCongL_param_doublelifted Pair (mkAp2T cf2 cp cv2)
                (IH2RecP_doublelifted.Df ih_p_v1_dl)
                (mkAp2T cf2 cp cv1) (ap1 cor rec_pv1)
                (IH2RecP_doublelifted.fstR ih_p_v1_dl)
                (IH2RecP_doublelifted.fstL ih_p_v1_dl)
                P1 P2
                (IH2RecP_doublelifted.shape ih_p_v1_dl)
                (IH2RecP_doublelifted.image ih_p_v1_dl)

    E_v2_dl : Deriv (P1 imp (P2 imp atomic
                (eqn (ap1 thmT Df_E_v2) (ap2 Pair Y_after_v1 Y_full))))
    E_v2_dl = thmTDispCongR_param_doublelifted Pair (ap1 cor rec_pv1)
                (IH2RecP_doublelifted.Df ih_p_v2_dl)
                (mkAp2T cf2 cp cv2) (ap1 cor rec_pv2)
                (IH2RecP_doublelifted.fstR ih_p_v2_dl)
                (IH2RecP_doublelifted.fstL ih_p_v2_dl)
                P1 P2
                (IH2RecP_doublelifted.shape ih_p_v2_dl)
                (IH2RecP_doublelifted.image ih_p_v2_dl)

    Df_E_v1_lifted : Term
    Df_E_v1_lifted = ap2 Pair tagCode_congR
                       (ap2 Pair sT (ap2 Pair Df_E_v1 ppCorPairForm))

    E_v1_lifted_dl : Deriv (P1 imp (P2 imp atomic
                       (eqn (ap1 thmT Df_E_v1_lifted)
                            (ap2 Pair u2_E1 u2_after_v1))))
    E_v1_lifted_dl = thmTDispCongR_param_doublelifted s ppCorPairForm Df_E_v1
                       Y_initial Y_after_v1
                       _ _
                       P1 P2
                       (axFst tagCode_congL _) E_v1_dl

    Df_E_v2_lifted : Term
    Df_E_v2_lifted = ap2 Pair tagCode_congR
                       (ap2 Pair sT (ap2 Pair Df_E_v2 ppCorPairForm))

    E_v2_lifted_dl : Deriv (P1 imp (P2 imp atomic
                       (eqn (ap1 thmT Df_E_v2_lifted)
                            (ap2 Pair u2_after_v1 u2_full))))
    E_v2_lifted_dl = thmTDispCongR_param_doublelifted s ppCorPairForm Df_E_v2
                       Y_after_v1 Y_full
                       _ _
                       P1 P2
                       (axFst tagCode_congR _) E_v2_dl

    Df_chain1 : Term
    Df_chain1 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_E1 Df_E_v1_lifted)

    chain1_dl : Deriv (P1 imp (P2 imp atomic
                  (eqn (ap1 thmT Df_chain1) (ap2 Pair u1_E1 u2_after_v1))))
    chain1_dl = thmTDispRuleTrans_param_doublelifted Df_E1 Df_E_v1_lifted
                  u1_E1 u2_E1 u2_E1 u2_after_v1
                  _ _
                  P1 P2
                  (axFst tagCode_axRecPNd _) E1_dl E_v1_lifted_dl

    Df_chain12 : Term
    Df_chain12 = ap2 Pair tagCode_ruleTrans (ap2 Pair Df_chain1 Df_E_v2_lifted)

    chain12_dl : Deriv (P1 imp (P2 imp atomic
                   (eqn (ap1 thmT Df_chain12) (ap2 Pair u1_E1 u2_full))))
    chain12_dl = thmTDispRuleTrans_param_doublelifted Df_chain1 Df_E_v2_lifted
                   u1_E1 u2_after_v1 u2_after_v1 u2_full
                   _ _
                   P1 P2
                   (axFst tagCode_ruleTrans _) chain1_dl E_v2_lifted_dl

    ----------------------------------------------------------------
    -- BRA-level outer bridge.  All axiom-only relative to ih_s_bra,
    -- so we build at unlifted level then liftAxiomTwo at the end.

    bridge_X_to_corPpairT : Deriv (atomic (eqn X (ap1 cor ppairT)))
    bridge_X_to_corPpairT = ruleSym (corOfPair v1T v2T)

    bridge_u1_E1 : Deriv (atomic (eqn u1_E1 (mkAp2T cf2 cp (ap1 cor ppairT))))
    bridge_u1_E1 =
      congR Pair (reify tagAp2)
        (congR Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
          (congR Pair cp bridge_X_to_corPpairT))

    bridge_ppCorPair_a : Deriv (atomic (eqn
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp X)))
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp (ap1 cor ppairT))))))
    bridge_ppCorPair_a =
      congR Pair (reify tagAp2)
        (congR Pair pCT
          (congR Pair cp bridge_X_to_corPpairT))

    bridge_ppCorPair_to_cor : Deriv (atomic (eqn
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp (ap1 cor ppairT))))
       (ap1 cor (ap2 Pair p ppairT))))
    bridge_ppCorPair_to_cor = ruleSym (corOfPair p ppairT)

    bridge_ppCorPair : Deriv (atomic (eqn
       (ap2 Pair (reify tagAp2) (ap2 Pair pCT (ap2 Pair cp X)))
       (ap1 cor (ap2 Pair p ppairT))))
    bridge_ppCorPair = ruleTrans bridge_ppCorPair_a bridge_ppCorPair_to_cor

    bridge_Y_full : Deriv (atomic (eqn Y_full (ap1 cor (ap2 Pair rec_pv1 rec_pv2))))
    bridge_Y_full = ruleSym (corOfPair rec_pv1 rec_pv2)

    u2_after_first : Term
    u2_after_first = ap2 Pair (reify tagAp2)
                       (ap2 Pair sT
                         (ap2 Pair (ap1 cor (ap2 Pair p ppairT)) Y_full))

    bridge_u2_a : Deriv (atomic (eqn u2_full u2_after_first))
    bridge_u2_a =
      congR Pair (reify tagAp2)
        (congR Pair sT
          (congL Pair Y_full bridge_ppCorPair))

    u2_after_both : Term
    u2_after_both = ap2 Pair (reify tagAp2)
                      (ap2 Pair sT
                        (ap2 Pair (ap1 cor (ap2 Pair p ppairT))
                                  (ap1 cor (ap2 Pair rec_pv1 rec_pv2))))

    bridge_u2_b : Deriv (atomic (eqn u2_after_first u2_after_both))
    bridge_u2_b =
      congR Pair (reify tagAp2)
        (congR Pair sT
          (congR Pair (ap1 cor (ap2 Pair p ppairT)) bridge_Y_full))

    bridge_u2_c : Deriv (atomic (eqn u2_after_both
                                    (ap1 cor (ap2 s (ap2 Pair p ppairT)
                                                    (ap2 Pair rec_pv1 rec_pv2)))))
    bridge_u2_c = ih_s_bra (ap2 Pair p ppairT) (ap2 Pair rec_pv1 rec_pv2)

    recP_unfold : Deriv (atomic (eqn (ap2 recPF p ppairT)
                                     (ap2 s (ap2 Pair p ppairT)
                                            (ap2 Pair rec_pv1 rec_pv2))))
    recP_unfold = axRecPNd s p v1T v2T

    bridge_u2_d : Deriv (atomic (eqn (ap1 cor (ap2 s (ap2 Pair p ppairT)
                                                     (ap2 Pair rec_pv1 rec_pv2)))
                                      (ap1 cor (ap2 recPF p ppairT))))
    bridge_u2_d = cong1 cor (ruleSym recP_unfold)

    bridge_u2_full : Deriv (atomic (eqn u2_full (ap1 cor (ap2 recPF p ppairT))))
    bridge_u2_full = ruleTrans bridge_u2_a
                       (ruleTrans bridge_u2_b (ruleTrans bridge_u2_c bridge_u2_d))

    bridge_outer : Deriv (atomic (eqn (ap2 Pair u1_E1 u2_full)
                                       (codeFTeq2Asym recPF p ppairT)))
    bridge_outer = ruleTrans (congL Pair u2_full bridge_u1_E1)
                             (congR Pair (mkAp2T cf2 cp (ap1 cor ppairT)) bridge_u2_full)

    bridge_outer_dl : Deriv (P1 imp (P2 imp atomic
                        (eqn (ap2 Pair u1_E1 u2_full)
                             (codeFTeq2Asym recPF p ppairT))))
    bridge_outer_dl = liftAxiomTwo P1 P2 bridge_outer

    ----------------------------------------------------------------
    -- Final doubly-lifted Sigma.

    thm12_RecP_s_pair_dl : Sigma Term (\ Df ->
      Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT Df) (codeFTeq2Asym recPF p ppairT)))))
    thm12_RecP_s_pair_dl = mkSigma Df_chain12
      (liftedRuleTransTwo P1 P2
         (ap1 thmT Df_chain12)
         (ap2 Pair u1_E1 u2_full)
         (codeFTeq2Asym recPF p ppairT)
         chain12_dl bridge_outer_dl)
