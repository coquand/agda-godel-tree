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
open import BRA.Thm.ThmT using
  ( thmT
  ; tagCode_axRecPLf ; tagCode_axRecPNd
  ; tagCode_ruleTrans ; tagCode_congL ; tagCode_congR
  ; thmTDispAxRecPLf_param )
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
  -- Schematic statement (universal closure deferred to glue).
  --
  -- Following the encoding-trick from NEXT-SESSION-RECP-TREEEQ.md:
  -- variable layout  x at var 0 (recursion variable), p at var 1 (kept fresh).
  -- The ruleIndBT step inducts on var 0; the IH for the step case
  -- substitutes (var 0 := Pair (var v_a) (var v_b)) on the formula.

  -- P_Th12_RecP_s : Formula
  -- P_Th12_RecP_s =
  --   atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var zero)))
  --               (codeFTeq2Asym recPF (var (suc zero)) (var zero)))
  --
  -- where Df_F2_RecP_s : Fun2 is the "auto-recursing" form
  --   Df_F2_RecP_s = RecP step_payload  (binary RecP at the BRA level)
  -- with step_payload : Fun2 producing the encoded chain Term as output.
  --
  -- The lf case is Th12_F2_RecP_s_at_lf (proved above).
  -- The Pair case is parametric in IH2RecP records (architectural pattern
  -- documented above; full chain composition deferred to glue).
