{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12FstSpotCheck
--
-- Concrete sanity check of the corrected V2 analysis (see
-- BRA/THM12-ASYM-FEASIBILITY.md): at the canonical input x = Pair O O,
-- the asymmetric encoded equation  codeFTeq1Asym Fst (ap2 Pair O O)
-- is Deriv-equal to the static GN of the closed BRA formula
--   Fst (Pair O O) = O
-- which is provable by  axFst O O .
--
-- If this typechecks, it confirms the case the prior V1 analysis
-- claimed was broken ("Fst breaks Theorem 12") is in fact closed by
-- a short Deriv chain combining cor's defining equation, axFst, and
-- a few congruences.
--
-- No postulates, no holes.

module BRA.Thm12FstSpotCheck where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym

------------------------------------------------------------------------
-- Static GN of the closed formula  Fst (Pair O O) = O .

static_GN : Term
static_GN = reify (codeFormula (atomic (eqn (ap1 Fst (ap2 Pair O O)) O)))

------------------------------------------------------------------------
-- The bridge lemma.

bridge :
  Deriv (atomic (eqn (codeFTeq1Asym Fst (ap2 Pair O O)) static_GN))
bridge =
  let
    -- (1) cor on the LHS Pair-input reduces to its static GN
    --     via  corOfReify (nd lf lf) .

    s1 : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                             (reify (code (ap2 Pair O O)))))
    s1 = corOfReify (nd lf lf)

    -- (2) cor of the f-applied input reduces to O.
    --     Fst (Pair O O) = O   (axFst)
    --     -> cor (Fst (Pair O O)) = cor O   (cong1 cor)
    --     -> cor O = O   (axRecLf, since cor = Rec O stepCor)
    --     -> cor (Fst (Pair O O)) = O   (ruleTrans).

    s2_axFst : Deriv (atomic (eqn (ap1 Fst (ap2 Pair O O)) O))
    s2_axFst = axFst O O

    s2_cong : Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair O O)))
                                  (ap1 cor O)))
    s2_cong = cong1 cor s2_axFst

    s2_corO : Deriv (atomic (eqn (ap1 cor O) O))
    s2_corO = axRecLf O stepCor

    s2 : Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair O O))) O))
    s2 = ruleTrans s2_cong s2_corO

    -- (3) Lift (1) through the mkAp1T wrapper on the LHS subterm.
    --     mkAp1T G T = ap2 Pair tagAp1T (ap2 Pair G T) .
    --     congR Pair on the (ap2 Pair G T) inner Pair, then again
    --     congR Pair at the outer.

    s3_inner : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF1 Fst)) (ap1 cor (ap2 Pair O O)))
                  (ap2 Pair (reify (codeF1 Fst))
                            (reify (code (ap2 Pair O O))))))
    s3_inner = congR Pair (reify (codeF1 Fst)) s1

    s3 : Deriv (atomic (eqn
            (mkAp1T (reify (codeF1 Fst)) (ap1 cor (ap2 Pair O O)))
            (mkAp1T (reify (codeF1 Fst))
                    (reify (code (ap2 Pair O O))))))
    s3 = congR Pair (reify tagAp1) s3_inner

    -- (4) Combine (3) (LHS subterm rewrite) with (2) (RHS subterm
    --     rewrite) through the outer mkEqT = ap2 Pair structure.

    s4_lhs : Deriv (atomic (eqn
              (mkEqT (mkAp1T (reify (codeF1 Fst)) (ap1 cor (ap2 Pair O O)))
                     (ap1 cor (ap1 Fst (ap2 Pair O O))))
              (mkEqT (mkAp1T (reify (codeF1 Fst))
                             (reify (code (ap2 Pair O O))))
                     (ap1 cor (ap1 Fst (ap2 Pair O O))))))
    s4_lhs = congL Pair (ap1 cor (ap1 Fst (ap2 Pair O O))) s3

    s4_rhs : Deriv (atomic (eqn
              (mkEqT (mkAp1T (reify (codeF1 Fst))
                             (reify (code (ap2 Pair O O))))
                     (ap1 cor (ap1 Fst (ap2 Pair O O))))
              (mkEqT (mkAp1T (reify (codeF1 Fst))
                             (reify (code (ap2 Pair O O))))
                     O)))
    s4_rhs = congR Pair (mkAp1T (reify (codeF1 Fst))
                                 (reify (code (ap2 Pair O O))))
                        s2

  in ruleTrans s4_lhs s4_rhs
