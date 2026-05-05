{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12AsymBaseCases
--
-- Working prototype of asymmetric Theorem 12 at concrete canonical
-- closed inputs, validating the V2 analysis (BRA/THM12-ASYM-FEASIBILITY.md).
--
-- Three instances:
--   thm12_I_at_O          : Sigma-witness for f = I,   x = O
--   thm12_Z_at_O          : Sigma-witness for f = Z,   x = O
--   thm12_Fst_at_PairOO   : Sigma-witness for f = Fst, x = ap2 Pair O O
--
-- Each demonstrates the construction pattern:
--   1. Take the closed Deriv of the un-encoded equation (axI / axZ / axFst).
--   2. encode it -> Sigma Tree witness for the static GN.
--   3. Bridge the static GN to codeFTeq1Asym via cor's defining equation
--      and f's own defining axiom.
--
-- Parameterised by  th : Fun1  and the symmetric  encode  primitive
-- (the same shape used in the existing  BRA.Thm12Abstract ).  No
-- parametric sbDef extension is needed for closed canonical inputs.
--
-- No postulates, no holes.

module BRA.Thm12AsymBaseCases where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym

------------------------------------------------------------------------
-- Module parameters: th and the symmetric encode primitive.

module BaseCases
  (th : Fun1)
  (encode : (P : Formula) -> Deriv P ->
            Sigma Tree (\ y ->
              Deriv (atomic (eqn (ap1 th (reify y)) (reify (codeFormula P))))))
  where

  ------------------------------------------------------------------
  -- thm12_I_at_O : Theorem 12 for f = I at x = O.

  thm12_I_at_O :
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d)) (codeFTeq1Asym I O))))
  thm12_I_at_O =
    let
      F : Formula
      F = atomic (eqn (ap1 I O) O)

      pf : Deriv F
      pf = axI O

      enc : Sigma Tree (\ y -> Deriv (atomic (eqn (ap1 th (reify y))
                                                   (reify (codeFormula F)))))
      enc = encode F pf

      y_I : Tree
      y_I = fst enc

      pf_static : Deriv (atomic (eqn (ap1 th (reify y_I))
                                      (reify (codeFormula F))))
      pf_static = snd enc

      -- reify (codeFormula F)  = mkEqT (mkAp1T (reify (codeF1 I)) O) O
      -- (definitional equality, since code O = lf, reify lf = O.)

      -- Bridge LHS subterm:  O = ap1 cor O   (via axRecLf, reversed).

      bL_O : Deriv (atomic (eqn O (ap1 cor O)))
      bL_O = ruleSym (axRecLf O stepCor)

      bL_inner : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF1 I)) O)
                  (ap2 Pair (reify (codeF1 I)) (ap1 cor O))))
      bL_inner = congR Pair (reify (codeF1 I)) bL_O

      bL : Deriv (atomic (eqn
              (mkAp1T (reify (codeF1 I)) O)
              (mkAp1T (reify (codeF1 I)) (ap1 cor O))))
      bL = congR Pair (reify tagAp1) bL_inner

      -- Bridge RHS subterm:  O = ap1 cor (ap1 I O) .
      --   axI O  : ap1 I O = O
      --   cong1 cor (axI O) : ap1 cor (ap1 I O) = ap1 cor O
      --   axRecLf O stepCor : ap1 cor O = O
      --   ruleTrans + ruleSym : O = ap1 cor (ap1 I O) .

      bR_axI : Deriv (atomic (eqn (ap1 I O) O))
      bR_axI = axI O

      bR_cong : Deriv (atomic (eqn (ap1 cor (ap1 I O)) (ap1 cor O)))
      bR_cong = cong1 cor bR_axI

      bR_corO : Deriv (atomic (eqn (ap1 cor O) O))
      bR_corO = axRecLf O stepCor

      bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 I O)) O))
      bR_combined = ruleTrans bR_cong bR_corO

      bR : Deriv (atomic (eqn O (ap1 cor (ap1 I O))))
      bR = ruleSym bR_combined

      -- Combine through the outer mkEqT structure.

      step1 : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T (reify (codeF1 I)) O) O)
                (ap2 Pair (mkAp1T (reify (codeF1 I)) (ap1 cor O)) O)))
      step1 = congL Pair O bL

      step2 : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T (reify (codeF1 I)) (ap1 cor O)) O)
                (ap2 Pair (mkAp1T (reify (codeF1 I)) (ap1 cor O))
                           (ap1 cor (ap1 I O)))))
      step2 = congR Pair (mkAp1T (reify (codeF1 I)) (ap1 cor O)) bR

      bridge : Deriv (atomic (eqn (reify (codeFormula F))
                                   (codeFTeq1Asym I O)))
      bridge = ruleTrans step1 step2

      pf_final : Deriv (atomic (eqn (ap1 th (reify y_I))
                                     (codeFTeq1Asym I O)))
      pf_final = ruleTrans pf_static bridge

    in mkSigma y_I pf_final

  ------------------------------------------------------------------
  -- thm12_Z_at_O : Theorem 12 for f = Z at x = O.

  thm12_Z_at_O :
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d)) (codeFTeq1Asym Z O))))
  thm12_Z_at_O =
    let
      F : Formula
      F = atomic (eqn (ap1 Z O) O)

      pf : Deriv F
      pf = axZ O

      enc : Sigma Tree (\ y -> Deriv (atomic (eqn (ap1 th (reify y))
                                                   (reify (codeFormula F)))))
      enc = encode F pf

      y_Z : Tree
      y_Z = fst enc

      pf_static : Deriv (atomic (eqn (ap1 th (reify y_Z))
                                      (reify (codeFormula F))))
      pf_static = snd enc

      bL_O : Deriv (atomic (eqn O (ap1 cor O)))
      bL_O = ruleSym (axRecLf O stepCor)

      bL_inner : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF1 Z)) O)
                  (ap2 Pair (reify (codeF1 Z)) (ap1 cor O))))
      bL_inner = congR Pair (reify (codeF1 Z)) bL_O

      bL : Deriv (atomic (eqn
              (mkAp1T (reify (codeF1 Z)) O)
              (mkAp1T (reify (codeF1 Z)) (ap1 cor O))))
      bL = congR Pair (reify tagAp1) bL_inner

      bR_axZ : Deriv (atomic (eqn (ap1 Z O) O))
      bR_axZ = axZ O

      bR_cong : Deriv (atomic (eqn (ap1 cor (ap1 Z O)) (ap1 cor O)))
      bR_cong = cong1 cor bR_axZ

      bR_corO : Deriv (atomic (eqn (ap1 cor O) O))
      bR_corO = axRecLf O stepCor

      bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 Z O)) O))
      bR_combined = ruleTrans bR_cong bR_corO

      bR : Deriv (atomic (eqn O (ap1 cor (ap1 Z O))))
      bR = ruleSym bR_combined

      step1 : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T (reify (codeF1 Z)) O) O)
                (ap2 Pair (mkAp1T (reify (codeF1 Z)) (ap1 cor O)) O)))
      step1 = congL Pair O bL

      step2 : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T (reify (codeF1 Z)) (ap1 cor O)) O)
                (ap2 Pair (mkAp1T (reify (codeF1 Z)) (ap1 cor O))
                           (ap1 cor (ap1 Z O)))))
      step2 = congR Pair (mkAp1T (reify (codeF1 Z)) (ap1 cor O)) bR

      bridge : Deriv (atomic (eqn (reify (codeFormula F))
                                   (codeFTeq1Asym Z O)))
      bridge = ruleTrans step1 step2

      pf_final : Deriv (atomic (eqn (ap1 th (reify y_Z))
                                     (codeFTeq1Asym Z O)))
      pf_final = ruleTrans pf_static bridge

    in mkSigma y_Z pf_final

  ------------------------------------------------------------------
  -- thm12_Fst_at_PairOO : Theorem 12 for f = Fst at x = ap2 Pair O O.
  --
  -- This is the case the prior V1 analysis incorrectly claimed
  -- "breaks Theorem 12."  The correct construction uses
  -- corOfReify (nd lf lf) for the LHS subterm bridge and
  -- axFst O O for the RHS subterm.

  thm12_Fst_at_PairOO :
    Sigma Tree (\ d ->
      Deriv (atomic (eqn (ap1 th (reify d))
                          (codeFTeq1Asym Fst (ap2 Pair O O)))))
  thm12_Fst_at_PairOO =
    let
      F : Formula
      F = atomic (eqn (ap1 Fst (ap2 Pair O O)) O)

      pf : Deriv F
      pf = axFst O O

      enc : Sigma Tree (\ y -> Deriv (atomic (eqn (ap1 th (reify y))
                                                   (reify (codeFormula F)))))
      enc = encode F pf

      y_Fst : Tree
      y_Fst = fst enc

      pf_static : Deriv (atomic (eqn (ap1 th (reify y_Fst))
                                      (reify (codeFormula F))))
      pf_static = snd enc

      -- Bridge LHS subterm:  reify (code (Pair O O)) = ap1 cor (Pair O O).
      --   corOfReify (nd lf lf)  : ap1 cor (ap2 Pair O O) = reify (code (ap2 Pair O O))
      --   ruleSym                 : reify (code (ap2 Pair O O)) = ap1 cor (ap2 Pair O O) .

      bL_corOf : Deriv (atomic (eqn (ap1 cor (ap2 Pair O O))
                                     (reify (code (ap2 Pair O O)))))
      bL_corOf = corOfReify (nd lf lf)

      bL_O : Deriv (atomic (eqn (reify (code (ap2 Pair O O)))
                                  (ap1 cor (ap2 Pair O O))))
      bL_O = ruleSym bL_corOf

      bL_inner : Deriv (atomic (eqn
                  (ap2 Pair (reify (codeF1 Fst))
                            (reify (code (ap2 Pair O O))))
                  (ap2 Pair (reify (codeF1 Fst))
                            (ap1 cor (ap2 Pair O O)))))
      bL_inner = congR Pair (reify (codeF1 Fst)) bL_O

      bL : Deriv (atomic (eqn
              (mkAp1T (reify (codeF1 Fst))
                       (reify (code (ap2 Pair O O))))
              (mkAp1T (reify (codeF1 Fst))
                       (ap1 cor (ap2 Pair O O)))))
      bL = congR Pair (reify tagAp1) bL_inner

      -- Bridge RHS subterm:  O = ap1 cor (ap1 Fst (ap2 Pair O O)) .
      --   axFst O O    : ap1 Fst (ap2 Pair O O) = O
      --   cong1 cor    : ap1 cor (ap1 Fst (ap2 Pair O O)) = ap1 cor O
      --   axRecLf      : ap1 cor O = O
      --   ruleTrans    : ap1 cor (ap1 Fst (ap2 Pair O O)) = O
      --   ruleSym      : O = ap1 cor (ap1 Fst (ap2 Pair O O)) .

      bR_axFst : Deriv (atomic (eqn (ap1 Fst (ap2 Pair O O)) O))
      bR_axFst = axFst O O

      bR_cong : Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair O O)))
                                    (ap1 cor O)))
      bR_cong = cong1 cor bR_axFst

      bR_corO : Deriv (atomic (eqn (ap1 cor O) O))
      bR_corO = axRecLf O stepCor

      bR_combined : Deriv (atomic (eqn (ap1 cor (ap1 Fst (ap2 Pair O O)))
                                        O))
      bR_combined = ruleTrans bR_cong bR_corO

      bR : Deriv (atomic (eqn O (ap1 cor (ap1 Fst (ap2 Pair O O)))))
      bR = ruleSym bR_combined

      -- Combine through the outer mkEqT.

      step1 : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T (reify (codeF1 Fst))
                                   (reify (code (ap2 Pair O O))))
                           O)
                (ap2 Pair (mkAp1T (reify (codeF1 Fst))
                                   (ap1 cor (ap2 Pair O O)))
                           O)))
      step1 = congL Pair O bL

      step2 : Deriv (atomic (eqn
                (ap2 Pair (mkAp1T (reify (codeF1 Fst))
                                   (ap1 cor (ap2 Pair O O)))
                           O)
                (ap2 Pair (mkAp1T (reify (codeF1 Fst))
                                   (ap1 cor (ap2 Pair O O)))
                           (ap1 cor (ap1 Fst (ap2 Pair O O))))))
      step2 = congR Pair (mkAp1T (reify (codeF1 Fst))
                                  (ap1 cor (ap2 Pair O O))) bR

      bridge : Deriv (atomic (eqn (reify (codeFormula F))
                                   (codeFTeq1Asym Fst (ap2 Pair O O))))
      bridge = ruleTrans step1 step2

      pf_final : Deriv (atomic (eqn (ap1 th (reify y_Fst))
                                     (codeFTeq1Asym Fst (ap2 Pair O O))))
      pf_final = ruleTrans pf_static bridge

    in mkSigma y_Fst pf_final
