{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.Parts.Z
--
-- Theorem 12 case for f = Z (the constant-leaf functor; Guard's o).
--
-- Goal: build a singulary functor  D_Z : Fun1  such that for every
-- Term x,
--     ap1 thmT (ap1 D_Z x)  =  codeFTeq1_Z x
-- where  codeFTeq1_Z x  encodes Guard's asymmetric defining equation
-- "Z(num x) = num(Z x)" :
--     Pair (Pair tagAp1 (Pair (codeF1 Z) (cor x))) (cor (Z x))
--
-- Strategy:
--   1. Define  D_Z = Comp2 Pair (KT tagCode_axKT) (Comp2 Pair (KT codeF1Z) cor)
--      so that  ap1 D_Z x  reduces to  parEncAxZ (cor x) .
--   2. Apply  parDispAxZ (cor x) : thmT(parEncAxZ (cor x)) = parOutAxZ (cor x).
--   3. Bridge the difference  parOutAxZ (cor x) -> codeFTeq1_Z x: only the
--      RHS slot differs (O vs cor (Z x)).  Provable via
--        cong1 cor (axZ x)  : cor (Z x) = cor O
--        axRecLf O stepCor  : cor O = O
--      then ruleSym + congR Pair.
--
-- This Parts file uses the ACTUAL ThmT (concrete) and the parametric
-- dispatch from BRA/Thm12/Param/AxZ.  It is not parametric over thmT
-- itself (per the planning doc's spirit; abstraction layer can be added
-- later if needed).

module BRA.Thm12.Parts.Z where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.Tag using (tagAxKT)
open import BRA.Thm.ThmT using (thmT ; tagCode_axKT)
open import BRA.Thm12.Param.AxZ using (parDispAxZ ; parEncAxZ ; parOutAxZ)

------------------------------------------------------------------------
-- D_Z : Fun1 .
--
-- Reads as: build a Pair whose left child is the closed tag-code for
-- axZ , and whose right child is the inner payload  Pair codeF1Z (cor x) .

D_Z : Fun1
D_Z =
  Comp2 Pair
    (KT tagCode_axKT)
    (Comp2 Pair
       (KT (reify (codeF1 Z)))
       cor)

------------------------------------------------------------------------
-- The asymmetric encoded equation, parametric in x.
--
-- LHS-slot uses  ap1 cor x  (Guard's "num x"), RHS uses  ap1 cor (ap1 Z x)
-- (Guard's "num (Z x)").

codeFTeq1_Z : Term -> Term
codeFTeq1_Z x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 Z)) (ap1 cor x)))
    (ap1 cor (ap1 Z x))

------------------------------------------------------------------------
-- Combinator reduction:  ap1 D_Z x = parEncAxZ (cor x) .

D_Z_reduce : (x : Term) ->
  Deriv (atomic (eqn (ap1 D_Z x) (parEncAxZ (ap1 cor x))))
D_Z_reduce x =
  let codeF1Z_T : Term
      codeF1Z_T = reify (codeF1 Z)

      inner : Fun1
      inner = Comp2 Pair (KT codeF1Z_T) cor

      -- axComp2 unfolds D_Z = Comp2 Pair (KT tagCode_axKT) inner.
      s1 : Deriv (atomic (eqn (ap1 D_Z x)
              (ap2 Pair (ap1 (KT tagCode_axKT) x) (ap1 inner x))))
      s1 = axComp2 Pair (KT tagCode_axKT) inner x

      -- KT tagCode_axKT : x -> tagCode_axKT  (axKT at v = natCode tagAxKT,
      -- since  tagCode_axKT = reify (natCode tagAxKT) ).
      s2 : Deriv (atomic (eqn (ap1 (KT tagCode_axKT) x) tagCode_axKT))
      s2 = axKT (natCode tagAxKT) x

      -- axComp2 unfolds  inner = Comp2 Pair (KT codeF1Z_T) cor .
      s3 : Deriv (atomic (eqn (ap1 inner x)
              (ap2 Pair (ap1 (KT codeF1Z_T) x) (ap1 cor x))))
      s3 = axComp2 Pair (KT codeF1Z_T) cor x

      -- KT codeF1Z_T : x -> codeF1Z_T  (axKT at v = codeF1 Z).
      s4 : Deriv (atomic (eqn (ap1 (KT codeF1Z_T) x) codeF1Z_T))
      s4 = axKT (codeF1 Z) x

      -- Stepwise rewrites combining s1..s4 into the final shape.
      r1 : Deriv (atomic (eqn (ap1 D_Z x)
              (ap2 Pair tagCode_axKT (ap1 inner x))))
      r1 = ruleTrans s1 (congL Pair (ap1 inner x) s2)

      r2 : Deriv (atomic (eqn (ap1 inner x)
              (ap2 Pair codeF1Z_T (ap1 cor x))))
      r2 = ruleTrans s3 (congL Pair (ap1 cor x) s4)

      r3 : Deriv (atomic (eqn (ap1 D_Z x)
              (ap2 Pair tagCode_axKT (ap2 Pair codeF1Z_T (ap1 cor x)))))
      r3 = ruleTrans r1 (congR Pair tagCode_axKT r2)
  in r3

------------------------------------------------------------------------
-- Bridge:  parOutAxZ (cor x) = codeFTeq1_Z x .
--
-- Both have outer shape  Pair (Pair tagAp1 (Pair codeF1Z (cor x))) <RHS>
-- where RHS differs:
--   parOutAxZ : O
--   codeFTeq1_Z : cor (Z x)
-- And  cor (Z x) = cor O = O  by  cong1 cor (axZ x) + axRecLf O stepCor .

bridgeRHS : (x : Term) -> Deriv (atomic (eqn (ap1 cor (ap1 Z x)) O))
bridgeRHS x =
  ruleTrans (cong1 cor (axZ x)) (axRecLf O stepCor)

bridgePair : (x : Term) ->
  Deriv (atomic (eqn (parOutAxZ (ap1 cor x)) (codeFTeq1_Z x)))
bridgePair x =
  let codeF1Z_T : Term
      codeF1Z_T = reify (codeF1 Z)

      pairAp1 : Term
      pairAp1 = ap2 Pair (reify tagAp1) (ap2 Pair codeF1Z_T (ap1 cor x))

      sym_bridge : Deriv (atomic (eqn O (ap1 cor (ap1 Z x))))
      sym_bridge = ruleSym (bridgeRHS x)
  in congR Pair pairAp1 sym_bridge

------------------------------------------------------------------------
-- D_correct_Z .  Compose: combinator reduction + dispatch + bridge.

D_correct_Z : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_Z x)) (codeFTeq1_Z x)))
D_correct_Z x =
  let r_red : Deriv (atomic (eqn (ap1 D_Z x) (parEncAxZ (ap1 cor x))))
      r_red = D_Z_reduce x

      r_thmT : Deriv (atomic (eqn (ap1 thmT (ap1 D_Z x))
                                   (ap1 thmT (parEncAxZ (ap1 cor x)))))
      r_thmT = cong1 thmT r_red

      r_disp : Deriv (atomic (eqn (ap1 thmT (parEncAxZ (ap1 cor x)))
                                    (parOutAxZ (ap1 cor x))))
      r_disp = parDispAxZ (ap1 cor x)

      r_bridge : Deriv (atomic (eqn (parOutAxZ (ap1 cor x)) (codeFTeq1_Z x)))
      r_bridge = bridgePair x
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)
