{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm12.Parts.I
--
-- Theorem 12 case for f = I (the identity functor).
--
-- Goal: build  D_I : Fun1  such that for every Term x,
--     ap1 thmT (ap1 D_I x)  =  codeFTeq1_I x
-- where codeFTeq1_I x  encodes Guard's asymmetric defining equation
-- "I(num x) = num(I x)" :
--     Pair (Pair tagAp1 (Pair (codeF1 I) (cor x))) (cor (I x))
--
-- Strategy (mirrors Parts/Z.agda):
--   1. D_I  =  Comp2 Pair (KT tagCode_axI) cor.
--   2. parDispAxI (cor x)  reduces  thmT(parEncAxI (cor x))  to
--      parOutAxI (cor x) = Pair (Pair tagAp1 (Pair codeF1I (cor x))) (cor x).
--   3. Bridge: parOutAxI (cor x) -> codeFTeq1_I x .  Differs only in the
--      RHS slot ( cor x  vs  cor (I x) ).  Provable from  cong1 cor (axI x).

module BRA2.Thm12.Parts.I where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Cor
open import BRA2.Thm.Tag using (tagAxI)
open import BRA2.Thm.ThmT using (thmT ; tagCode_axI)
open import BRA2.Thm12.Param.AxI using (parDispAxI ; parEncAxI ; parOutAxI)

------------------------------------------------------------------------
-- D_I .

D_I : Fun1
D_I = Comp2 Pair (KT tagCode_axI) cor

------------------------------------------------------------------------
-- The asymmetric encoded equation, parametric in x.

codeFTeq1_I : Term -> Term
codeFTeq1_I x =
  ap2 Pair
    (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 I)) (ap1 cor x)))
    (ap1 cor (ap1 I x))

------------------------------------------------------------------------
-- Combinator reduction:  ap1 D_I x = parEncAxI (cor x) .

D_I_reduce : (x : Term) ->
  Deriv (atomic (eqn (ap1 D_I x) (parEncAxI (ap1 cor x))))
D_I_reduce x =
  let s1 : Deriv (atomic (eqn (ap1 D_I x)
              (ap2 Pair (ap1 (KT tagCode_axI) x) (ap1 cor x))))
      s1 = axComp2 Pair (KT tagCode_axI) cor x

      s2 : Deriv (atomic (eqn (ap1 (KT tagCode_axI) x) tagCode_axI))
      s2 = axKT (natCode tagAxI) (natCode_isValue tagAxI) x
  in ruleTrans s1 (congL Pair (ap1 cor x) s2)

------------------------------------------------------------------------
-- Bridge:  parOutAxI (cor x) = codeFTeq1_I x .
--
-- Both have outer shape  Pair (Pair tagAp1 (Pair codeF1I (cor x))) <RHS>
-- where the RHS differs:
--   parOutAxI : cor x
--   codeFTeq1_I : cor (I x)
-- And  cor x = cor (I x)  by  ruleSym (cong1 cor (axI x)) .

bridgePair : (x : Term) ->
  Deriv (atomic (eqn (parOutAxI (ap1 cor x)) (codeFTeq1_I x)))
bridgePair x =
  let codeF1I_T : Term
      codeF1I_T = reify (codeF1 I)

      pairAp1 : Term
      pairAp1 = ap2 Pair (reify tagAp1) (ap2 Pair codeF1I_T (ap1 cor x))

      sym_bridge : Deriv (atomic (eqn (ap1 cor x) (ap1 cor (ap1 I x))))
      sym_bridge = ruleSym (cong1 cor (axI x))
  in congR Pair pairAp1 sym_bridge

------------------------------------------------------------------------
-- D_correct_I .

D_correct_I : (x : Term) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 D_I x)) (codeFTeq1_I x)))
D_correct_I x =
  let r_red : Deriv (atomic (eqn (ap1 D_I x) (parEncAxI (ap1 cor x))))
      r_red = D_I_reduce x

      r_thmT : Deriv (atomic (eqn (ap1 thmT (ap1 D_I x))
                                   (ap1 thmT (parEncAxI (ap1 cor x)))))
      r_thmT = cong1 thmT r_red

      r_disp : Deriv (atomic (eqn (ap1 thmT (parEncAxI (ap1 cor x)))
                                    (parOutAxI (ap1 cor x))))
      r_disp = parDispAxI (ap1 cor x)

      r_bridge : Deriv (atomic (eqn (parOutAxI (ap1 cor x)) (codeFTeq1_I x)))
      r_bridge = bridgePair x
  in ruleTrans r_thmT (ruleTrans r_disp r_bridge)
