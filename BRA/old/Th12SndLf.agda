{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Th12SndLf -- Theorem 12 for Snd at the lf-input case.
--
-- Mirror of BRA.Th12FstLf with axFstLf → axSndLf and Fst → Snd everywhere.
-- The Pair-input case still requires the simultaneous double-substitution
-- machinery (subT2 + thmT extension).

module BRA.Th12SndLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor ; stepCor)
open import BRA.StepReduce   using (ktRed)
open import BRA.Thm.Parts.AxSndLf using (encAxSndLf ; outAxSndLf)
open import BRA.Thm.ThmT     using (thmT ; thmTDispAxSndLf)
open import BRA.Thm14CodeFTeqAsym using (codeFTeq1Asym ; mkAp1T ; mkEqT)

------------------------------------------------------------------------
-- Df_F1_Snd_lf : Fun1 (constant Fun1 returning reify encAxSndLf).

Df_F1_Snd_lf : Fun1
Df_F1_Snd_lf = KT (reify encAxSndLf)

------------------------------------------------------------------------
-- Th12_F1_Snd_at_lf : Theorem 12 for Snd at lf-input.

Th12_F1_Snd_at_lf :
  Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Snd_lf O))
                     (codeFTeq1Asym Snd O)))
Th12_F1_Snd_at_lf =
  let
    pcT : Term
    pcT = reify encAxSndLf

    s1 : Deriv (atomic (eqn (ap1 Df_F1_Snd_lf O) pcT))
    s1 = ktRed encAxSndLf O

    s2 : Deriv (atomic (eqn (ap1 thmT (ap1 Df_F1_Snd_lf O))
                             (ap1 thmT pcT)))
    s2 = cong1 thmT s1

    s3 : Deriv (atomic (eqn (ap1 thmT pcT) (reify outAxSndLf)))
    s3 = thmTDispAxSndLf

    bridgeInner : Deriv (atomic (eqn O (ap1 cor O)))
    bridgeInner = ruleSym (axRecLf stepCor)

    bridgeRHS : Deriv (atomic (eqn O (ap1 cor (ap1 Snd O))))
    bridgeRHS =
      ruleSym (ruleTrans (cong1 cor axSndLf) (axRecLf stepCor))

    bridgeLHS : Deriv (atomic (eqn (mkAp1T (reify (codeF1 Snd)) O)
                                    (mkAp1T (reify (codeF1 Snd)) (ap1 cor O))))
    bridgeLHS =
      congR Pair (reify tagAp1)
        (congR Pair (reify (codeF1 Snd)) bridgeInner)

    bridgeFull : Deriv (atomic (eqn (mkEqT (mkAp1T (reify (codeF1 Snd)) O) O)
                                     (codeFTeq1Asym Snd O)))
    bridgeFull =
      ruleTrans (congL Pair O bridgeLHS)
                (congR Pair (mkAp1T (reify (codeF1 Snd)) (ap1 cor O)) bridgeRHS)

    s4 : Deriv (atomic (eqn (reify outAxSndLf) (codeFTeq1Asym Snd O)))
    s4 = bridgeFull

  in ruleTrans s2 (ruleTrans s3 s4)
