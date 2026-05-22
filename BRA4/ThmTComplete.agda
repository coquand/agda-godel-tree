{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTComplete -- per-constructor pieces of the verifier-completeness
-- theorem.  Each function delivers
--
--   thmT_complete_<rule> :
--     <args + IH-equations> ->
--     Deriv (eqF (ap1 thmT (encode (<rule> args))) (codeFormula <conclusion>))
--
-- for one BRA3.Deriv constructor.  IH equations are taken as separate
-- premises (no Agda-level structural recursion on Deriv), so the
-- consumer can compose the chain to fit any Deriv tree.
--
-- This is the EASY layer of S6 FINAL :
--   * ax_succ_nonzero
--   * axK         (uses thmT_at_axN11)
--   * mp          (uses thmT_at_mp_codeF)
--   * ruleInst    (uses thmT_at_sb + sbfEq_codeFormula)
--   * ruleIndNat  (uses thmT_at_ind_codeF)
--
-- The HARD layer (axN1..axN10, axS, axNeg ; require Closed witnesses
-- on Term parameters to bridge substT k b a = a in the substituted
-- SCHEMA codeFormula) is deferred to BRA4.ThmTCompleteAx* (round 3).
-- See memory entry [[project-bra4-s6-round1-done]].
--
-- USAGE.  A future  thmT_complete : (d : Deriv P) -> ... -> Deriv ...
-- function with structural recursion on  d  is assembled by clients on
-- top of these per-constructor pieces.  This staging lets the client
-- thread the appropriate Closed witnesses at the call site.

module BRA4.ThmTComplete where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Encode
open import BRA4.ThmT      using ( thmT )
open import BRA4.SbF       using ( sbf )
open import BRA4.SbT       using ( sbt )
open import BRA4.SbContract using ( SbContract )
open import BRA4.SbfAtClosures using ( sbContract )
open import BRA4.SbDerived using ( module Derive )

open import BRA4.ThmTAtSb   using ( thmT_at_sb )
open import BRA4.ThmTAtMp   using ( thmT_at_mp_codeF )
open import BRA4.ThmTAtInd  using ( thmT_at_ind_codeF )
open import BRA4.ThmTAtAx0  using ( thmT_at_axN0 )
open import BRA4.ThmTAtAx11 using ( thmT_at_axN11 )

open import BRA3.Church          using ( pi )
open import BRA3.PairAlgebra     using ( axFst ; axSnd )

------------------------------------------------------------------------
-- Specialise sbtEq_codeTerm / sbfEq_codeFormula to BRA4's concrete sbt , sbf .

open Derive sbt sbf sbContract public

------------------------------------------------------------------------
-- CASE  ax_succ_nonzero  :  P = neg (eqF (s O) O) .
-- encode = packAx 0 O .  thmT_at_axN0 O delivers directly.

thmT_complete_ax_succ_nonzero :
  Deriv (eqF (ap1 thmT (encode ax_succ_nonzero))
              (codeFormula (neg (atomic (eqn (ap1 s O) O)))))
thmT_complete_ax_succ_nonzero = thmT_at_axN0 O

------------------------------------------------------------------------
-- CASE  mp dPQ dP .
-- encode (mp dPQ dP) = pi tag_mp (pi (encode dPQ) (encode dP)) .
-- Apply  thmT_at_mp_codeF  directly with the two IH equations.

thmT_complete_mp :
  (P Q : Formula)
  (dPQ : Deriv (imp P Q)) (dP : Deriv P)
  (ih_PQ : Deriv (eqF (ap1 thmT (encode dPQ)) (codeFormula (imp P Q))))
  (ih_P  : Deriv (eqF (ap1 thmT (encode dP))  (codeFormula P))) ->
  Deriv (eqF (ap1 thmT (encode (mp dPQ dP))) (codeFormula Q))
thmT_complete_mp P Q dPQ dP ih_PQ ih_P =
  thmT_at_mp_codeF (encode dPQ) (encode dP) P Q ih_PQ ih_P

------------------------------------------------------------------------
-- CASE  ruleInst k t dP .
-- encode = pi tag_sb (pi (pi (natCode k) (codeTerm t)) (encode dP)) .
-- Chain  thmT_at_sb  +  sbfEq_codeFormula k t P .

thmT_complete_ruleInst :
  (k : Nat) (t : Term) (P : Formula)
  (dP : Deriv P)
  (ih : Deriv (eqF (ap1 thmT (encode dP)) (codeFormula P))) ->
  Deriv (eqF (ap1 thmT (encode (ruleInst k t dP)))
              (codeFormula (substF k t P)))
thmT_complete_ruleInst k t P dP ih =
  let spec : Term
      spec = ap2 Pair (natCode k) (codeTerm t)

      step_sb :
        Deriv (eqF (ap1 thmT (encode (ruleInst k t dP)))
                    (ap2 sbf spec (ap1 thmT (encode dP))))
      step_sb = thmT_at_sb spec (encode dP)

      step_lift :
        Deriv (eqF (ap2 sbf spec (ap1 thmT (encode dP)))
                    (ap2 sbf spec (codeFormula P)))
      step_lift = congR sbf spec ih

      step_codeF :
        Deriv (eqF (ap2 sbf spec (codeFormula P))
                    (codeFormula (substF k t P)))
      step_codeF = sbfEq_codeFormula k t P
  in ruleTrans step_sb (ruleTrans step_lift step_codeF)

------------------------------------------------------------------------
-- CASE  ruleIndNat k {P} dB dS .
-- encode = pi tag_ind (pi (encode dB) (encode dS)) .
-- Apply  thmT_at_ind_codeF  with the step IH normalised so that
-- thmT (encode dS) has the shape  pi tag_imp (pi (codeFormula P) cStepCons) .
-- (Definitional unfold of  codeFormula (imp P (substF ...)) .)

thmT_complete_ruleIndNat :
  (k : Nat) (P : Formula)
  (dB : Deriv (substF k O P))
  (dS : Deriv (imp P (substF k (ap1 s (var k)) P)))
  (ih_base : Deriv (eqF (ap1 thmT (encode dB)) (codeFormula (substF k O P))))
  (ih_step : Deriv (eqF (ap1 thmT (encode dS))
                         (codeFormula (imp P (substF k (ap1 s (var k)) P))))) ->
  Deriv (eqF (ap1 thmT (encode (ruleIndNat k dB dS))) (codeFormula P))
thmT_complete_ruleIndNat k P dB dS ih_base ih_step =
  thmT_at_ind_codeF (encode dB) (encode dS) (codeFormula P)
                     (codeFormula (substF k O P))
                     (codeFormula (substF k (ap1 s (var k)) P))
                     ih_base ih_step

------------------------------------------------------------------------
-- CASE  axK A B .   P = imp A (imp B A) .
-- encode = packAx 11 (pi codeA codeB) .
-- thmT_at_axN11 outputs schema with Fst/Snd projections of  extra ;
-- reduce these via  axFst / axSnd  to get  codeFormula (imp A (imp B A)) .

thmT_complete_axK :
  (A B : Formula) ->
  Deriv (eqF (ap1 thmT (encode (axK A B))) (codeFormula (imp A (imp B A))))
thmT_complete_axK A B =
  let cA : Term
      cA = codeFormula A
      cB : Term
      cB = codeFormula B
      extra : Term
      extra = ap2 Pair cA cB

      raw :
        Deriv (eqF (ap1 thmT (encode (axK A B)))
                    (ap2 pi (natCode tag_imp)
                      (ap2 pi (ap1 Fst extra)
                        (ap2 pi (natCode tag_imp)
                          (ap2 pi (ap1 Snd extra) (ap1 Fst extra))))))
      raw = thmT_at_axN11 extra

      fst_eq : Deriv (eqF (ap1 Fst extra) cA)
      fst_eq = axFst cA cB

      snd_eq : Deriv (eqF (ap1 Snd extra) cB)
      snd_eq = axSnd cA cB

      inner_BA :
        Deriv (eqF (ap2 pi (ap1 Snd extra) (ap1 Fst extra))
                    (ap2 pi cB cA))
      inner_BA = ruleTrans (congL pi (ap1 Fst extra) snd_eq)
                            (congR pi cB fst_eq)

      imp_BA :
        Deriv (eqF (ap2 pi (natCode tag_imp)
                     (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))
                    (ap2 pi (natCode tag_imp) (ap2 pi cB cA)))
      imp_BA = congR pi (natCode tag_imp) inner_BA

      outer :
        Deriv (eqF (ap2 pi (ap1 Fst extra)
                     (ap2 pi (natCode tag_imp)
                       (ap2 pi (ap1 Snd extra) (ap1 Fst extra))))
                    (ap2 pi cA (ap2 pi (natCode tag_imp) (ap2 pi cB cA))))
      outer = ruleTrans (congL pi (ap2 pi (natCode tag_imp)
                                       (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))
                                    fst_eq)
                         (congR pi cA imp_BA)

      final :
        Deriv (eqF (ap2 pi (natCode tag_imp)
                     (ap2 pi (ap1 Fst extra)
                       (ap2 pi (natCode tag_imp)
                         (ap2 pi (ap1 Snd extra) (ap1 Fst extra)))))
                    (codeFormula (imp A (imp B A))))
      final = congR pi (natCode tag_imp) outer
  in ruleTrans raw final
