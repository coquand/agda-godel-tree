{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.Sigma1KdefConj -- Piece 2a of the KdefConj
-- reformulation per  T4/NEXT-SESSION-KDEFCONJ.md  : the Sigma_1
-- internalisation of a closed  Deriv (KdefConj M enum (natCode r))
-- to a closed thmT-fact, in  codeFormula  form ( no  KcodeConj  Fun1
-- bridge yet ).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   sigma1KdefConj :
--     (M : Nat) (enum : Fun1) (r : Nat) ->
--     Deriv (KdefConj M enum (natCode r)) ->
--     Sigma Term (\ w_r ->
--       Deriv (eqF (ap1 thmT w_r)
--                   (codeFormula (KdefConj M enum (natCode r)))))
--
-- One-line glue of the universal meta necessitation
-- thmT_complete_rec  (Hilbert-Bernays derivability condition (1) ,
-- surprise.pdf p.4 ) :
--
--   thmT_complete_rec dKdefConj :
--     Deriv (eqF (ap1 thmT (encode dKdefConj))
--                 (codeFormula (KdefConj M enum (natCode r)))) .
--
-- =====================================================================
-- WHAT IS DEFERRED  (Piece 2c per the handoff).
-- =====================================================================
--
--   * Piece 2c :  Retarget  CGI_core_num_raw  ( and its supporting
--                 DischargeKdef / ChainKdef / CgiClash internals ) at
--                 the new shape .   ~200-300 LoC across 6-8 files .
--
-- With Piece 2b shipped ( KcodeConj + KcodeConj_correct ), this file
-- now provides BOTH the  codeFormula -shape Sigma  AND  the  KcodeConj
-- -shape Sigma  ( which mirrors  the old  ap1 (Kcode L) (natCode r)
-- shape and is what a CGI-Conj will consume ).

module T4.SurpriseG2.Sigma1KdefConj where

open import T4.Base
open import T4.Code                      using ( codeFormula )
open import T4.Encode                    using ( encode )
open import T4.ThmT                      using ( thmT )
open import T4.ThmTCompleteRec           using ( thmT_complete_rec )
open import T4.SurpriseG2.KdefConj       using ( KdefConj )
open import T4.SurpriseG2.KcodeConj      using ( KcodeConj ; KcodeConj_correct )
open import T4.SurpriseG2.CGIConjSpec    using ( Sigma ; mkSigma )

------------------------------------------------------------------------
-- The Sigma_1 internalisation -- one-liner over  thmT_complete_rec .
-- Produces the  codeFormula -shape thmT-fact .

sigma1KdefConj :
  (M : Nat) (enum : Fun1) (r : Nat) ->
  Deriv (KdefConj M enum (natCode r)) ->
  Sigma Term (\ w_r ->
    Deriv (eqF (ap1 thmT w_r)
                (codeFormula (KdefConj M enum (natCode r)))))
sigma1KdefConj M enum r dKdefConj =
  mkSigma (encode dKdefConj) (thmT_complete_rec dKdefConj)

------------------------------------------------------------------------
-- The Kcode-shape variant, mirroring  sigma1KFormula 's old output :
-- thmT (encode d) = ap1 (KcodeConj M enum) (natCode r) .   Uses
-- KcodeConj_correct  as the inverse bridge ( ruleSym ) to align with
-- the future CGI-Conj's expected input shape .

sigma1KdefConj_KcodeShape :
  (M : Nat) (enum : Fun1) (r : Nat) ->
  Deriv (KdefConj M enum (natCode r)) ->
  Sigma Term (\ w_r ->
    Deriv (eqF (ap1 thmT w_r)
                (ap1 (KcodeConj M enum) (natCode r))))
sigma1KdefConj_KcodeShape M enum r dKdefConj =
  let w_r : Term
      w_r = encode dKdefConj

      step1 :
        Deriv (eqF (ap1 thmT w_r)
                    (codeFormula (KdefConj M enum (natCode r))))
      step1 = thmT_complete_rec dKdefConj

      step2 :
        Deriv (eqF (ap1 (KcodeConj M enum) (natCode r))
                    (codeFormula (KdefConj M enum (natCode r))))
      step2 = KcodeConj_correct M enum r

      proof :
        Deriv (eqF (ap1 thmT w_r)
                    (ap1 (KcodeConj M enum) (natCode r)))
      proof = ruleTrans step1 (ruleSym step2)
  in mkSigma w_r proof
