{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DIncBC -- the  dInc  production : "T proves Inc[F]" from the input
-- D : imp K_rest (KdefBigConj M enum (natCode r))  and the Sigma_1-lift
-- dKrest_F : "T proves K_rest[F]" .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   dIncFromKrest :
--     (Krest : Formula) ->
--     (D : Deriv (imp Krest (KdefBigConj M enum (natCode r)))) ->   -- frontEnd output
--     (wKrest : Term) ->
--     Deriv (eqF (ap1 thmT wKrest) (codeFormula (substF zero F Krest))) ->  -- dKrest_F
--     Deriv (eqF (ap1 thmT (cmp (encode (ruleInst zero F D)) wKrest))
--                (ap1 (KcodeBC enum F M) (natCode r)))               -- dInc, recogniser shape
--
-- Mechanical wiring ( all SHIPPED ) :
--   * ruleInst 0 F D       : instantiate the shared fuel  var 0 := F .
--   * thmT_complete_rec     : T proves  (K_rest[F] -> Inc[F]) .
--   * encoded_mp  vs dKrest_F : T proves  Inc[F]  ( = code of  substF 0 F Inc ) .
--   * numBridgeF            : bridge that code to the recogniser builder
--                              ap1 (KcodeBC enum F M) (natCode r) .
--
-- This reduces  dInc  to the single honest Sigma_1 obligation  dKrest_F
-- ( "T proves K_rest[F]" , the Kritchman-Raz Eq. 2 aggregation : each
-- closed run  runProg (enum (picks d)) F = s (natCode d)  is provable via
-- CompressComp.dPosComp + RunMono fuel-pin, aggregated by encoded_and ).

module T4.DIncBC where

open import T4.Base
open import T4.ThmT             using ( thmT )
open import T4.Code             using ( codeFormula )
open import T4.Encode           using ( encode )
open import T4.ThmTCompleteRec  using ( thmT_complete_rec )
open import T4.ConInj           using ( cmp )
open import T4.Thm12.EncodedMp  using ( encoded_mp )
open import T4.SurpriseG2.KdefBigConj using ( KdefBigConj )
open import T4.KdefBigConjRecog using ( KcodeBC )
open import T4.KdefBigConjFuelBridge using ( numBridgeF )

module _ (enum : Fun1) (M : Nat) (r : Nat) (F : Term) where

  Inc : Formula
  Inc = KdefBigConj M enum (natCode r)

  dIncFromKrest :
    (Krest : Formula) ->
    (D : Deriv (imp Krest Inc)) ->
    (wKrest : Term) ->
    Deriv (eqF (ap1 thmT wKrest) (codeFormula (substF zero F Krest))) ->
    Deriv (eqF (ap1 thmT (cmp (encode (ruleInst zero F D)) wKrest))
               (ap1 (KcodeBC enum F M) (natCode r)))
  dIncFromKrest Krest D wKrest dKrest_F =
    let DF : Deriv (imp (substF zero F Krest) (substF zero F Inc))
        DF = ruleInst zero F D

        -- T proves  (K_rest[F] -> Inc[F]) .
        dImp : Deriv (eqF (ap1 thmT (encode DF))
                          (codeFormula (imp (substF zero F Krest) (substF zero F Inc))))
        dImp = thmT_complete_rec DF

        -- encoded mp : T proves  Inc[F]  ( = code (substF 0 F Inc) ) .
        mpd : Deriv (eqF (ap1 thmT (cmp (encode DF) wKrest))
                         (codeFormula (substF zero F Inc)))
        mpd = encoded_mp (encode DF) wKrest
                (codeFormula (substF zero F Krest))
                (codeFormula (substF zero F Inc))
                dImp dKrest_F
    in ruleTrans mpd (numBridgeF enum F M r)
