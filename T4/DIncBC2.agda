{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DIncBC2 -- the TWO-FUEL  dInc  production, clos-faithful ( x1 = var 1 kept
-- FREE ).   This is  T4/clos  Steps 2-4 at the two-fuel shape.
--
-- =====================================================================
-- clos Steps 2-4 ( with  x1 free ).
-- =====================================================================
--
-- frontEnd2 gives  D : imp K_rest (KdefBigConjF enum (var 1) M (natCode r))
-- ( K_rest @ x0 = var 0 ,  Inc = phi @ x1 = var 1 ).   clos pins ONLY  x0 := F0
-- ( the  picks  halting bound ) and leaves  x1 = var 1  FREE so the Chaitin
-- diagonal ( Steps 5 ) may choose it :
--
--   Step 2 : ruleInst 0 F0 D ; encode .   ( Inc has no  var 0  -> unchanged. )
--   Step 3 : encoded_mp  vs  dKrest  ( "T proves K_rest[F0]" ).
--   Step 4 : numBridgeF_at  at fuel  var 1 .
--
-- yielding  dInc  in the RECOGNISER shape at the OPEN fuel  var 1 :
--
--   dInc2 :  thmT (cmp (encode (ruleInst 0 F0 D)) wKrest)
--          = ap1 (KcodeBC enum (var 1) M) (natCode r)
--
-- which is EXACTLY the  h  parameter of  T4.ChaitinG1DischargeBC.DischargeBC /
-- *ChainBC  at  fuel := var 1  ( Step 5 ).   Unlike  T4.KdefClash2  ( which
-- pinned  x1 := F1  up front ), here  x1  is never instantiated by us.

module T4.DIncBC2 where

open import T4.Base
open import T4.ThmT             using ( thmT )
open import T4.Code             using ( codeFormula )
open import T4.Kdef             using ( runProg )
open import T4.Encode           using ( encode )
open import T4.ConInj           using ( cmp )
open import T4.ThmTCompleteRec  using ( thmT_complete_rec )
open import T4.Thm12.EncodedMp  using ( encoded_mp )
open import T4.SubstNoVar       using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF ; numBridgeF_at )
open import T4.KdefBigConjRecog using ( KcodeBC )

module _ (enum : Fun1) (M : Nat) (r : Nat) (F0 : Term) where

  Inc1 : Formula                          -- phi @ x1 = var 1  ( the open-x1 Inc )
  Inc1 = KdefBigConjF enum (var (suc zero)) M (natCode r)

  ----------------------------------------------------------------------
  -- substF 0 F0  is VACUOUS on  Inc1  ( var 0 absent ; fuel is var 1 ;
  -- the  natCode  leaves are  NoVar ).   By induction on  M .

  dist0v1_pp : (k : Nat) ->
    Eq (substF zero F0 (perProgNegF enum (var (suc zero)) (natCode r) k))
       (perProgNegF enum (var (suc zero)) (natCode r) k)
  dist0v1_pp k =
    eqTrans
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum z) (var (suc zero)))
                               (ap1 s (substT zero F0 (natCode r)))))
              (substT_NoVar zero F0 (natCode k) (NoVar_natCode k)))
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum (natCode k)) (var (suc zero)))
                               (ap1 s z)))
              (substT_NoVar zero F0 (natCode r) (NoVar_natCode r)))

  dist0v1 : (m : Nat) ->
    Eq (substF zero F0 (KdefBigConjF enum (var (suc zero)) m (natCode r)))
       (KdefBigConjF enum (var (suc zero)) m (natCode r))
  dist0v1 zero    = dist0v1_pp zero
  dist0v1 (suc m) =
    eqTrans
      (eqCong (\ H -> neg (imp H
                            (neg (substF zero F0
                                    (KdefBigConjF enum (var (suc zero)) m (natCode r))))))
              (dist0v1_pp (suc m)))
      (eqCong (\ T -> neg (imp (perProgNegF enum (var (suc zero)) (natCode r) (suc m))
                                (neg T)))
              (dist0v1 m))

  ----------------------------------------------------------------------
  -- dInc at the recogniser shape, fuel  var 1  ( clos Steps 2-4 ).

  dInc2 :
    (Krest : Formula) ->
    (D : Deriv (imp Krest Inc1)) ->                                  -- frontEnd2 output
    (wKrest : Term) ->
    Deriv (eqF (ap1 thmT wKrest) (codeFormula (substF zero F0 Krest))) ->  -- dKrest
    Deriv (eqF (ap1 thmT (cmp (encode (ruleInst zero F0 D)) wKrest))
               (ap1 (KcodeBC enum (var (suc zero)) M) (natCode r)))
  dInc2 Krest D wKrest dKrest =
    let DF : Deriv (imp (substF zero F0 Krest) (substF zero F0 Inc1))
        DF = ruleInst zero F0 D

        dImp : Deriv (eqF (ap1 thmT (encode DF))
                          (codeFormula (imp (substF zero F0 Krest) (substF zero F0 Inc1))))
        dImp = thmT_complete_rec DF

        mpd : Deriv (eqF (ap1 thmT (cmp (encode DF) wKrest))
                         (codeFormula (substF zero F0 Inc1)))
        mpd = encoded_mp (encode DF) wKrest
                (codeFormula (substF zero F0 Krest))
                (codeFormula (substF zero F0 Inc1))
                dImp dKrest

        -- identify  substF 0 F0 Inc1 = Inc1  ( x1 untouched ) :  "T proves Inc1" .
        mpd' : Deriv (eqF (ap1 thmT (cmp (encode DF) wKrest)) (codeFormula Inc1))
        mpd' = eqSubst (\ C -> Deriv (eqF (ap1 thmT (cmp (encode DF) wKrest)) C))
                       (eqCong codeFormula (dist0v1 M)) mpd
    in ruleTrans mpd' (numBridgeF_at enum (var (suc zero)) M r)
