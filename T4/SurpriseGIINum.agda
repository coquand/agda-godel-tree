{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIINum -- THE HEADLINE :  surprise-Goedel-II on the number-code base.
--
--   surpriseGII_num : Deriv falseF        ( falseF = (0 = 1) )
--
-- "from open-interval consistency  ConOpenInt ,  T  proves  0 = 1 "  ( the
-- Kritchman-Raz / Chaitin surprise-exam descent, number-code shape ).
--
-- The external induction ( T4.StageReachN.stageN ) reaches  S(N)  from  S(0)
-- through the day-r clashes ( r = 0..N-1 ).   This file fires the FINAL day-N
-- clash, where the remaining conjunction  K_rest = BigConjFormulaN N (suc N) =
-- trueF  ( empty, countDays N (suc N) = 0 ) :  so  frontEnd2N  at  r = N  yields
-- the day-N incompressibility  Q = K(N) > L*  UNCONDITIONALLY ( mp with  trueF ),
-- whose provability the Chaitin diagonal turns into  thmT(h) = code(0=1) ,
-- contradicting  ConOpenInt  ->  falseF .
--
-- Only  ConOpenInt  is assumed ;  no postulates, no holes.

open import T4.Base
open import BRA3.PairAlgebra using ( Pair )
open import BRA3.RuleInst2 using ( le-refl ; le-zero )
open import T4.Tags using ( tag_mp )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFalse ; falseF ; codeFormula )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.Counting using ( negToImpFalse )
open import T4.KGodel1BridgeDefN using ( NthrN )
open import T4.KdefN NthrN using ( KdefN ; KcodeN ; KcodeN_correct )
open import T4.KdefRecogN NthrN using ( outKdefN ; outKdefN_correct )
open import T4.ChaitinNumGIAbs using ( chaitinGI_imp ; gFunN )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.SurpriseG2.BigConjFormula using ( trueF ; countDays )
open import T4.CountDaysLemmas using ( countDays_above )
open import T4.StagePredFN
  using ( bigConjCountN ; openFuel ; BigConjFormulaN ; StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( frontEnd2N ; KdefBigConjNF ; F1 )

module T4.SurpriseGIINum (Lstar : Nat) (con : ConOpenInt) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.StageReachN Lstar con using ( stageN )

-- the day-N program choice ( any bounded one ;  picks0 d = 0 <= M ).
picks0 : Nat -> Nat
picks0 _ = 0

open import T4.Step5aN Lstar picks0 using ( KdefForm )
open import T4.Step5bN Lstar picks0 using ( guardRw )

mpBuild : Term -> Term -> Term
mpBuild wImp wAnt = ap2 Pair (natCode tag_mp) (ap2 Pair wImp wAnt)

------------------------------------------------------------------------
-- SECTION 1.  Q = K(N) > L*  proven UNCONDITIONALLY ( empty K_rest = trueF ).

bound0 : PicksBound N M picks0
bound0 d dleN = le-zero M

Q : Formula
Q = KdefBigConjNF F1 M N

-- frontEnd2N at r = N :  imp (BigConjFormulaN N (suc N) picks0) Q  =  imp trueF Q .
feN : Deriv (imp (BigConjFormulaN N (suc N) picks0) Q)
feN = frontEnd2N picks0 N M N (le-refl N) stageN bound0

-- BigConjFormulaN N (suc N) picks0 = trueF  ( countDays N (suc N) = 0 ).
emptyK : Eq (BigConjFormulaN N (suc N) picks0) trueF
emptyK = eqCong (\ c -> bigConjCountN c (suc N) picks0 openFuel) (countDays_above N)

Qproof : Deriv Q
Qproof =
  mp feN
    (eqSubst (\ F -> Deriv F) (eqSym emptyK) (axRefl O))

------------------------------------------------------------------------
-- SECTION 2.  Encode  Q , push through  coverBridgeN + guardRw , fire Chaitin.

open import T4.CoverBridgeN using ( coverBridgeN )

vQ : Term
vQ = encode Qproof

vK : Term                                   -- proves  KdefForm M N
vK = mpBuild (encode (coverBridgeN M N)) vQ

v' : Term                                  -- proves  KdefN (natCode N)
v' = mpBuild (encode (guardRw N)) vK

surpriseGII_num : Deriv falseF
surpriseGII_num =
  let thmQ : Deriv (eqF (ap1 thmT vQ) (codeFormula Q))
      thmQ = thmT_complete_rec Qproof

      thmV : Deriv (eqF (ap1 thmT vK) (codeFormula (KdefForm M N)))
      thmV = encoded_mp (encode (coverBridgeN M N)) vQ
               (codeFormula Q) (codeFormula (KdefForm M N))
               (thmT_complete_rec (coverBridgeN M N)) thmQ

      thmV' : Deriv (eqF (ap1 thmT v') (codeFormula (KdefN (natCode N))))
      thmV' = encoded_mp (encode (guardRw N)) vK
                (codeFormula (KdefForm M N)) (codeFormula (KdefN (natCode N)))
                (thmT_complete_rec (guardRw N)) thmV

      kcode : Deriv (eqF (ap1 thmT v') (ap1 KcodeN (natCode N)))
      kcode = ruleTrans thmV' (ruleSym (KcodeN_correct N))

      outOk : Deriv (eqF (ap1 outKdefN v') (natCode N))
      outOk = outKdefN_correct v' (natCode N) kcode

      anteHyp : Deriv (eqF (ap1 thmT v') (ap1 KcodeN (ap1 outKdefN v')))
      anteHyp = ruleTrans kcode (cong1 KcodeN (ruleSym outOk))

      chaitin : Deriv (eqF (ap1 thmT (gFunN v')) codeFalse)
      chaitin = mp (chaitinGI_imp v') anteHyp

      conH : Deriv (neg (eqF (ap1 thmT (gFunN v')) codeFalse))
      conH = ruleInst 0 (gFunN v') con
  in mp (negToImpFalse (eqF (ap1 thmT (gFunN v')) codeFalse) conH) chaitin
