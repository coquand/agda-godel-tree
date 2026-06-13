{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIIImg -- surprise-Goedel-II from IMAGE consistency.
--
--   surpriseGII_img : ConImage -> Deriv falseF
--
-- Verbatim mirror of  T4.SurpriseGIINum  with the consistency hypothesis
-- weakened from  ConOpenInt  ( T proves  thmT(x) <> code(0=1)  for EVERY x )
-- to  ConImage  ( T4.ConImageDef :  T proves it only for  x = gFunN w , the
-- image of the Chaitin diagonal transformer ).   The descent ( now via
-- T4.StageReachImg ) and the final clash both consume  conImg  ONLY at
-- image points, so the proof goes through unchanged.
--
-- CONSEQUENCE ( the point of this file ) .  Combined with
-- T4.ConImageDef.fromOpen : ConOpenInt -> ConImage , this STRENGTHENS
-- Goedel II : it is enough for  T  to prove the consistency of the single
-- fragment  { gFunN w : w a Term }  ( the Kritchman-Raz / Chaitin diagonal
-- programs ) for  T  to be inconsistent.   Global self-consistency is NOT
-- needed -- only image self-consistency.
--
-- It does NOT discharge the hypothesis :  ConImage is itself a  Deriv
-- ( an assumed  T-proof ) , and by Goedel I it is unprovable in  T -- for
-- if  bra : ConImage  held in  T , then  surpriseGII_img bra : Deriv falseF
-- would make  T  inconsistent.   See  T4.ConImageObstruction .

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
open import T4.ConImageDef using ( ConImage )
open import T4.SurpriseG2.BigConjFormula using ( trueF ; countDays )
open import T4.CountDaysLemmas using ( countDays_above )
open import T4.StagePredFN
  using ( bigConjCountN ; openFuel ; BigConjFormulaN ; StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( frontEnd2N ; KdefBigConjNF ; F1 )

module T4.SurpriseGIIImg (Lstar : Nat) (conImg : ConImage) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.StageReachImg Lstar conImg using ( stageN )

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

feN : Deriv (imp (BigConjFormulaN N (suc N) picks0) Q)
feN = frontEnd2N picks0 N M N (le-refl N) stageN bound0

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

vK : Term
vK = mpBuild (encode (coverBridgeN M N)) vQ

v' : Term
v' = mpBuild (encode (guardRw N)) vK

surpriseGII_img : Deriv falseF
surpriseGII_img =
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
      conH = conImg v'
  in mp (negToImpFalse (eqF (ap1 thmT (gFunN v')) codeFalse) conH) chaitin
