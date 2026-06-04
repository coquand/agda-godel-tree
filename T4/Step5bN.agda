{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step5bN -- clos STEP 5 ( fire Chaitin-GI ) + STEP 6's encoded core.
--
--   step5b r k ... :
--     Deriv (imp (eqF (ap1 (Kr r k) (var 0)) O)             -- Kr x0 = O
--                (eqF (ap1 thmT (gFunN v'))                 -- thmT( h x0 )
--                     codeFalse))                            -- = code( 0 = 1 )
--
-- "if  Kr x0 = O  then  T  proves  0 = 1".   Chain ( all under  Kr x0 = O ):
--   * Step 5a : thmT(vDiag) = code( KdefN-form @ predN := natCode Mcount )
--   * guardRw : rewrite the guard numeral  natCode Mcount -> NthrN  ( the SIZE
--       IDENTITY  T4.StageBaseSizeN.sizeId ), encode + encoded_mp ->
--       thmT(v') = code( KdefN(natCode r) @ NthrN )
--   * KcodeN_correct :   thmT(v') = KcodeN(natCode r)
--   * imp_outKdefN_correct :  outKdefN v' = natCode r , so
--       thmT(v') = KcodeN(outKdefN v')
--   * chaitinGI_imp v' :   thmT(gFunN v') = codeFalse .
--
-- The number-code finite set is  { p < NthrN }  ( = base-3 initial segment ), so
-- the old  enum  blocker is gone ;  the guard meets Chaitin's via  sizeId .

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.Church using ( sub )
open import BRA3.Logic using ( prependEqLeft )
open import BRA3.Contrapositive using ( liftP ; compI )
open import T4.ParseN using ( runProgN )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula ; codeFalse )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.Thm12.EncodedMp using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impRuleSym )
open import T4.SigmaZeroN using ( identImp )
open import T4.CoverBridgeN using ( impCompUnder )
open import T4.KGodel1BridgeDefN using ( NthrN )
open import T4.StageBaseSizeN using ( Mcount ; sizeId )
open import T4.KdefN NthrN using ( KdefN ; KcodeN ; KcodeN_correct )
open import T4.KdefRecogN NthrN using ( outKdefN )
open import T4.KdefRecogImpN NthrN using ( imp_outKdefN_correct )
open import T4.ChaitinNumGIAbs using ( chaitinGI_imp ; gFunN )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( F1 )

module T4.Step5bN (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN  picks using ( Kr )
open import T4.Step3N   Lstar picks using ( mpBuild )
open import T4.Step5aN  Lstar picks using ( KdefForm ; vDiag ; step5a )

------------------------------------------------------------------------
-- The guard rewrite  natCode Mcount -> NthrN  ( SIZE IDENTITY ).
-- N.B.  M = Mcount  ( T4.StageBase0N now provides the Chaitin-aligned counts ).

leqNthrToMcount : Deriv (imp (leq (var zero) NthrN) (leq (var zero) (natCode Mcount)))
leqNthrToMcount =
  prependEqLeft (ap2 sub (var zero) (natCode Mcount)) (ap2 sub (var zero) NthrN) O
                (congR sub (var zero) sizeId)

guardRw : (r : Nat) -> Deriv (imp (KdefForm M r) (KdefN (natCode r)))
guardRw r =
  impCompUnder {KdefForm M r} {leq (var zero) NthrN} {leq (var zero) (natCode M)}
               {neg (eqF (ap2 runProgN (var zero) F1) (ap1 s (natCode r)))}
    (liftP (KdefForm M r) leqNthrToMcount)
    (identImp (KdefForm M r))

------------------------------------------------------------------------
-- Step 5b.

vChaitin :
  (r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r -> (bound : PicksBound N M picks) -> Term
vChaitin r k kEq rleN Sr bound =
  mpBuild (encode (guardRw r)) (vDiag r k kEq rleN Sr bound)

step5b :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
             (eqF (ap1 thmT (gFunN (vChaitin r k kEq rleN Sr bound))) codeFalse))
step5b r k kEq rleN Sr bound =
  let P : Formula
      P = eqF (ap1 (Kr r k) (var zero)) O
      v' : Term
      v' = vChaitin r k kEq rleN Sr bound

      thmKdefN : Deriv (imp P (eqF (ap1 thmT v') (codeFormula (KdefN (natCode r)))))
      thmKdefN =
        imp_encoded_mp P (encode (guardRw r)) (vDiag r k kEq rleN Sr bound)
          (codeFormula (KdefForm M r)) (codeFormula (KdefN (natCode r)))
          (impLift {P} (thmT_complete_rec (guardRw r)))
          (step5a r k kEq rleN Sr bound)

      kcode : Deriv (imp P (eqF (ap1 thmT v') (ap1 KcodeN (natCode r))))
      kcode =
        impEqTrans {P} (ap1 thmT v') (codeFormula (KdefN (natCode r)))
          (ap1 KcodeN (natCode r))
          thmKdefN (impLift {P} (ruleSym (KcodeN_correct r)))

      outOk : Deriv (imp P (eqF (ap1 outKdefN v') (natCode r)))
      outOk = imp_outKdefN_correct P v' (natCode r) kcode

      anteHyp : Deriv (imp P (eqF (ap1 thmT v') (ap1 KcodeN (ap1 outKdefN v'))))
      anteHyp =
        impEqTrans {P} (ap1 thmT v') (ap1 KcodeN (natCode r))
          (ap1 KcodeN (ap1 outKdefN v'))
          kcode
          (impRuleSym (impCong1 {P} KcodeN (ap1 outKdefN v') (natCode r) outOk))
  in compI anteHyp (chaitinGI_imp v')
