{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step3N -- clos STEP 3 :  push provability through the encoded implication.
--
-- Step 2b :  thmT(w') = code( Kr(num x0)=O  =>  Q(x1) )   ( w' = wStep2b ).
-- Step 4  :  Kr x0=O  =>  thmT(D Kr x0) = code( Kr(num x0)=O ) .
-- By the encoded modus ponens ( T4.Thm12.EncodedMp.imp_encoded_mp ) :
--
--   step3 r k ... :
--     Deriv (imp (eqF (ap1 (Kr r k) (var 0)) O)                       -- Kr x0 = O
--                (eqF (ap1 thmT (mpBuild w' (D Kr x0)))               -- thmT( mp w' (D Kr x0) )
--                     (codeFormula (KdefBigConjNF F1 M r))))          -- = code( Q(x1) )
--
-- "if  Kr x0 = O  then  T  proves  K(r) > L* " -- clos Step 3, the encoded
-- consequent  Q  now provable in  T  under the hypothesis  Kr x0 = O .

open import T4.Base
open import BRA3.PairAlgebra using ( Pair )
open import BRA3.RuleInst2 using ( NatLe )
open import T4.Tags using ( tag_mp )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula )
open import T4.DefWit using ( cEqTm )
open import T4.CgiClash using ( cAp1f )
open import T4.Thm12.EncodedMp using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( KdefBigConjNF ; F1 )

module T4.Step3N (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN picks using ( Kr )
open import T4.Step4N  picks using ( S0 ; D ; step4 )
open import T4.Step2bN Lstar picks using ( wStep2b ; step2b )

-- the mp-combined proof term.
mpBuild : Term -> Term -> Term
mpBuild wImp wAnt = ap2 Pair (natCode tag_mp) (ap2 Pair wImp wAnt)

step3 :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
             (eqF (ap1 thmT (mpBuild (wStep2b r k kEq rleN Sr bound)
                                     (ap1 (D (Kr r k)) (var zero))))
                  (codeFormula (KdefBigConjNF F1 M r))))
step3 r k kEq rleN Sr bound =
  let P : Formula
      P = eqF (ap1 (Kr r k) (var zero)) O
      antPart : Term
      antPart = cEqTm (cAp1f (Kr r k) S0) O
      consPart : Term
      consPart = codeFormula (KdefBigConjNF F1 M r)
  in imp_encoded_mp P
       (wStep2b r k kEq rleN Sr bound)
       (ap1 (D (Kr r k)) (var zero))
       antPart consPart
       (impLift {P} (step2b r k kEq rleN Sr bound))
       (step4 r k)
