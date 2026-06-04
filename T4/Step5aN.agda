{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step5aN -- the encoded conjunction->KdefN adapter ( clos Step 5, part 1 ).
--
-- Step 34 :  Kr x0=O  =>  thmT(g x0) = code(Q)         ( Q = KdefBigConjNF F1 M r ).
-- coverBridgeN :  Q  =>  KdefForm M r   ( the bounded- forall  KdefN body @ predN
--   := natCode M ), an OBJECT implication, ENCODED by  thmT_complete_rec  and
-- pushed through by  imp_encoded_mp :
--
--   step5a r k ... :
--     Deriv (imp (eqF (ap1 (Kr r k) (var 0)) O)                 -- Kr x0 = O
--                (eqF (ap1 thmT (vDiag r k ...))                -- thmT( v )
--                     (codeFormula (KdefForm M r))))            -- = code( KdefN(r) )
--
-- "if  Kr x0 = O  then  T  proves  K(r) > L*  in the bounded- forall  KdefN form",
-- ready ( modulo  natCode M = NthrN ) for  ChaitinNumGIAbs.chaitinGI_imp .

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.ChurchLeq using ( leq )
open import T4.ParseN using ( runProgN )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.Thm12.EncodedMp using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift )
open import T4.CoverBridgeN using ( coverBridgeN )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( KdefBigConjNF ; F1 )

module T4.Step5aN (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN  picks using ( Kr )
open import T4.Step3N   Lstar picks using ( mpBuild )
open import T4.Step34N  Lstar picks using ( gProof ; step34 )

-- the bounded- forall  KdefN body ( = coverBridgeN's consequent ).
KdefForm : Nat -> Nat -> Formula
KdefForm M' r =
  imp (leq (var zero) (natCode M'))
      (neg (eqF (ap2 runProgN (var zero) F1) (ap1 s (natCode r))))

-- the diagonal proof term :  mp( encode coverBridgeN )( g x0 ) .
vDiag :
  (r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r -> (bound : PicksBound N M picks) -> Term
vDiag r k kEq rleN Sr bound =
  mpBuild (encode (coverBridgeN M r)) (gProof r k kEq rleN Sr bound)

step5a :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
             (eqF (ap1 thmT (vDiag r k kEq rleN Sr bound))
                  (codeFormula (KdefForm M r))))
step5a r k kEq rleN Sr bound =
  let P : Formula
      P = eqF (ap1 (Kr r k) (var zero)) O
      antPart : Term
      antPart = codeFormula (KdefBigConjNF F1 M r)
      consPart : Term
      consPart = codeFormula (KdefForm M r)
  in imp_encoded_mp P
       (encode (coverBridgeN M r))
       (gProof r k kEq rleN Sr bound)
       antPart consPart
       (impLift {P} (thmT_complete_rec (coverBridgeN M r)))
       (step34 r k kEq rleN Sr bound)
