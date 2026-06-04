{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step34N -- clos Steps 3+4 combined, with the diagonal proof-builder  g  named.
--
--   gProof r k ... := mpBuild (wStep2b ...) (D (Kr r k) x0)     ( clos's  g x0 )
--   step34 r k ... : Deriv (imp (eqF (ap1 (Kr r k) (var 0)) O)         -- Kr x0 = O
--                              (eqF (ap1 thmT (gProof r k ...))         -- thmT( g x0 )
--                                   (codeFormula (KdefBigConjNF F1 M r)))) -- = code Q(x1)
--
-- = exactly  T4.Step3N.step3  ( which already folded Step 4 in via
--   imp_encoded_mp ), just with the proof term named  g x0 .

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( KdefBigConjNF ; F1 )

module T4.Step34N (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN picks using ( Kr )
open import T4.Step4N  picks using ( D )
open import T4.Step2bN Lstar picks using ( wStep2b )
open import T4.Step3N  Lstar picks using ( mpBuild ; step3 )

-- clos's  g x0 :  the combined Step-2b implication-proof and Step-4 antecedent-proof.
gProof :
  (r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r -> (bound : PicksBound N M picks) -> Term
gProof r k kEq rleN Sr bound =
  mpBuild (wStep2b r k kEq rleN Sr bound) (ap1 (D (Kr r k)) (var zero))

step34 :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
             (eqF (ap1 thmT (gProof r k kEq rleN Sr bound))
                  (codeFormula (KdefBigConjNF F1 M r))))
step34 r k kEq rleN Sr bound = step3 r k kEq rleN Sr bound
