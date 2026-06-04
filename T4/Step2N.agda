{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step2N -- clos STEP 2 :  encode the Step-1 implication into a  thmT -fact.
--
-- Given  S(r) , clos Step 1 ( T4.KrToQ0N.krToQ0 ) proves the object implication
--   Kr x0 = O  =>  Q(x1)   ( Q = KdefBigConjNF F1 M r ).
-- The meta encoder ( T4.Encode.encode ) turns this derivation into a closed proof
-- term  w , and  thmT_complete_rec  certifies that  T  proves the implication :
--
--   wStep2 r k ... := encode ( krToQ0 ... )
--   step2  r k ... : Deriv (eqF (ap1 thmT (wStep2 r k ...))
--                              (codeFormula (imp (Kr x0 = O) (Q x1))))
--
-- i.e.  thmT(w) = code( Kr x0 = O  =>  Q(x1) ) .   ( N = Bnat , M = Bnat - 1
-- from  L*  via  T4.StageBase0N. )

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import T4.ThmT  using ( thmT )
open import T4.Code  using ( codeFormula )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.SurpriseG2.BigConjFormula using ( countDays )
open import T4.StagePredFN using ( StagePredFN ; PicksBound )
open import T4.StepFrontEnd2N using ( KdefBigConjNF ; F1 )

module T4.Step2N (Lstar : Nat) (picks : Nat -> Nat) where

open import T4.StageBase0N Lstar using ( N ; M )
open import T4.KrFoldN  picks using ( Kr )
open import T4.KrToQ0N  Lstar picks using ( krToQ0 )

-- The encoded proof term  w  of the Step-1 implication.
wStep2 :
  (r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r -> (bound : PicksBound N M picks) -> Term
wStep2 r k kEq rleN Sr bound = encode (krToQ0 r k kEq rleN Sr bound)

-- clos Step 2 :  T proves the Step-1 implication.
step2 :
  (r k : Nat) -> (kEq : Eq (suc k) (countDays N (suc r))) ->
  (rleN : NatLe r N) -> (Sr : StagePredFN N M r) -> (bound : PicksBound N M picks) ->
  Deriv (eqF (ap1 thmT (wStep2 r k kEq rleN Sr bound))
             (codeFormula (imp (eqF (ap1 (Kr r k) (var zero)) O)
                               (KdefBigConjNF F1 M r))))
step2 r k kEq rleN Sr bound = thmT_complete_rec (krToQ0 r k kEq rleN Sr bound)
