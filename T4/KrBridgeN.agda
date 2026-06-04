{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KrBridgeN -- the conj-bridge  Kr x0 = O  =>  K_rest(x0)  and the resulting
-- SAME-FUEL clos Step 1  Kr x0 = O  =>  Q(x0)  ( SURPRISE-GII-NUMBERCODE-HANDOFF
-- S3.4 + clos Step 1 ).
--
--   krBridgeN start k : imp ( KrFold start k (var 0) = O )
--                           ( bigConjCountN (suc k) start picks openFuel )
--
-- "the sum-of-fails being zero forces every day described" -- a clean aligned
-- induction now that  KrFold  right-nests like  bigConjCountN .   Each head fail
-- is reflected to its describe equation by  T4.DefIndReflN.failReflectN ; the sum
-- telescopes by  T4.SigmaZeroN.sigmaZeroL/R ;  conjuncts are re-introduced under
-- the common hypothesis by  liftedAndIntro .
--
--   step1N : ... -> imp ( Kr r k (var 0) = O ) ( KdefBigConjN M r )
--
-- = the conj-bridge precomposed with  T4.StepFrontEndN.frontEndN  ( clos Step 1
-- at a single fuel  x0 = var 0 ) :  from  S(r) ,  Kr x0 = O  proves  K(r) > L* .

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.Church    using ( isZero ; pi ; sigma )
open import BRA3.Logic     using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI ; liftP )
open import T4.DefIndN     using ( defIndN )
open import T4.SigmaZeroN  using ( sigmaZeroL ; sigmaZeroR )
open import T4.DefIndReflN using ( failReflectN )
open import T4.SurpriseG2.BigConjFormula using ( trueF ; countDays )
open import T4.SurpriseG2.AndLemmas using ( liftedAndIntro )
open import T4.StagePredFN using ( describeAtN ; bigConjCountN ; openFuel
                                 ; BigConjFormulaN ; StagePredFN ; Picks ; PicksBound )
open import T4.KdefBigConjN using ( KdefBigConjN )
open import T4.StepFrontEndN using ( frontEndN )

module T4.KrBridgeN (picks : Nat -> Nat) where

open import T4.KrFoldN picks
  using ( failTermN ; failTermN_eq ; KrFold ; KrFold_succ ; Kr )

------------------------------------------------------------------------
-- The per-day reflection at fuel  var 0 :  a zero fail = that day described.

dayReflectN :
  (d : Nat) ->
  Deriv (imp (eqF (ap1 (failTermN d) (var zero)) O)
             (describeAtN (picks d) d (var zero)))
dayReflectN d =
  compI (prependEqLeft (ap1 isZero (ap2 defIndN (natCode (picks d))
                                            (ap2 pi (natCode d) (var zero))))
                       (ap1 (failTermN d) (var zero)) O
                       (ruleSym (failTermN_eq d (var zero))))
        (failReflectN (natCode (picks d)) (natCode d) (var zero))

------------------------------------------------------------------------
-- The conj-bridge  KrFold start k (var 0) = O  =>  the day-[start..start+k]
-- big conjunction.   Aligned induction on  k .

krBridgeN :
  (start k : Nat) ->
  Deriv (imp (eqF (ap1 (KrFold start k) (var zero)) O)
             (bigConjCountN (suc k) start picks openFuel))
krBridgeN start zero =
  let X : Formula
      X = eqF (ap1 (failTermN start) (var zero)) O
  in liftedAndIntro X (describeAtN (picks start) start (var zero)) trueF
       (dayReflectN start) (liftP X (axRefl O))
krBridgeN start (suc k') =
  let X : Formula
      X = eqF (ap1 (KrFold start (suc k')) (var zero)) O
      headF : Term
      headF = ap1 (failTermN start) (var zero)
      restF : Term
      restF = ap1 (KrFold (suc start) k') (var zero)
      toSigma : Deriv (imp X (eqF (ap2 sigma headF restF) O))
      toSigma = prependEqLeft (ap2 sigma headF restF)
                  (ap1 (KrFold start (suc k')) (var zero)) O
                  (ruleSym (KrFold_succ start k' (var zero)))
      headO : Deriv (imp X (eqF headF O))
      headO = compI toSigma (sigmaZeroL headF restF)
      restO : Deriv (imp X (eqF restF O))
      restO = compI toSigma (sigmaZeroR headF restF)
      head : Deriv (imp X (describeAtN (picks start) start (var zero)))
      head = compI headO (dayReflectN start)
      tail : Deriv (imp X (bigConjCountN (suc k') (suc start) picks openFuel))
      tail = compI restO (krBridgeN (suc start) k')
  in liftedAndIntro X (describeAtN (picks start) start (var zero))
       (bigConjCountN (suc k') (suc start) picks openFuel) head tail

------------------------------------------------------------------------
-- clos STEP 1 ( same fuel ) :  from  S(r) ,  Kr x0 = O  =>  K(r) > L* .
--   k  must align the fold range with the day count :  suc k = countDays N (suc r) .

step1N :
  (N M r k : Nat) -> Eq (suc k) (countDays N (suc r)) ->
  NatLe r N -> StagePredFN N M r ->
  (bound : PicksBound N M picks) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O) (KdefBigConjN M r))
step1N N M r k kEq rleN Sr bound =
  let br : Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
                      (bigConjCountN (suc k) (suc r) picks openFuel))
      br = krBridgeN (suc r) k
      br' : Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
                       (BigConjFormulaN N (suc r) picks))
      br' = eqSubst
              (\ c -> Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
                                 (bigConjCountN c (suc r) picks openFuel)))
              kEq br
      fe : Deriv (imp (BigConjFormulaN N (suc r) picks) (KdefBigConjN M r))
      fe = frontEndN N M r rleN Sr picks bound
  in compI br' fe
