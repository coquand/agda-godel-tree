{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KrBridgeRevN -- the REVERSE conj-bridge  K_rest  =>  Kr x0 = O  ( the other
-- half of  Kr 's characterisation,  Kr x0=O  <=>  K(x0,p(r+1),...,pN) ).
--
--   krBridgeRev start k :
--     imp (bigConjCountN (suc k) start picks openFuel)        -- /\ describes
--         (eqF (ap1 (KrFold start k) (var 0)) O)              -- Kr x0 = O
--
-- "if every day is described then every fail indicator is O, so the sum is O".
-- Dual of  T4.KrBridgeN.krBridgeN  :  each conjunct's describe  runProgN p x0 = s d
-- forces  natEqF = s O  ( natEqF_self_univ ), hence  defIndN = s O , hence the fail
-- isZero(defIndN) = O  ( TisZeroSucc ) ;  the fails are summed to  O  by
-- sigma_both_zero_imp  ( the forward sigma-zero, dual to  sigmaZeroL/R ).

open import T4.Base
open import BRA3.Church using ( isZero ; pi ; sigma ; TisZeroSucc )
open import T4.ParseN using ( runProgN )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.SubT.NatEqRefl using ( natEqF_self_univ )
open import BRA3.Contrapositive using ( identP ; compI )
open import T4.Counting using ( sigma_both_zero_imp )
open import T4.DefIndN using ( defIndN )
open import T4.DefIndReflN using ( defIndN_at_pi )
open import T4.SurpriseG2.AndLemmas using ( fstAndImp ; sndAndImp )
open import T4.SurpriseG2.BigConjFormula using ( trueF )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impEqTrans ; impCong1 ; impCongR ; impRuleSym )
open import T4.StagePredFN using ( describeAtN ; bigConjCountN ; openFuel )

module T4.KrBridgeRevN (picks : Nat -> Nat) where

open import T4.KrFoldN picks
  using ( failTermN ; failTermN_eq ; KrFold ; KrFold_succ )

------------------------------------------------------------------------
-- The per-day REVERSE reflection :  day described => its fail is O.

dayReflectRev :
  (d : Nat) ->
  Deriv (imp (describeAtN (picks d) d (var zero))
             (eqF (ap1 (failTermN d) (var zero)) O))
dayReflectRev d =
  let A : Term
      A = ap2 runProgN (natCode (picks d)) (var zero)
      B : Term
      B = ap1 s (natCode d)
      Hd : Formula
      Hd = eqF A B
      diN : Term
      diN = ap2 defIndN (natCode (picks d)) (ap2 pi (natCode d) (var zero))

      -- under Hd ( A = B ) :  natEqF A B = natEqF A A = s O .
      e_nat : Deriv (imp Hd (eqF (ap2 natEqF A B) (ap1 s O)))
      e_nat =
        impEqTrans {Hd} (ap2 natEqF A B) (ap2 natEqF A A) (ap1 s O)
          (impCongR {Hd} natEqF B A A (impRuleSym (identP Hd)))
          (impLift {Hd} (natEqF_self_univ A))

      e_diSO : Deriv (imp Hd (eqF diN (ap1 s O)))
      e_diSO =
        impEqTrans {Hd} diN (ap2 natEqF A B) (ap1 s O)
          (impLift {Hd} (defIndN_at_pi (natCode (picks d)) (natCode d) (var zero)))
          e_nat

      e_iz : Deriv (imp Hd (eqF (ap1 isZero diN) O))
      e_iz =
        impEqTrans {Hd} (ap1 isZero diN) (ap1 isZero (ap1 s O)) O
          (impCong1 {Hd} isZero diN (ap1 s O) e_diSO)
          (impLift {Hd} (ruleInst 0 O TisZeroSucc))
  in impEqTrans {Hd} (ap1 (failTermN d) (var zero)) (ap1 isZero diN) O
       (impLift {Hd} (failTermN_eq d (var zero))) e_iz

------------------------------------------------------------------------
-- The reverse bridge.

krBridgeRev :
  (start k : Nat) ->
  Deriv (imp (bigConjCountN (suc k) start picks openFuel)
             (eqF (ap1 (KrFold start k) (var zero)) O))
krBridgeRev start zero =
  compI (fstAndImp (describeAtN (picks start) start (var zero)) trueF)
        (dayReflectRev start)
krBridgeRev start (suc k') =
  let KBC : Formula
      KBC = bigConjCountN (suc (suc k')) start picks openFuel
      headF : Term
      headF = ap1 (failTermN start) (var zero)
      restF : Term
      restF = ap1 (KrFold (suc start) k') (var zero)
      hd : Formula
      hd = describeAtN (picks start) start (var zero)
      tl : Formula
      tl = bigConjCountN (suc k') (suc start) picks openFuel
      headO : Deriv (imp KBC (eqF headF O))
      headO = compI (fstAndImp hd tl) (dayReflectRev start)
      tailO : Deriv (imp KBC (eqF restF O))
      tailO = compI (sndAndImp hd tl) (krBridgeRev (suc start) k')
      sumO : Deriv (imp KBC (eqF (ap2 sigma headF restF) O))
      sumO = sigma_both_zero_imp KBC headF restF headO tailO
  in impEqTrans {KBC} (ap1 (KrFold start (suc k')) (var zero))
       (ap2 sigma headF restF) O
       (impLift {KBC} (KrFold_succ start k' (var zero))) sumO
