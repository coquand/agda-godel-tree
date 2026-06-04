{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step2bInvariant -- clos Step 2b, the "right part unchanged" at the CODE
-- level :  the num-installation  sbf (Pair (natCode 0) S0)  ( the  x0 |-> num x0
-- code substitution ) leaves  codeFormula (KdefBigConjF enum (var 1) M (natCode r))
-- UNCHANGED -- because that code has no  var 0  leaf ( fuel is the  var 1  leaf
-- cVarc 1 , programs the closed  enum k , subject the closed  natCode r ).
--
--   rightSbfInv M r :
--     sbf (Pair (natCode 0) S0) (codeFormula (KdefBigConjF enum (var 1) M (natCode r)))
--       = codeFormula (KdefBigConjF enum (var 1) M (natCode r))
--
-- GENERIC in  enum  ( the functor codes stay opaque via  sbt_step_ap1/ap2 ),
-- and in  S0  -- so it composes with  thmT_at_sb  on the closed proof code.

module T4.Step2bInvariant where

open import T4.Base
open import T4.Code using ( codeTerm ; codeFormula )
open import T4.Kdef using ( runProg )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.CgiClash using ( cAp1f ; cAp2f ; cVarc )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt )
open import T4.SbtAtVar using ( sbt_at_var_nomatch )
open import T4.SbStep using
  ( sbf_step_imp ; sbf_step_atomic ; sbf_step_neg ; sbt_step_ap1 ; sbt_step_ap2
  ; NumCode ; ncO ; ncAp1 ; sbt_inert_NumCode )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF )

module _ (enum : Fun1) (S0 : Term) where

  spec0 : Term
  spec0 = ap2 Pair (natCode zero) S0

  ----------------------------------------------------------------------
  -- codeTerm (natCode n)  is a  NumCode .

  numCodeNat : (n : Nat) -> NumCode (codeTerm (natCode n))
  numCodeNat zero    = ncO
  numCodeNat (suc n) = ncAp1 s (codeTerm (natCode n)) (numCodeNat n)

  ----------------------------------------------------------------------
  -- Per-conjunct :  sbf spec0  fixes  codeFormula (perProgNegF ...) .

  perConjInert :
    (r k : Nat) ->
    Deriv (eqF (ap2 sbf spec0 (codeFormula (perProgNegF enum (var (suc zero)) (natCode r) k)))
               (codeFormula (perProgNegF enum (var (suc zero)) (natCode r) k)))
  perConjInert r k =
    let progCode : Term
        progCode = cAp1f enum (codeTerm (natCode k))
        varCode : Term
        varCode = cVarc (suc zero)
        lhs : Term
        lhs = cAp2f runProg progCode varCode
        rhs : Term
        rhs = cAp1f s (codeTerm (natCode r))

        eK : Deriv (eqF (ap2 sbt spec0 (codeTerm (natCode k))) (codeTerm (natCode k)))
        eK = sbt_inert_NumCode (codeTerm (natCode k)) (numCodeNat k) zero S0

        eProg : Deriv (eqF (ap2 sbt spec0 progCode) progCode)
        eProg = sbt_step_ap1 zero S0 enum (codeTerm (natCode k)) (codeTerm (natCode k)) eK

        eVar : Deriv (eqF (ap2 sbt spec0 varCode) varCode)
        eVar = sbt_at_var_nomatch zero (suc zero) S0 refl

        eLHS : Deriv (eqF (ap2 sbt spec0 lhs) lhs)
        eLHS = sbt_step_ap2 zero S0 runProg progCode varCode progCode varCode eProg eVar

        eRHS : Deriv (eqF (ap2 sbt spec0 rhs) rhs)
        eRHS = sbt_inert_NumCode rhs
                 (ncAp1 s (codeTerm (natCode r)) (numCodeNat r)) zero S0

        eAtom : Deriv (eqF (ap2 sbf spec0 (cEqTm lhs rhs)) (cEqTm lhs rhs))
        eAtom = sbf_step_atomic zero S0 lhs rhs lhs rhs eLHS eRHS
    in sbf_step_neg zero S0 (cEqTm lhs rhs) (cEqTm lhs rhs) eAtom

  ----------------------------------------------------------------------
  -- The whole consequent is fixed.

  rightSbfInv :
    (M r : Nat) ->
    Deriv (eqF (ap2 sbf spec0 (codeFormula (KdefBigConjF enum (var (suc zero)) M (natCode r))))
               (codeFormula (KdefBigConjF enum (var (suc zero)) M (natCode r))))
  rightSbfInv zero    r = perConjInert r zero
  rightSbfInv (suc M) r =
    let hd : Term
        hd = codeFormula (perProgNegF enum (var (suc zero)) (natCode r) (suc M))
        tl : Term
        tl = codeFormula (KdefBigConjF enum (var (suc zero)) M (natCode r))

        eTl : Deriv (eqF (ap2 sbf spec0 tl) tl)
        eTl = rightSbfInv M r

        eNegTl : Deriv (eqF (ap2 sbf spec0 (cNeg tl)) (cNeg tl))
        eNegTl = sbf_step_neg zero S0 tl tl eTl

        eImp : Deriv (eqF (ap2 sbf spec0 (cImp hd (cNeg tl))) (cImp hd (cNeg tl)))
        eImp = sbf_step_imp zero S0 hd (cNeg tl) hd (cNeg tl)
                 (perConjInert r (suc M)) eNegTl
    in sbf_step_neg zero S0 (cImp hd (cNeg tl)) (cImp hd (cNeg tl)) eImp
