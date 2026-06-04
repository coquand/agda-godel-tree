{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step4N -- clos STEP 4 :  Sigma_1-completeness of the characteristic atom.
--
--   step4 r k : Deriv (imp (eqF (ap1 (Kr r k) (var 0)) O)               -- Kr x0 = O
--                          (eqF (ap1 thmT (ap1 (D (Kr r k)) (var 0)))    -- thmT( D Kr x0 )
--                               (cEqTm (cAp1f (Kr r k) (num x0)) O)))    -- = code( Kr(num x0)=O )
--
-- "if  Kr x0 = O  then  T  proves  Kr(num x0) = O ".   Built from the shipped
-- imp_thm13_singulary  ( the imp-form  thm13  for a unary atom ), at  f := Kr r k ,
-- x := var 0 , y := O , under the hypothesis  P := (Kr x0 = O)  itself ( identP ).
-- The thm13 RHS is the numeral box  num O ; it is reconciled to the bare  O  ( =
-- Step 2b's antecedent RHS ) by  num_at_O .   D Kr x0 = ap1 (fst (thm12 (Kr r k)))
-- (var 0)  is the diagonal proof-builder.

open import T4.Base
open import BRA3.PairAlgebra using ( Pair )
open import BRA3.Contrapositive using ( identP )
open import T4.Tags using ( tag_eq )
open import T4.Num  using ( num ; num_at_O )
open import T4.ThmT using ( thmT )
open import T4.DefWit using ( cEqTm )
open import T4.CgiClash using ( cAp1f )
open import T4.Thm12.All using ( thm12 ; fst )
open import T4.Thm12.Thm13 using ( codeFXeqY1 )
open import T4.Thm12.ImpThm13 using ( imp_thm13_singulary )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )

module T4.Step4N (picks : Nat -> Nat) where

open import T4.KrFoldN picks using ( Kr )

-- the substituent / diagonal proof-builder.
S0 : Term
S0 = ap1 num (var zero)

D : Fun1 -> Fun1
D f = fst (thm12 f)

step4 :
  (r k : Nat) ->
  Deriv (imp (eqF (ap1 (Kr r k) (var zero)) O)
             (eqF (ap1 thmT (ap1 (D (Kr r k)) (var zero)))
                  (cEqTm (cAp1f (Kr r k) S0) O)))
step4 r k =
  let P : Formula
      P = eqF (ap1 (Kr r k) (var zero)) O

      base : Deriv (imp P (eqF (ap1 thmT (ap1 (D (Kr r k)) (var zero)))
                               (codeFXeqY1 (Kr r k) (var zero) O)))
      base = imp_thm13_singulary (Kr r k) (var zero) O P (identP P)

      -- reconcile the thm13 RHS  num O  to the bare  O .
      e_rhs : Deriv (eqF (codeFXeqY1 (Kr r k) (var zero) O)
                         (cEqTm (cAp1f (Kr r k) S0) O))
      e_rhs = congR Pair (natCode tag_eq)
                (congR Pair (cAp1f (Kr r k) S0) num_at_O)
  in impEqTrans {P} (ap1 thmT (ap1 (D (Kr r k)) (var zero)))
       (codeFXeqY1 (Kr r k) (var zero) O)
       (cEqTm (cAp1f (Kr r k) S0) O)
       base (impLift {P} e_rhs)
