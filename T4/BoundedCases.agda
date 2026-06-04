{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BoundedCases -- bounded case-elimination ( the device for internalising a
-- bounded quantifier ) :
--
--   boundedCases x n Gf :
--     ((m : Nat) -> NatLe m n -> Deriv (imp (eqF x (natCode m)) Gf)) ->
--     Deriv (imp (leq x (natCode n)) Gf)
--
-- "if  Gf  follows from  x = m  for every  m <= n , and  x <= n , then  Gf ".
-- By induction on  n , the step a  leq -succ case-split ( BRA3.ChurchT82 :
-- leq x (s y) ->  ~(leq x y) -> x = s y ).   This collapses the object bound
-- leq x (natCode n)  into the finite disjunction of numeral cases  x = natCode m ,
-- the internal form of "a bounded value is one of finitely many numerals".
-- ( Gf  not  C : the latter is the combinator constructor. )

module T4.BoundedCases where

open import T4.Base
open import BRA3.Church         using ( sub )
open import BRA3.ChurchLeq      using ( leq )
open import BRA3.ChurchSubSucc  using ( T_sub_O )
open import BRA3.ChurchT82      using ( T82 )
open import BRA3.Logic          using ( prependEqLeft )
open import BRA3.ChurchCM       using ( caseElim )
open import BRA3.Contrapositive using ( identP ; compI )
open import BRA3.ChurchT80      using ( impFlip )
open import BRA3.RuleInst2      using ( NatLe ; le-zero ; le-refl ; le-suc-right ; ruleInst2 )
open import T4.NatEqReflect     using ( app2 )
open import T4.Thm12.ImpHelpers using ( impLift )

leqO_eq : (x : Term) -> Deriv (imp (leq x O) (eqF x O))
leqO_eq x = prependEqLeft x (ap2 sub x O) O (ruleSym (T_sub_O x))

boundedCases :
  (x : Term) (n : Nat) (Gf : Formula) ->
  ((m : Nat) -> NatLe m n -> Deriv (imp (eqF x (natCode m)) Gf)) ->
  Deriv (imp (leq x (natCode n)) Gf)
boundedCases x zero     Gf cases = compI (leqO_eq x) (cases zero (le-zero zero))
boundedCases x (suc n') Gf cases =
  let sn : Term
      sn = ap1 s (natCode n')
      X : Formula
      X = leq x (natCode n')          -- x <= n'
      Rf : Formula
      Rf = imp (leq x sn) Gf          -- (x <= s n') -> Gf

      ih : Deriv (imp (leq x (natCode n')) Gf)
      ih = boundedCases x n' Gf (\ m mle -> cases m (le-suc-right mle))

      branchLeq : Deriv (imp X Rf)
      branchLeq = compI ih (axK Gf (leq x sn))

      t82 : Deriv (imp (leq x sn) (imp (neg X) (eqF x sn)))
      t82 = ruleInst2 0 x 1 (natCode n') refl T82
      caseTop : Deriv (imp (eqF x sn) Gf)
      caseTop = cases (suc n') (le-refl (suc n'))
      branchNleq : Deriv (imp (neg X) Rf)
      branchNleq = app2 (impLift {neg X} (impLift {leq x sn} caseTop)) (impFlip t82)
  in caseElim {X} {neg X} {Rf} (identP (neg X)) branchLeq branchNleq
