{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SigmaZeroN -- the object "addition is zero iff both summands are zero"
-- facts, the arithmetic core of surprise-GII's single-summand projection
-- ( SURPRISE-GII-NUMBERCODE-HANDOFF S3.3 / S3.4 : "a sum of naturals is 0 iff
-- all summands are 0" ).  Pure BRA arithmetic, Sigma_1-free, reusable.
--
--   succNeqO_imp x : Deriv (imp (eqF (ap1 s x) O) falseF)     ( s x = O  is absurd )
--   sigmaZeroR a b : Deriv (imp (eqF (ap2 sigma a b) O) (eqF b O))
--   sigmaZeroL a b : Deriv (imp (eqF (ap2 sigma a b) O) (eqF a O))
--
-- ( sigma  is BRA addition :  sigma a O = a [T33] ,  sigma a (s n) = s (sigma a n)
-- [T34] , so  a + b = O  forces  b = O  -- else the head is  s _  -- and then
-- a = a + O = a + b = O . )

module T4.SigmaZeroN where

open import T4.Base
open import T4.Code            using ( falseF )
open import BRA3.Church        using ( sigma ; isZero ; T33 ; T34 ; TisZeroSucc ; TisZeroZ )
open import BRA3.Logic         using ( prependEqLeft ; appendEqRight ; eqSymImp )
open import BRA3.RuleInst2     using ( ruleInst2 )
open import BRA3.ChurchT80     using ( exFalsoFromSO )
open import BRA3.Contrapositive using ( compI )
open import T4.Thm12.ImpHelpers using ( impCongR ; impRuleSym ; impEqTrans )

------------------------------------------------------------------------
-- Local identity implication ( mirror CountingObj.identImp ).

identImp : (A : Formula) -> Deriv (imp A A)
identImp A = mp (mp (axS A (imp A A) A) (axK A (imp A A))) (axK A A)

------------------------------------------------------------------------
-- falseF eliminator :  falseF = (O = s O) , so  s O = O  (sym) explodes.

falseF_elim : (X : Formula) -> Deriv (imp falseF X)
falseF_elim X = compI (eqSymImp O (ap1 s O)) (exFalsoFromSO X)

------------------------------------------------------------------------
-- s x = O  is absurd  ( = falseF ) :  apply  isZero  to both sides ,
-- isZero (s x) = O  [TisZeroSucc]  but  isZero O = s O  [TisZeroZ] ,
-- so  O = s O = falseF .

succNeqO_imp : (x : Term) -> Deriv (imp (eqF (ap1 s x) O) falseF)
succNeqO_imp x =
  let H : Formula
      H = eqF (ap1 s x) O

      cong : Deriv (imp H (eqF (ap1 isZero (ap1 s x)) (ap1 isZero O)))
      cong = ax_eqCong1 isZero (ap1 s x) O

      isZ_sx : Deriv (eqF (ap1 isZero (ap1 s x)) O)
      isZ_sx = ruleInst 0 x TisZeroSucc

      t1 : Deriv (imp H (eqF O (ap1 isZero O)))
      t1 = compI cong (prependEqLeft O (ap1 isZero (ap1 s x)) (ap1 isZero O)
                                     (ruleSym isZ_sx))

      t2 : Deriv (imp H (eqF O (ap1 s O)))
      t2 = compI t1 (appendEqRight O (ap1 isZero O) (ap1 s O) TisZeroZ)
  in t2

------------------------------------------------------------------------
-- sigma a b = O  ->  b = O   ( the count-up argument must vanish ).
-- Object induction on  var 0  (the second argument), with  var 1  the first.

private
  sigmaZR_v :
    Deriv (imp (eqF (ap2 sigma (var (suc zero)) (var zero)) O)
               (eqF (var zero) O))
  sigmaZR_v = ruleIndNat zero {P = P} base step
    where
      P : Formula
      P = imp (eqF (ap2 sigma (var (suc zero)) (var zero)) O) (eqF (var zero) O)

      base : Deriv (imp (eqF (ap2 sigma (var (suc zero)) O) O) (eqF O O))
      base = mp (axK (eqF O O) (eqF (ap2 sigma (var (suc zero)) O) O)) (axRefl O)

      step :
        Deriv (imp P
          (imp (eqF (ap2 sigma (var (suc zero)) (ap1 s (var zero))) O)
               (eqF (ap1 s (var zero)) O)))
      step =
        let v1 : Term
            v1 = var (suc zero)
            v0 : Term
            v0 = var zero
            H : Formula
            H = eqF (ap2 sigma v1 (ap1 s v0)) O

            t34i : Deriv (eqF (ap2 sigma v1 (ap1 s v0))
                              (ap1 s (ap2 sigma v1 v0)))
            t34i = ruleInst2 0 v1 1 v0 refl T34

            h1 : Deriv (imp H (eqF (ap1 s (ap2 sigma v1 v0)) O))
            h1 = prependEqLeft (ap1 s (ap2 sigma v1 v0)) (ap2 sigma v1 (ap1 s v0)) O
                               (ruleSym t34i)

            hFalse : Deriv (imp H falseF)
            hFalse = compI h1 (succNeqO_imp (ap2 sigma v1 v0))

            conseq : Deriv (imp H (eqF (ap1 s v0) O))
            conseq = compI hFalse (falseF_elim (eqF (ap1 s v0) O))
        in mp (axK (imp H (eqF (ap1 s v0) O)) P) conseq

sigmaZeroR : (a b : Term) -> Deriv (imp (eqF (ap2 sigma a b) O) (eqF b O))
sigmaZeroR a b = ruleInst2 1 a 0 b refl sigmaZR_v

------------------------------------------------------------------------
-- sigma a b = O  ->  a = O  :   a = sigma a O = sigma a b = O .

sigmaZeroL : (a b : Term) -> Deriv (imp (eqF (ap2 sigma a b) O) (eqF a O))
sigmaZeroL a b =
  let H : Formula
      H = eqF (ap2 sigma a b) O

      hb : Deriv (imp H (eqF b O))
      hb = sigmaZeroR a b

      A : Deriv (imp H (eqF a (ap2 sigma a O)))
      A = mp (axK (eqF a (ap2 sigma a O)) H) (ruleSym (T33 a))

      B : Deriv (imp H (eqF (ap2 sigma a O) (ap2 sigma a b)))
      B = impCongR sigma O b a (impRuleSym hb)

      C : Deriv (imp H (eqF (ap2 sigma a b) O))
      C = identImp H

      t1 : Deriv (imp H (eqF a (ap2 sigma a b)))
      t1 = impEqTrans a (ap2 sigma a O) (ap2 sigma a b) A B
  in impEqTrans a (ap2 sigma a b) O t1 C
