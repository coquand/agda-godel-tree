{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14TPrime -- Guard's  t'  numeral (guard15.pdf p.17) :
--
--     th(t')  =  "x_0 = x_1  ⊃  x_0 ≠ x_1  ⊃  0 = 1"
--
-- This is the encoded derivation of the negation-elimination schema for
-- equality , with the two free meta-variables  x_0 , x_1 .  In Guard's
-- proof of Theorem 14 ,  t'  serves as the schema that  h(x)  ( built
-- via two ruleInst-style substitutions instantiating  x_0 := "th(x_)"
-- and  x_1 := "sub(i,i)" )  decodes through .
--
-- BRA4 construction .  Take the meta-Agda Hilbert derivation
--
--      axExFalso A falseF
--        :  Deriv (imp A (imp (neg A) falseF))
--
-- ( BRA3.Contrapositive.axExFalso ;  proved from  axK + axS + axNeg  )
-- with  A = atomic (eqn (var 0) (var 1))  the open eq formula and
--  falseF = atomic (eqn O (ap1 s O))  ( BRA4.Code ) the "0 = 1" formula .
--
-- Then  t' := encode (axExFalso A falseF)  is a CLOSED BRA Term , and by
-- the verifier-completeness theorem  thmT_complete_rec  :
--
--      Deriv (eqF (ap1 thmT t') (codeFormula F_prime))
--
-- where  F_prime  =  imp A (imp (neg A) falseF) .

module BRA4.Thm.Thm14TPrime where

open import BRA4.Base
open import BRA4.Code              using ( codeFormula ; falseF )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Encode            using ( encode )
open import BRA4.ThmTCompleteRec   using ( thmT_complete_rec )
open import BRA3.Contrapositive    using ( axExFalso )

------------------------------------------------------------------------
-- The open equation  A  ( = "x_0 = x_1" )  with  x_0 = var 0 , x_1 = var 1 .

A_eq : Formula
A_eq = atomic (eqn (var zero) (var (suc zero)))

------------------------------------------------------------------------
-- The Guard schema  F'  :  Deriv-level statement "x_0 = x_1 ⊃ x_0 ≠ x_1 ⊃ 0 = 1" .

F_prime : Formula
F_prime = imp A_eq (imp (neg A_eq) falseF)

------------------------------------------------------------------------
-- The meta-Agda Deriv of  F_prime  via  axExFalso  ( BRA3.Contrapositive ).

derivFPrime : Deriv F_prime
derivFPrime = axExFalso A_eq falseF

------------------------------------------------------------------------
-- Guard's  t'  -- the encoded derivation Term .  Closed (no free vars) .

t_prime : Term
t_prime = encode derivFPrime

------------------------------------------------------------------------
-- Verifier completeness :  thmT(t')  =Deriv=  codeFormula F' .

thmT_t_prime : Deriv (eqF (ap1 thmT t_prime) (codeFormula F_prime))
thmT_t_prime = thmT_complete_rec derivFPrime
