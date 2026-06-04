{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.NatEqSoundImp -- the IMP-FORM of  natEqF  forward reflection :
--
--   natEqF_sound_imp : (a b) -> Deriv (imp (eqF (ap2 natEqF a b) (s O)) (eqF a b))
--
-- The meta form  T4.NatEqReflect.natEqF_sound  ( Deriv (natEqF a b = sO) ->
-- Deriv (a = b) ) is not usable under a standing object hypothesis ; the
-- surjectivity-free internal enum-coverage proof threads everything
-- Carneiro-style, so it needs this implication form.   Same mathematics as
-- natEqF_sound, re-derived with the conclusion's premise as the antecedent  P .

module T4.NatEqSoundImp where

open import T4.Base
open import T4.Code using ( falseF )

open import BRA3.Church        using ( sub ; isZero )
open import BRA3.ChurchLeq     using ( leq )            -- leq a b = eqF (sub a b) O
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.ChurchT52     using ( T52 )
open import BRA3.ChurchIsZeroEq using ( isZeroSO_to_zero )
open import BRA3.ChurchT80     using ( exFalsoFromSO )
open import BRA3.Contrapositive using ( identP ; compI ; bComb ; axContrapos )
open import T4.Counting        using ( antisym_curry ; impFalseToNeg_imp )
open import T4.Thm12.ImpHelpers using ( impLift )
open import T4.NatEqReflect    using ( factO ; factS ; app2 )

natEqF_sound_imp :
  (a b : Term) ->
  Deriv (imp (eqF (ap2 natEqF a b) (ap1 s O)) (eqF a b))
natEqF_sound_imp a b =
  let N  : Term
      N  = ap2 natEqF a b
      Z1 : Term
      Z1 = ap1 isZero (ap2 sub a b)
      Z2 : Term
      Z2 = ap1 isZero (ap2 sub b a)
      P  : Formula
      P  = eqF N (ap1 s O)

      -- t1 :  under P ,  N = O  ->  s O = O   ( transitivity, P = (N = sO) ).
      t1 : Deriv (imp P (imp (eqF N O) (eqF (ap1 s O) O)))
      t1 = ax_eqTrans N (ap1 s O) O

      -- pNfalse :  under P ,  N = O  ->  falseF .
      pNfalse : Deriv (imp P (imp (eqF N O) falseF))
      pNfalse =
        app2 (impLift {P} (impLift {eqF N O} (exFalsoFromSO falseF))) t1

      -- pNneg :  under P ,  N /= O .
      pNneg : Deriv (imp P (neg (eqF N O)))
      pNneg = compI pNfalse (impFalseToNeg_imp (eqF N O))

      -- pZ1nz :  under P ,  Z1 /= O   ( contrapose  factO : (Z1=O) -> (N=O) ).
      pZ1nz : Deriv (imp P (neg (eqF Z1 O)))
      pZ1nz = compI pNneg (mp (axContrapos (eqF Z1 O) (eqF N O)) (factO a b))

      -- pZ1sO :  under P ,  Z1 = s O   ( T52 ).
      pZ1sO : Deriv (imp P (eqF Z1 (ap1 s O)))
      pZ1sO = compI pZ1nz (ruleInst 0 (ap2 sub a b) T52)

      -- pNZ2 :  under P ,  N = Z2   ( factS ).
      pNZ2 : Deriv (imp P (eqF N Z2))
      pNZ2 = compI pZ1sO (factS a b)

      -- pZ2sO :  under P ,  Z2 = s O   ( Z2 = N = s O ).
      pZ2sO : Deriv (imp P (eqF Z2 (ap1 s O)))
      pZ2sO = bComb (bComb (impLift {P} (ax_eqTrans N Z2 (ap1 s O))) pNZ2)
                    (identP P)

      -- leq a b  and  leq b a   ( isZeroSO_to_zero ;  leq x y = (sub x y = O) ).
      pLeqab : Deriv (imp P (leq a b))
      pLeqab = compI pZ1sO (ruleInst 0 (ap2 sub a b) isZeroSO_to_zero)

      pLeqba : Deriv (imp P (leq b a))
      pLeqba = compI pZ2sO (ruleInst 0 (ap2 sub b a) isZeroSO_to_zero)

      -- antisymmetry closes.
      result : Deriv (imp P (eqF a b))
      result = bComb (bComb (impLift {P} (antisym_curry a b)) pLeqab) pLeqba
  in result
