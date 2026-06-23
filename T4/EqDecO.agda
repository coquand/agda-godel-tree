{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EqDecO -- a term-equality decision returning  O  iff the two codes are
-- equal:  eqDecO a b = isZero (natEqF a b) .  Both reflection directions, for
-- ARBITRARY term codes (the endpoint conjuncts of the bundled CR qcheck):
--
--   eqDecO_complete : a = b          =>  eqDecO a b = O
--   eqDecO_sound    : eqDecO a b = O  =>  a = b
--
-- complete : a=b => natEqF a b = s O (natEqF_self_univ) => isZero(s O)=O.
-- sound    : isZero(natEqF a b)=O, but under neg(a=b) natEqF a b=O
--            (natEqF_complete) so isZero(natEqF a b)=isZero O=s O ; s O=O false,
--            giving neg(neg(a=b)), then DNE.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.EqDecO where

open import T4.Base
open import T4.Code using ( falseF )

open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Counting using ( negToImpFalse ; impFalseToNeg_imp )
open import T4.Thm12.ImpHelpers using ( impEqTrans ; impLift ; impCong1 )

open import BRA3.Church using ( isZero ; TisZeroZ ; TisZeroSucc )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.SubT.NatEqRefl using ( natEqF_self_univ )
open import BRA3.Logic using ( prependEqLeft ; eqSymImp )
open import BRA3.Contrapositive using ( compI ; DNE )

------------------------------------------------------------------------

eqDecO : Term -> Term -> Term
eqDecO a b = ap1 isZero (ap2 natEqF a b)

eqDecO_complete : (a b : Term) -> Deriv (eqF a b) -> Deriv (eqF (eqDecO a b) O)
eqDecO_complete a b hab =
  let nq_val : Deriv (eqF (ap2 natEqF a b) (ap1 s O))
      nq_val = ruleTrans (congL natEqF b hab) (natEqF_self_univ b)
      isZsO : Deriv (eqF (ap1 isZero (ap1 s O)) O)
      isZsO = ruleInst 0 O TisZeroSucc
  in ruleTrans (cong1 isZero nq_val) isZsO

eqDecO_sound : (a b : Term) -> Deriv (eqF (eqDecO a b) O) -> Deriv (eqF a b)
eqDecO_sound a b h =
  let nq : Formula
      nq = neg (eqF a b)
      w : Term
      w = ap2 natEqF a b
      -- under nq:  w = O  (natEqF_complete), hence  isZero w = isZero O = s O .
      d_natO : Deriv (imp nq (eqF w O))
      d_natO = natEqF_complete a b
      d_cong : Deriv (imp nq (eqF (ap1 isZero w) (ap1 isZero O)))
      d_cong = impCong1 isZero w O d_natO
      d_VsO : Deriv (imp nq (eqF (ap1 isZero w) (ap1 s O)))
      d_VsO = impEqTrans (ap1 isZero w) (ap1 isZero O) (ap1 s O)
                d_cong (impLift TisZeroZ)
      -- combine with  h : isZero w = O  to get  s O = O .
      d_symVsO : Deriv (imp nq (eqF (ap1 s O) (ap1 isZero w)))
      d_symVsO = compI d_VsO (eqSymImp (ap1 isZero w) (ap1 s O))
      d_sOO : Deriv (imp nq (eqF (ap1 s O) O))
      d_sOO = impEqTrans (ap1 s O) (ap1 isZero w) O d_symVsO (impLift h)
      d_false : Deriv (imp nq falseF)
      d_false = compI d_sOO (negToImpFalse (eqF (ap1 s O) O) ax_succ_nonzero)
      dnn : Deriv (neg nq)
      dnn = mp (impFalseToNeg_imp nq) d_false
  in mp (DNE (eqF a b)) dnn
