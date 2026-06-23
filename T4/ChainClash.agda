{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChainClash -- the head-clash capstone: NO join of  ze#  and  su# X  over
-- transparent reduction traces.  This is the object core of Con(T0) for the
-- trace-presented equational theory: if  0  and  s X  had a common reduct  w ,
-- head-stability (T4.ChainHeadStab) forces  hd w = tagZe  AND  hd w = tagSu ,
-- i.e.  O = s O , refuted by  ax_succ_nonzero -- a genuine object  Deriv falseF.
--
-- Combined with confluence over conversion traces (Conv => Join, the remaining
-- piece), this gives  Not (Conv 0 (s 0))  = consistency of the trace-presented
-- T0.  No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ChainClash where

open import T4.Base

open import T4.ChainHeadStab using ( ChainM ; chainHeadZe ; chainHeadSu )
open import T4.TrsCodeObj using ( ze# ; su# ; hd ; tagZe ; tagSu ; hd_ze ; hd_su )

open import BRA3.ChurchT80 using ( succEqO_to_anything )

------------------------------------------------------------------------
-- SECTION 1.  Joinability over transparent traces.

record SgT (B : Term -> Set) : Set where
  constructor mkSgT
  field
    car : Term
    prf : B car
open SgT public

data Conj (A B : Set) : Set where
  mkConj : A -> B -> Conj A B

prjL : {A B : Set} -> Conj A B -> A
prjL (mkConj a _) = a

prjR : {A B : Set} -> Conj A B -> B
prjR (mkConj _ b) = b

JoinChain : Term -> Term -> Set
JoinChain b c = SgT (\ w -> Conj (ChainM b w) (ChainM c w))

------------------------------------------------------------------------
-- SECTION 2.  The clash:  0  and  s X  have no common reduct.

-- ex falso: a join of  ze#  and  su# X  proves ANY object formula  Q
-- (so the trace theory containing such a join is object-inconsistent).
-- Conclusion kept OBJECT (Deriv Q) -- NO meta refuter (Deriv .. -> Empty).

joinClash : (X : Term) (Q : Formula) -> JoinChain ze# (su# X) -> Deriv Q
joinClash X Q jc =
  let hz : Deriv (eqF (hd (car jc)) tagZe)
      hz = chainHeadZe (prjL (prf jc)) hd_ze
      hs : Deriv (eqF (hd (car jc)) tagSu)
      hs = chainHeadSu (prjR (prf jc)) (hd_su X)
      clashSym : Deriv (eqF (ap1 s O) O)
      clashSym = ruleSym (ruleTrans (ruleSym hz) hs)
  in mp (succEqO_to_anything O Q) clashSym
