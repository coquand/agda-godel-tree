{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SizedDescentOp -- the "descent UNDER THE VERIFIED BRANCH" lemmas: the
-- bridge that lets SizedTree.covMeasure (mu = pSize) descend on an OPAQUE
-- proof code, given only the size-consistency equation that  checkPar  has
-- verified at that node.
--
-- For a BUILT node  pcAd l r  the descent is  T4.SizedProof.descP_cAdL/R .
-- For an OPAQUE  p  the verifier  checkPar p = 0  establishes the SIZE-
-- CONSISTENCY equation
--
--     pSize p = s (sigma (pSize (pL p)) (pSize (pR p)))      (binary)
--     pSize p = s (pSize (pArg p))                           (unary)
--
-- and from THAT hypothesis the strict child-descent follows by exactly the
-- same  leq_sigma + T78  (binary) / sub_self (unary) argument -- NO surjective
-- pairing, no value-descent on Cantor Fst.  This is precisely "size(child) <
-- size(node), PR-provable only under the verified-constructor branch".
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.SizedDescentOp where

open import T4.Base

open import T4.SizedProof    using ( pSize )
open import T4.SizedProofDec using ( pArg ; pL ; pR )

open import T4.LeqMono using ( leq_sigma_left ; leq_sigma_right )

open import BRA3.Church    using ( sigma ; sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )

------------------------------------------------------------------------
-- BINARY descent under the verified size-consistency hypothesis.

descOpaqueL : (p : Term) ->
  Deriv (eqF (pSize p) (ap1 s (ap2 sigma (pSize (pL p)) (pSize (pR p))))) ->
  Deriv (leq (ap1 s (pSize (pL p))) (pSize p))
descOpaqueL p hyp =
  let l' : Term
      l' = pSize (pL p)
      r' : Term
      r' = pSize (pR p)
      leqS : Deriv (leq (ap1 s l') (ap1 s (ap2 sigma l' r')))
      leqS = mp (ruleInst2 0 l' 1 (ap2 sigma l' r') refl T78)
                (leq_sigma_left l' r')
  in ruleTrans (congR sub (ap1 s l') hyp) leqS

descOpaqueR : (p : Term) ->
  Deriv (eqF (pSize p) (ap1 s (ap2 sigma (pSize (pL p)) (pSize (pR p))))) ->
  Deriv (leq (ap1 s (pSize (pR p))) (pSize p))
descOpaqueR p hyp =
  let l' : Term
      l' = pSize (pL p)
      r' : Term
      r' = pSize (pR p)
      leqS : Deriv (leq (ap1 s r') (ap1 s (ap2 sigma l' r')))
      leqS = mp (ruleInst2 0 r' 1 (ap2 sigma l' r') refl T78)
                (leq_sigma_right l' r')
  in ruleTrans (congR sub (ap1 s r') hyp) leqS

------------------------------------------------------------------------
-- UNARY descent under the verified size-consistency hypothesis.

descOpaqueU : (p : Term) ->
  Deriv (eqF (pSize p) (ap1 s (pSize (pArg p)))) ->
  Deriv (leq (ap1 s (pSize (pArg p))) (pSize p))
descOpaqueU p hyp =
  ruleTrans (congR sub (ap1 s (pSize (pArg p))) hyp)
            (sub_self (ap1 s (pSize (pArg p))))
