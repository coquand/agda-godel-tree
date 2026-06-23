{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CodeDescent -- the VALIDITY-FREE strict code-descent bounds that feed the
-- INTERNAL course-of-values eliminator T4.TreeCovInd.covFuel (whose measure is
-- the code value itself, leq (s child) d -- NOT dsize).  A child code is a
-- Cantor sub-projection of the parent, hence <= predecessor d, hence < d:
--
--   pArg d <= predecessor d            (T4.WfRedExtract.argValueBound)
--   pL   d <= predecessor d            (pLValueBound)        => s child <= d
--   pR   d <= predecessor d            (pRValueBound)
--   pArg (pL d) <= pL d <= pred d      (grandchild, no-grandchild Ad/Su case)
--
-- The +1 / predecessor step is  T78 + succForm (s (pred d) = d).  NO validity
-- hypothesis is used (only d != O), so the covFuel descent is free.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CodeDescent where

open import T4.Base

open import T4.DerCodeS using ( pArg ; pL ; pR )
open import T4.WfRedExtract using ( argValueBound ; pLValueBound ; pRValueBound )
open import T4.SndDescent using ( sndLe )
open import T4.SizedPres using ( succForm )

open import BRA3.Church    using ( sub ; predecessor )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import T4.LeqMono     using ( leq_trans )

------------------------------------------------------------------------
-- s c <= d  from  c <= predecessor d  (d != O).

private
  bumpToSelf : (c d : Term) -> Deriv (neg (eqF d O)) ->
    Deriv (leq c (ap1 predecessor d)) -> Deriv (leq (ap1 s c) d)
  bumpToSelf c d ne cle =
    let ss : Deriv (leq (ap1 s c) (ap1 s (ap1 predecessor d)))
        ss = mp (ruleInst2 0 c 1 (ap1 predecessor d) refl T78) cle
    in ruleTrans (congR sub (ap1 s c) (ruleSym (succForm d ne))) ss

------------------------------------------------------------------------
-- the descent bounds.

descCodeArg : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (leq (ap1 s (pArg d)) d)
descCodeArg d ne = bumpToSelf (pArg d) d ne (argValueBound d ne)

descCodeL : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (leq (ap1 s (pL d)) d)
descCodeL d ne = bumpToSelf (pL d) d ne (pLValueBound d ne)

descCodeR : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (leq (ap1 s (pR d)) d)
descCodeR d ne = bumpToSelf (pR d) d ne (pRValueBound d ne)

-- pArg z <= z, free (a child is below its parent code).
pArgLeSelf : (z : Term) -> Deriv (leq (pArg z) z)
pArgLeSelf z =
  leq_trans (pArg z) (ap1 Snd z) z (sndLe (ap1 Snd z)) (sndLe z)

-- grandchild  pArg (pL d) < d  (for the Ad/Su critical pair).
descCodeArgL : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (leq (ap1 s (pArg (pL d))) d)
descCodeArgL d ne =
  bumpToSelf (pArg (pL d)) d ne
    (leq_trans (pArg (pL d)) (pL d) (ap1 predecessor d)
       (pArgLeSelf (pL d)) (pLValueBound d ne))
