{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SizedProof -- SIZE-PREFIXED coding of the 5-constructor parallel-reduction
-- PROOF trees, the foundation of the FUEL / MEASURE diamond (the redesign that
-- removes the depth-2 sub-code descent blocker).
--
-- THE PROBLEM IT FIXES.  Recursing on an opaque Cantor proof code by  Snd
-- projections needs  Snd d < d  (descSnd, ok) but the BINARY constructors'
-- FIRST child is  Fst (Snd d) , and Cantor  Fst  is NOT a strict (nor even a
-- non-strict) decrease -- so the nested-redex (cAd) case has no value-descent
-- without surjective pairing.  THE FIX (size-prefixed coding, a la
-- T4.SizedTree): carry the size as the OUTERMOST field so the induction MEASURE
-- is a free projection  pSize = Fst , and the size is ADDITIVE, so BOTH
-- children of a node strictly decrease -- one line each, no nu, no surjPair.
-- The diamond then recurses on the external measure via  SizedTree.covMeasure ;
-- "size(child) < size(node)" is  descP*  below.
--
-- Coding (size prefix; inner = Pair ctorTag payload; payload = child / Pair l r):
--   pcZe        = Pair (natCode 1) (Pair (natCode 0) O)                 -- size 1
--   pcSu c      = Pair (s (pSize c))                  (Pair (natCode 1) c)
--   pcAd l r    = Pair (s (sigma (pSize l) (pSize r)))(Pair (natCode 2) (Pair l r))
--   pcRO c      = Pair (s (pSize c))                  (Pair (natCode 3) c)
--   pcRS l r    = Pair (s (sigma (pSize l) (pSize r)))(Pair (natCode 4) (Pair l r))
--   pSize d     = Fst d
--
-- This file delivers the coding + the size equations + the STRICT child-descent
-- lemmas (the keystone that kills the depth-2 problem).  Decoder projectors and
-- the diamond interpreter are the next bricks.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.SizedProof where

open import T4.Base

open import T4.LeqMono using ( leq_sigma_left ; leq_sigma_right )

open import BRA3.Church    using ( sigma ; sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )

------------------------------------------------------------------------
-- SECTION 1.  The measure and the size-prefixed constructors.

pSize : Term -> Term
pSize d = ap1 Fst d

pcZe : Term
pcZe = ap2 Pair (natCode 1) (ap2 Pair (natCode 0) O)

pcSu : Term -> Term
pcSu c = ap2 Pair (ap1 s (pSize c)) (ap2 Pair (natCode 1) c)

pcAd : Term -> Term -> Term
pcAd l r =
  ap2 Pair (ap1 s (ap2 sigma (pSize l) (pSize r)))
           (ap2 Pair (natCode 2) (ap2 Pair l r))

pcRO : Term -> Term
pcRO c = ap2 Pair (ap1 s (pSize c)) (ap2 Pair (natCode 3) c)

pcRS : Term -> Term -> Term
pcRS l r =
  ap2 Pair (ap1 s (ap2 sigma (pSize l) (pSize r)))
           (ap2 Pair (natCode 4) (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 2.  Size equations (each is the outer  axFst ).

pSize_cZe : Deriv (eqF (pSize pcZe) (natCode 1))
pSize_cZe = axFst (natCode 1) (ap2 Pair (natCode 0) O)

pSize_cSu : (c : Term) -> Deriv (eqF (pSize (pcSu c)) (ap1 s (pSize c)))
pSize_cSu c = axFst (ap1 s (pSize c)) (ap2 Pair (natCode 1) c)

pSize_cAd : (l r : Term) ->
  Deriv (eqF (pSize (pcAd l r)) (ap1 s (ap2 sigma (pSize l) (pSize r))))
pSize_cAd l r =
  axFst (ap1 s (ap2 sigma (pSize l) (pSize r)))
        (ap2 Pair (natCode 2) (ap2 Pair l r))

pSize_cRO : (c : Term) -> Deriv (eqF (pSize (pcRO c)) (ap1 s (pSize c)))
pSize_cRO c = axFst (ap1 s (pSize c)) (ap2 Pair (natCode 3) c)

pSize_cRS : (l r : Term) ->
  Deriv (eqF (pSize (pcRS l r)) (ap1 s (ap2 sigma (pSize l) (pSize r))))
pSize_cRS l r =
  axFst (ap1 s (ap2 sigma (pSize l) (pSize r)))
        (ap2 Pair (natCode 4) (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 3.  STRICT child-descent (the keystone; matches covMeasure's
-- IH precondition  leq (s (mu e)) (mu d)  with  mu = pSize ).
--
--   UNARY  (cSu / cRO): node size = s (pSize c), so  leq (s (pSize c)) node
--   is  leq X X  = sub_self  (after rewriting node via the size eq).
--   BINARY (cAd / cRS): exactly descSzL / descSzR -- child <= sigma (leq_sigma)
--   + s-monotonicity (T78), rewritten through the size eq.  BOTH children
--   strictly decrease -- this is what the Cantor-Fst route could not give.

descP_cSu : (c : Term) -> Deriv (leq (ap1 s (pSize c)) (pSize (pcSu c)))
descP_cSu c =
  ruleTrans (congR sub (ap1 s (pSize c)) (pSize_cSu c)) (sub_self (ap1 s (pSize c)))

descP_cRO : (c : Term) -> Deriv (leq (ap1 s (pSize c)) (pSize (pcRO c)))
descP_cRO c =
  ruleTrans (congR sub (ap1 s (pSize c)) (pSize_cRO c)) (sub_self (ap1 s (pSize c)))

descP_cAdL : (l r : Term) -> Deriv (leq (ap1 s (pSize l)) (pSize (pcAd l r)))
descP_cAdL l r =
  let sumlr : Term
      sumlr = ap2 sigma (pSize l) (pSize r)
      leqS : Deriv (leq (ap1 s (pSize l)) (ap1 s sumlr))
      leqS = mp (ruleInst2 0 (pSize l) 1 sumlr refl T78)
                (leq_sigma_left (pSize l) (pSize r))
  in ruleTrans (congR sub (ap1 s (pSize l)) (pSize_cAd l r)) leqS

descP_cAdR : (l r : Term) -> Deriv (leq (ap1 s (pSize r)) (pSize (pcAd l r)))
descP_cAdR l r =
  let sumlr : Term
      sumlr = ap2 sigma (pSize l) (pSize r)
      leqS : Deriv (leq (ap1 s (pSize r)) (ap1 s sumlr))
      leqS = mp (ruleInst2 0 (pSize r) 1 sumlr refl T78)
                (leq_sigma_right (pSize l) (pSize r))
  in ruleTrans (congR sub (ap1 s (pSize r)) (pSize_cAd l r)) leqS

descP_cRSL : (l r : Term) -> Deriv (leq (ap1 s (pSize l)) (pSize (pcRS l r)))
descP_cRSL l r =
  let sumlr : Term
      sumlr = ap2 sigma (pSize l) (pSize r)
      leqS : Deriv (leq (ap1 s (pSize l)) (ap1 s sumlr))
      leqS = mp (ruleInst2 0 (pSize l) 1 sumlr refl T78)
                (leq_sigma_left (pSize l) (pSize r))
  in ruleTrans (congR sub (ap1 s (pSize l)) (pSize_cRS l r)) leqS

descP_cRSR : (l r : Term) -> Deriv (leq (ap1 s (pSize r)) (pSize (pcRS l r)))
descP_cRSR l r =
  let sumlr : Term
      sumlr = ap2 sigma (pSize l) (pSize r)
      leqS : Deriv (leq (ap1 s (pSize r)) (ap1 s sumlr))
      leqS = mp (ruleInst2 0 (pSize r) 1 sumlr refl T78)
                (leq_sigma_right (pSize l) (pSize r))
  in ruleTrans (congR sub (ap1 s (pSize r)) (pSize_cRS l r)) leqS
