{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SizedTree -- a SIZE-PREFIXED coding of binary trees (Leaf / Branch) for
-- which course-of-values induction applies with a ONE-LINE, eta-free descent
-- (no surjective pairing, no nu-arithmetic).
--
-- The size is carried as the OUTERMOST field, so the induction MEASURE is a
-- free projection (sz = Fst), and the child-size < node-size descent is
-- immediate from leq_sigma + s-monotonicity (T78) -- exactly the HeightInd
-- technique, but on the carried size, so even `sz_node` is just `axFst`.
--
--   szLeaf a    = Pair (natCode 1) a                                   -- size 1
--   szNode l r  = Pair (s (sigma (sz l) (sz r))) (Pair (natCode 2) (Pair l r))
--   sz d        = Fst d                                                -- the size field
--
--   sz_node    : sz (szNode l r) = s (sigma (sz l) (sz r))            (= axFst)
--   descSzL    : leq (s (sz l)) (sz (szNode l r))                     (one line)
--   descSzR    : leq (s (sz r)) (sz (szNode l r))                     (one line)
--
-- And the MEASURE-INDEXED course-of-values eliminator:
--   covMeasure mu Q step n d (leq (mu d) (natCode n)) : Q d
-- (covFuel generalised to descend on an arbitrary measure mu; here mu = sz).
-- So for the size coding the descent feeding the strong IH to a child is
-- descSzL / descSzR -- keystone-free.
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.SizedTree where

open import T4.Base

open import T4.TreeCovInd using ( leq_s_s_cancel ; leq_s_O_absurd )
open import T4.LeqMono    using ( leq_trans ; leq_sigma_left ; leq_sigma_right )

open import BRA3.Church    using ( sigma ; sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )

------------------------------------------------------------------------
-- SECTION 1.  Measure-indexed course-of-values induction (covFuel with a
-- measure mu; the descent feeding the strong IH is on  mu , not the raw code).

covMeasure :
  (mu : Term -> Term) ->
  (Q : Term -> Formula) ->
  ( (d : Term) ->
    ( (e : Term) -> Deriv (leq (ap1 s (mu e)) (mu d)) -> Deriv (Q e) ) ->
    Deriv (Q d) ) ->
  (n : Nat) -> (d : Term) -> Deriv (leq (mu d) (natCode n)) -> Deriv (Q d)
covMeasure mu Q stp zero d bnd =
  stp d (\ e lsed ->
           leq_s_O_absurd (mu e) (Q e)
             (leq_trans (ap1 s (mu e)) (mu d) O lsed bnd))
covMeasure mu Q stp (suc n) d bnd =
  stp d (\ e lsed ->
           let lss : Deriv (leq (ap1 s (mu e)) (ap1 s (natCode n)))
               lss = leq_trans (ap1 s (mu e)) (mu d) (ap1 s (natCode n)) lsed bnd
               len : Deriv (leq (mu e) (natCode n))
               len = leq_s_s_cancel (mu e) (natCode n) lss
           in covMeasure mu Q stp n e len)

------------------------------------------------------------------------
-- SECTION 2.  The size-prefixed coding.

sz : Term -> Term
sz d = ap1 Fst d

szLeaf : Term -> Term
szLeaf a = ap2 Pair (natCode 1) a

szNode : Term -> Term -> Term
szNode l r =
  ap2 Pair (ap1 s (ap2 sigma (sz l) (sz r)))
           (ap2 Pair (natCode 2) (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 3.  Size equations (both via axFst -- the size IS the Fst field).

sz_leaf : (a : Term) -> Deriv (eqF (sz (szLeaf a)) (natCode 1))
sz_leaf a = axFst (natCode 1) a

sz_node : (l r : Term) ->
  Deriv (eqF (sz (szNode l r)) (ap1 s (ap2 sigma (sz l) (sz r))))
sz_node l r =
  axFst (ap1 s (ap2 sigma (sz l) (sz r)))
        (ap2 Pair (natCode 2) (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 4.  THE CHEAP, ETA-FREE DESCENT (one line each; no nu, no surjPair).
--   child-size <= sigma(sz l)(sz r) (leq_sigma) + s-mono (T78), rewritten
--   through sz_node (leq a b is definitionally eqF (sub a b) O).

descSzL : (l r : Term) -> Deriv (leq (ap1 s (sz l)) (sz (szNode l r)))
descSzL l r =
  let sumlr : Term
      sumlr = ap2 sigma (sz l) (sz r)
      leqS : Deriv (leq (ap1 s (sz l)) (ap1 s sumlr))
      leqS = mp (ruleInst2 0 (sz l) 1 sumlr refl T78) (leq_sigma_left (sz l) (sz r))
  in ruleTrans (congR sub (ap1 s (sz l)) (sz_node l r)) leqS

descSzR : (l r : Term) -> Deriv (leq (ap1 s (sz r)) (sz (szNode l r)))
descSzR l r =
  let sumlr : Term
      sumlr = ap2 sigma (sz l) (sz r)
      leqS : Deriv (leq (ap1 s (sz r)) (ap1 s sumlr))
      leqS = mp (ruleInst2 0 (sz r) 1 sumlr refl T78) (leq_sigma_right (sz l) (sz r))
  in ruleTrans (congR sub (ap1 s (sz r)) (sz_node l r)) leqS
