{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DiamondTrace -- DELIVERABLE 1 (the mathematical CR core), FINISHED for the
-- single parallel step: the diamond as an object map producing genuine object
-- JOINABILITY, with every object in ONE trace coding (the cert coding
-- CertM/codeC + T4.DiamondF), NO opaque verifier, NO coding bridge.
--
--   diamondTrace : (two parallel-step traces with a common source)
--                  -> Join (their targets)
--
-- where  Join b c  is OBJECT joinability: an apex  w  and two VALID traces
-- (cert codes  d  with  isCert d = O ,  src d = . ,  tgt d = w ) from  b  and
-- from  c  to  w .  This is exactly the LLM's deliverable 1 shape
--   diamondTrace : p:a=>b -> q:a=>c -> Join b c
-- with all objects in the same coding -- proved DIRECTLY from
-- T4.DiamondF.localDiamond (apex = devF(src), legs = triF p / triF q), no
-- CertM/pc* mismatch, no opaque-proof decoding.
--
-- (Multi-step confluence = iterate this via strip/confl over a list of steps;
-- compiling a T0 equational proof into such traces is deliverable 2; both
-- build ON this finished core.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DiamondTrace where

open import T4.Base

open import T4.CertTree using ( CertM ; codeC )
open import T4.ParEnds  using ( src ; tgt ; isCert )
open import T4.DiamondF using
  ( diamondF ; diaW ; diaL ; diaR
  ; LocalDiamond ; localDiamond
  ; okL_cert ; okL_src ; okL_tgt ; okR_cert ; okR_src ; okR_tgt )

------------------------------------------------------------------------
-- SECTION 1.  Object joinability in the cert trace coding.

record SgT (B : Term -> Set) : Set where
  constructor mkSgT
  field
    car : Term
    prf : B car
open SgT public

data Conj (A B : Set) : Set where
  mkConj : A -> B -> Conj A B

-- TraceTo b w : there is a VALID cert trace  d  with  src d = b ,  tgt d = w .
TraceTo : Term -> Term -> Set
TraceTo b w =
  SgT (\ d -> Conj (Conj (Deriv (eqF (ap1 isCert d) O))
                         (Deriv (eqF (ap1 src d) b)))
                   (Deriv (eqF (ap1 tgt d) w)))

-- Join b c : a common reduct  w  with valid traces from  b  and  c  to  w .
Join : Term -> Term -> Set
Join b c = SgT (\ w -> Conj (TraceTo b w) (TraceTo c w))

------------------------------------------------------------------------
-- SECTION 2.  The single-step diamond produces joinability (finished).

diamondTrace :
  (c1 c2 : CertM) ->
  Deriv (eqF (ap1 src (codeC c1)) (ap1 src (codeC c2))) ->
  Join (ap1 tgt (codeC c1)) (ap1 tgt (codeC c2))
diamondTrace c1 c2 srcEq =
  let dgm : Term
      dgm = diamondF (codeC c1) (codeC c2)
      ld : LocalDiamond (ap1 tgt (codeC c1)) (ap1 tgt (codeC c2))
                        (diaW dgm) (diaL dgm) (diaR dgm)
      ld = localDiamond c1 c2 srcEq
      legL : TraceTo (ap1 tgt (codeC c1)) (diaW dgm)
      legL = mkSgT (diaL dgm)
               (mkConj (mkConj (okL_cert ld) (okL_src ld)) (okL_tgt ld))
      legR : TraceTo (ap1 tgt (codeC c2)) (diaW dgm)
      legR = mkSgT (diaR dgm)
               (mkConj (mkConj (okR_cert ld) (okR_src ld)) (okR_tgt ld))
  in mkSgT (diaW dgm) (mkConj legL legR)
