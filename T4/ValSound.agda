{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ValSound -- SOUNDNESS of the equational theory Eq for the denotational
-- value model  valF , and the resulting (schematic) Con(Eq).
--
-- PfM t u : the object-term analogue of T4.EqProvConv.EqProv -- a proof tree of
-- the equation  t = u  in the addition-TRS equational theory, indexed by its two
-- endpoints (object coded terms ze# / su# / ad#).  The model soundness is then a
-- ONE-LINE structural recursion: every rule is discharged by the matching
-- T4.ValModel building block, and  eTrans  is literally  ruleTrans  (the middle
-- term matches by the index).
--
--   soundM : PfM t u -> Deriv (valF t = valF u)
--
-- Hence  PfM ze# (su# ze#)  is impossible-with-a-true-model:  it forces BRA to
-- prove the false atom  s O = O  (refuted by ax_succ_nonzero).  This is Con(Eq)
-- in the same SCHEMATIC sense as T4.DerClash.convClashU -- an inconsistency
-- transfer -- but obtained from a genuine MODEL covering ALL eight Eq rules, with
-- NO confluence / head-stability / reduction machinery.
--
-- (The fully-internal Pi-0-1 form  forall y. thEq0(y) /= code(0=s0)  needs the
-- cov-recursive proof verifier; see HANDOFF-CONEQ-VALMODEL.md.  The MODEL core
-- it consumes is exactly  T4.ValModel  +  soundM  here.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ValSound where

open import T4.Base

open import T4.ValF using ( valF )
open import T4.ValModel
  using ( vRO ; vRS ; vSu ; vAd1 ; vAd2 ; vZe ; vSuZe )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )

------------------------------------------------------------------------
-- SECTION 1.  Object-term equational proof trees (= EqProv over coded terms).

data PfM : Term -> Term -> Set where
  pRO    : (y : Term) -> PfM (ad# ze# y) y
  pRS    : (x y : Term) -> PfM (ad# (su# x) y) (su# (ad# x y))
  pRefl  : (t : Term) -> PfM t t
  pSym   : {t u : Term} -> PfM t u -> PfM u t
  pTrans : {t u v : Term} -> PfM t u -> PfM u v -> PfM t v
  pSu    : {t u : Term} -> PfM t u -> PfM (su# t) (su# u)
  pAd1   : {a a' : Term} (b : Term) -> PfM a a' -> PfM (ad# a b) (ad# a' b)
  pAd2   : (a : Term) {b b' : Term} -> PfM b b' -> PfM (ad# a b) (ad# a b')

------------------------------------------------------------------------
-- SECTION 2.  Model soundness:  PfM t u  =>  valF t = valF u .

soundM : {t u : Term} -> PfM t u -> Deriv (eqF (ap1 valF t) (ap1 valF u))
soundM (pRO y)        = vRO y
soundM (pRS x y)      = vRS x y
soundM (pRefl t)      = axRefl (ap1 valF t)
soundM (pSym pf)      = ruleSym (soundM pf)
soundM (pTrans p1 p2) = ruleTrans (soundM p1) (soundM p2)
soundM (pSu pf)       = vSu _ _ (soundM pf)
soundM (pAd1 b pf)    = vAd1 _ _ b (soundM pf)
soundM (pAd2 a pf)    = vAd2 a _ _ (soundM pf)

------------------------------------------------------------------------
-- SECTION 3.  Con(Eq), schematic:  no Eq-proof concludes  0 = s0 .

-- A proof of  ze# = su# ze#  forces the false atom  s O = O :
--   valF ze# = O ,  valF (su# ze#) = s O ,  and  valF ze# = valF (su# ze#) .
conEqM : PfM ze# (su# ze#) -> Deriv (eqF (ap1 s O) O)
conEqM pf =
  let e : Deriv (eqF (ap1 valF ze#) (ap1 valF (su# ze#)))
      e = soundM pf
  in ruleTrans (ruleSym vSuZe) (ruleTrans (ruleSym e) vZe)
