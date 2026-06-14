{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EqSound -- the EQUATIONAL SOUNDNESS layer of attempt3 §9 and the toy
-- Con(T0): for the orthogonal recursor TRS (ze/su/ad), the equational theory
-- T0 (the rewrite rules as equations + reflexivity/symmetry/transitivity +
-- congruence) is SOUND for convertibility, hence CONSISTENT.
--
--     (EqSound)  EqProv t u  ->  Join t u           (eqSound)
--     Con(T0)    Not (EqProv ze (su ze))            (conT0)   = 0 != s0
--
-- This is the meta object analog of attempt3's
--     (EqSound)  EqProv_{T0}(t=u)  =>  t = u  (convertible)
-- composed with the Church-Rosser headline  ¬(0 = s0)  (T4.ParHeadline).
-- Every equational generator embeds into convertibility (eqProvConv), and
-- convertible terms are joinable (T4.ParHeadline.convJoin, via confluence);
-- ze and su ze are not joinable, so they are not equal in T0.
--
-- STILL AHEAD (the logical half, attempt3 §9 obligation (Cons)): for the FULL
-- T0 with propositional structure (implicational axioms + MP), reducing an
-- atomic theorem  T0 |- (0 = s0)  to an EQUATIONAL derivation  EqProv (0 = s0)
-- = free-cut elimination + subformula property.  Here T0 IS the equational
-- theory, so (Cons) is identity; the propositional reduction is the remaining
-- engineering.

module T4.EqSound where

open import T4.ParReflPres using ( Tm ; ze ; su ; ad )
open import T4.ParStep     using ( StepM ; stO ; stS ; stSu ; stA1 ; stA2 )
open import T4.ParHeadline using
  ( Empty ; Not ; Join
  ; Conv ; cstep ; crefl ; csym ; ctrans
  ; convJoin ; zeNotConvSuZe )

------------------------------------------------------------------------
-- Congruence for convertibility (Conv has only single-step + the
-- equivalence closure; congruence is derived through the Step congruences).

convSu : {t t' : Tm} -> Conv t t' -> Conv (su t) (su t')
convSu (cstep st)    = cstep (stSu st)
convSu crefl         = crefl
convSu (csym c)      = csym (convSu c)
convSu (ctrans c1 c2) = ctrans (convSu c1) (convSu c2)

convAd1 : {a a' b : Tm} -> Conv a a' -> Conv (ad a b) (ad a' b)
convAd1 (cstep st)    = cstep (stA1 st)
convAd1 crefl         = crefl
convAd1 (csym c)      = csym (convAd1 c)
convAd1 (ctrans c1 c2) = ctrans (convAd1 c1) (convAd1 c2)

convAd2 : {a b b' : Tm} -> Conv b b' -> Conv (ad a b) (ad a b')
convAd2 (cstep st)    = cstep (stA2 st)
convAd2 crefl         = crefl
convAd2 (csym c)      = csym (convAd2 c)
convAd2 (ctrans c1 c2) = ctrans (convAd2 c1) (convAd2 c2)

convAd : {a a' b b' : Tm} -> Conv a a' -> Conv b b' -> Conv (ad a b) (ad a' b')
convAd ca cb = ctrans (convAd1 ca) (convAd2 cb)

------------------------------------------------------------------------
-- The toy equational theory T0 (the INDUCTION-FREE equational fragment):
-- the recursor rules as equations + reflexivity / symmetry / transitivity
-- + congruence under the constructors.

data EqProv : Tm -> Tm -> Set where
  eRO    : (y : Tm)                            -> EqProv (ad ze y) y
  eRS    : (x y : Tm)                          -> EqProv (ad (su x) y) (su (ad x y))
  eRefl  : (t : Tm)                            -> EqProv t t
  eSym   : {t u : Tm}      -> EqProv t u       -> EqProv u t
  eTrans : {t u v : Tm}    -> EqProv t u -> EqProv u v -> EqProv t v
  eSu    : {t t' : Tm}     -> EqProv t t'      -> EqProv (su t) (su t')
  eAd    : {a a' b b' : Tm} -> EqProv a a' -> EqProv b b' ->
                              EqProv (ad a b) (ad a' b')

------------------------------------------------------------------------
-- Embedding T0 into convertibility:  every equational generator is a
-- convertibility step / closure operation.

eqProvConv : {t u : Tm} -> EqProv t u -> Conv t u
eqProvConv (eRO y)       = cstep (stO y)
eqProvConv (eRS x y)     = cstep (stS x y)
eqProvConv (eRefl t)     = crefl
eqProvConv (eSym p)      = csym (eqProvConv p)
eqProvConv (eTrans p q)  = ctrans (eqProvConv p) (eqProvConv q)
eqProvConv (eSu p)       = convSu (eqProvConv p)
eqProvConv (eAd pa pb)   = convAd (eqProvConv pa) (eqProvConv pb)

------------------------------------------------------------------------
-- (EqSound) and the headline  Con(T0)  for the toy theory.

eqSound : {t u : Tm} -> EqProv t u -> Join t u
eqSound p = convJoin (eqProvConv p)

-- Con(T0):  T0 does NOT equationally derive  0 = s0 .

conT0 : Not (EqProv ze (su ze))
conT0 p = zeNotConvSuZe (eqProvConv p)
