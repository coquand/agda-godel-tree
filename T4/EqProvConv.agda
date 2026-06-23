{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EqProvConv -- STEP 2 (meta level): compile an equational derivation of the
-- toy theory T0 into a conversion, then compose with the finished consistency
-- core (T4.ConvClash) to get the head-clash.
--
--   EqProv t u   -- the equational theory of the ze/su/ad recursor TRS:
--                   rewrite-rules-as-equations (eRO/eRS) + eRefl/eSym/eTrans
--                   + congruences (eSu/eAd1/eAd2).  T0 has NO induction rule,
--                   so this is a finite, local, syntax-directed proof system.
--   eqProvConv : EqProv t u -> Conv t u          -- proof translation (step 2)
--   eqProvClash : EqProv ze (su ze) -> (Q:Formula) -> Deriv Q
--                                                -- = convClash . eqProvConv
--
-- Hence  EqProv ze (su ze)  (a T0-equational proof of 0 = s0) makes the OBJECT
-- theory prove anything -- the consistency of the (meta) equational T0, with an
-- OBJECT-Deriv conclusion.  The translation is structural recursion on the
-- equational derivation (each rule case finite/local), NOT reflection.
--
-- (This is meta-input -- the equational proof is the meta inductive EqProv; the
-- OBJECT-input BRA |- Con(T0) replaces EqProv by an object proof code + the
-- object compileFuel, reusing eqProvConv's clause structure.)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.EqProvConv where

open import T4.Base

open import T4.ParReflPres using ( Tm ; ze ; su ; ad )
open import T4.ParStep     using ( stO ; stS ; stSu ; stA1 ; stA2 )
open import T4.ParHeadline using ( Conv ; cstep ; crefl ; csym ; ctrans )
open import T4.ConvClash   using ( convClash )

------------------------------------------------------------------------
-- SECTION 1.  The equational theory T0 (rewrite rules as equations).

data EqProv : Tm -> Tm -> Set where
  eRO    : {y : Tm}     -> EqProv (ad ze y) y
  eRS    : {x y : Tm}   -> EqProv (ad (su x) y) (su (ad x y))
  eRefl  : {t : Tm}     -> EqProv t t
  eSym   : {t u : Tm}   -> EqProv t u -> EqProv u t
  eTrans : {t u v : Tm} -> EqProv t u -> EqProv u v -> EqProv t v
  eSu    : {t u : Tm}   -> EqProv t u -> EqProv (su t) (su u)
  eAd1   : {a a' b : Tm} -> EqProv a a' -> EqProv (ad a b) (ad a' b)
  eAd2   : {a b b' : Tm} -> EqProv b b' -> EqProv (ad a b) (ad a b')

------------------------------------------------------------------------
-- SECTION 2.  Conversion congruences (by induction on Conv, via StepM congs).

convSu : {t u : Tm} -> Conv t u -> Conv (su t) (su u)
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

------------------------------------------------------------------------
-- SECTION 3.  The proof translation  EqProv -> Conv  (step 2).

eqProvConv : {t u : Tm} -> EqProv t u -> Conv t u
eqProvConv (eRO {y})     = cstep (stO y)
eqProvConv (eRS {x} {y}) = cstep (stS x y)
eqProvConv eRefl         = crefl
eqProvConv (eSym e)      = csym (eqProvConv e)
eqProvConv (eTrans e1 e2) = ctrans (eqProvConv e1) (eqProvConv e2)
eqProvConv (eSu e)       = convSu (eqProvConv e)
eqProvConv (eAd1 e)      = convAd1 (eqProvConv e)
eqProvConv (eAd2 e)      = convAd2 (eqProvConv e)

------------------------------------------------------------------------
-- SECTION 4.  The head-clash for the equational theory (meta Con(T0) core).

eqProvClash : EqProv ze (su ze) -> (Q : Formula) -> Deriv Q
eqProvClash e Q = convClash (eqProvConv e) Q
