{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ConjCodeExp -- the code-skeleton layer for the shared object
-- Fun2 K-functor of surprise-GII.
--
-- Exp2 smart constructors (T4.AbsFun2) mirroring the meta code-builders
-- ( cNeg / cImp / cEqTm / cAp1f / cAp2f / cAnd ), plus the big-conjunction
-- fold  econjUpTo  for  K(x0,...) = /\_{j} ¬ define_{p_j}(x0, j) .
--
-- Each smart constructor satisfies  denote2 (e... a b) x r = c... (denote2 a x r) ...
-- DEFINITIONALLY (the meta builders are pure  ap2 Pair / natCode  skeletons),
-- so once an  Exp2  for  code K  is assembled,  compile2  (T4.AbsFun2) turns
-- it into the genuine  Fun2 Kfunctor  with  ap2 Kfunctor x0 r = code K(num x0, ...)
-- as a PROVED Deriv -- the term that must appear identically in surprise-GII
-- Steps 2 (W's recognition), 4 (Chaitin's antecedent), and 6 (thm12's output).
--
-- The  _pin  lemmas lock the denotation contract by  refl .

module T4.ConjCodeExp where

open import T4.Base
open import T4.AbsFun2
  using ( Exp2 ; econst ; eap1 ; eap2 ; denote2 )
open import T4.Thm12.ConstTermFun1 using ( NoVar_natCode )
open import T4.DoubleCodeNum using ( NoVar_codeFun1L ; NoVar_codeFun2L )
open import T4.Code using ( codeFun1 ; codeFun2 )
open import T4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 )
open import T4.DefWit using ( cNeg ; cImp ; cEqTm ; cAnd )
open import T4.CgiClash using ( cAp1f ; cAp2f )

------------------------------------------------------------------------
-- Basic Exp2 leaves / nodes.

enat2 : Nat -> Exp2
enat2 n = econst (natCode n) (NoVar_natCode n)

epair2 : Exp2 -> Exp2 -> Exp2
epair2 a b = eap2 Pair a b

------------------------------------------------------------------------
-- Code-builder smart constructors (mirror T4.DefWit / T4.CgiClash).

ecNeg2 : Exp2 -> Exp2
ecNeg2 c = epair2 (enat2 tag_neg) c

ecImp2 : Exp2 -> Exp2 -> Exp2
ecImp2 a b = epair2 (enat2 tag_imp) (epair2 a b)

ecEqTm2 : Exp2 -> Exp2 -> Exp2
ecEqTm2 a b = epair2 (enat2 tag_eq) (epair2 a b)

ecAp1f2 : Fun1 -> Exp2 -> Exp2
ecAp1f2 f t =
  epair2 (enat2 tag_ap1) (epair2 (econst (codeFun1 f) (NoVar_codeFun1L f)) t)

ecAp2f2 : Fun2 -> Exp2 -> Exp2 -> Exp2
ecAp2f2 g a b =
  epair2 (enat2 tag_ap2)
         (epair2 (econst (codeFun2 g) (NoVar_codeFun2L g)) (epair2 a b))

ecAnd2 : Exp2 -> Exp2 -> Exp2
ecAnd2 a b = ecNeg2 (ecImp2 a (ecNeg2 b))

------------------------------------------------------------------------
-- The big conjunction  f 0 /\ f 1 /\ ... /\ f n  (right-nested via cAnd),
-- the K-formula shape  /\_{j} (atom j) .

econjUpTo : (Nat -> Exp2) -> Nat -> Exp2
econjUpTo f zero    = f zero
econjUpTo f (suc n) = ecAnd2 (f (suc n)) (econjUpTo f n)

------------------------------------------------------------------------
-- Denotation contract (all by refl) -- the Exp2 builders ARE the meta
-- code-builders under  denote2 .

cNeg_pin :
  (c : Exp2) (a b : Term) ->
  Eq (denote2 (ecNeg2 c) a b) (cNeg (denote2 c a b))
cNeg_pin c a b = refl

cImp_pin :
  (x y : Exp2) (a b : Term) ->
  Eq (denote2 (ecImp2 x y) a b) (cImp (denote2 x a b) (denote2 y a b))
cImp_pin x y a b = refl

cEqTm_pin :
  (x y : Exp2) (a b : Term) ->
  Eq (denote2 (ecEqTm2 x y) a b) (cEqTm (denote2 x a b) (denote2 y a b))
cEqTm_pin x y a b = refl

cAp1f_pin :
  (f : Fun1) (t : Exp2) (a b : Term) ->
  Eq (denote2 (ecAp1f2 f t) a b) (cAp1f f (denote2 t a b))
cAp1f_pin f t a b = refl

cAp2f_pin :
  (g : Fun2) (x y : Exp2) (a b : Term) ->
  Eq (denote2 (ecAp2f2 g x y) a b) (cAp2f g (denote2 x a b) (denote2 y a b))
cAp2f_pin g x y a b = refl

cAnd_pin :
  (x y : Exp2) (a b : Term) ->
  Eq (denote2 (ecAnd2 x y) a b) (cAnd (denote2 x a b) (denote2 y a b))
cAnd_pin x y a b = refl
