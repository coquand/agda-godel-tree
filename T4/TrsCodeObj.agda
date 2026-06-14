{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TrsCodeObj -- STAGE I1 of attempt3 §11 (internalising CR in BRA).
--
-- Object-level Gödel coding of the toy TRS terms (ze / su / ad) as BRA
-- numerals-and-pairs, with the structural projectors and their DERIV
-- (object-derivable) equations.  This is the encoding layer on which the
-- internal reduction relation (I2), dev (I3) and the triangle (I4) will rest.
--
-- Coding (UNIFORMLY tagged pairs, all object Terms; subterm slots are
-- arbitrary object Terms so every statement is SCHEMATIC = universal):
--     ze#        = Pair O           O          (tag 0)
--     su# t      = Pair (s O)       t          (tag 1)
--     ad# a b    = Pair (s (s O))   (Pair a b)  (tag 2)
-- Projectors:  hd = Fst (head tag),  ar = Snd (argument bundle).
--
-- NB.  ze# is a TAGGED pair (head tag  O = natCode 0 ), not the bare  O .
-- Uniform tagging is what lets the internal reduction relation (I2)
-- dispatch on the head tag of EVERY constructor (incl. ze) via  eqAtT ;
-- the bare-O coding made ze#'s "tag"  Fst O  junk and broke dispatch.
--
-- Everything here is proved from  axFst / axSnd  (Pair algebra) — no
-- induction yet; this is the constructor/decoder interface.

module T4.TrsCodeObj where

open import T4.Base

------------------------------------------------------------------------
-- Tags and constructors (object Terms)

tagZe : Term
tagZe = O

tagSu : Term
tagSu = ap1 s O

tagAd : Term
tagAd = ap1 s (ap1 s O)

ze# : Term
ze# = ap2 Pair tagZe O

su# : Term -> Term
su# t = ap2 Pair tagSu t

ad# : Term -> Term -> Term
ad# a b = ap2 Pair tagAd (ap2 Pair a b)

------------------------------------------------------------------------
-- Projectors

hd : Term -> Term
hd t = ap1 Fst t

ar : Term -> Term
ar t = ap1 Snd t

------------------------------------------------------------------------
-- Object-derivable projection equations (universal in the subterm codes)

hd_ze : Deriv (eqF (hd ze#) tagZe)
hd_ze = axFst tagZe O

ar_ze : Deriv (eqF (ar ze#) O)
ar_ze = axSnd tagZe O

hd_su : (t : Term) -> Deriv (eqF (hd (su# t)) tagSu)
hd_su t = axFst tagSu t

ar_su : (t : Term) -> Deriv (eqF (ar (su# t)) t)
ar_su t = axSnd tagSu t

hd_ad : (a b : Term) -> Deriv (eqF (hd (ad# a b)) tagAd)
hd_ad a b = axFst tagAd (ap2 Pair a b)

ar_ad : (a b : Term) -> Deriv (eqF (ar (ad# a b)) (ap2 Pair a b))
ar_ad a b = axSnd tagAd (ap2 Pair a b)

-- First / second argument of an  ad#  node.

ad1 : (a b : Term) -> Deriv (eqF (ap1 Fst (ar (ad# a b))) a)
ad1 a b = ruleTrans (cong1 Fst (ar_ad a b)) (axFst a b)

ad2 : (a b : Term) -> Deriv (eqF (ap1 Snd (ar (ad# a b))) b)
ad2 a b = ruleTrans (cong1 Snd (ar_ad a b)) (axSnd a b)
