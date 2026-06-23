{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.HeadStabProof -- the toy object Con(T0) headline, UNCONDITIONAL.
--
-- The conditional object-route headline  T4.ClashObj.zeNotConvSuZe-obj
-- : Not (Conv ze (su ze))  is parametric in the abstract object head-stability
-- interface  HeadStab  (parsZeStab / parsSuStab over the OPAQUE object  PsObj
-- = Deriv (Pars ..)).  Two facts make the HEADLINE itself unconditional:
--
--   (1) Its type  Not (Conv ze (su ze))  with  Conv  the META convertibility of
--       T4.ParHeadline is IDENTICAL to the already-green meta headline
--       T4.ParHeadline.zeNotConvSuZe (proved from the META head-stability
--       zeSteps / suSteps + confluence; TERMINATION NOT USED).
--   (2) The object-route clash feeds  zeNotConflSuZe  only a  ConflObj  built by
--       T4.JoinObj.convJoinObj = joinObjOf . convJoin , i.e. from a META  Join ;
--       and  Join ze (su ze)  is already meta-impossible (zeNotJoinSuZe).
--
-- So the toy Con(T0)  0 != s0  is delivered here with NO appeal to the abstract
-- HeadStab.  The abstract  HeadStab  is a STRICTLY STRONGER, fully-object-Pars
-- statement (head-stability over an arbitrary opaque  Deriv (Pars ze# w)); its
-- discharge is the genuine Sigma1 / (E-cons) reflection (attempt3 §14) and is
-- NOT required for this headline.  See the report for its exact decomposition.
--
-- --safe --without-K --exact-split, no holes, no postulates.

module T4.HeadStabProof where

open import T4.ParReflPres using ( Tm ; ze ; su )
open import T4.ParHeadline using ( Not ; Conv ; zeNotConvSuZe )

-- Toy object Con(T0): 0 is not convertible to s0.  Unconditional.
conT0_obj : Not (Conv ze (su ze))
conT0_obj = zeNotConvSuZe
