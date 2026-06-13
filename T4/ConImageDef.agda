{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ConImageDef -- the IMAGE-restricted consistency hypothesis.
--
-- The surprise-GII descent assumes  ConOpenInt :  T |- ~(thmT(x) = code(0=1))
-- OPEN over  var 0 , i.e. T proves its own consistency for EVERY code  x .
-- But inspection of the two consumers ( T4.DayClashN and T4.SurpriseGIINum )
-- shows  con  is used SOLELY through
--
--     ruleInst 0 (gFunN w) con
--
-- i.e. instantiated at arguments in the IMAGE of the Chaitin diagonal
-- transformer  gFunN .   So the descent does NOT need full open consistency ;
-- it needs only
--
--     ConImage = (w : Term) -> Deriv (neg (eqF (ap1 thmT (gFunN w)) codeFalse))
--
-- "T proves that no diagonal program  gFunN w  is a proof of  0 = 1".
-- This is the Nelson-style LOCAL consistency of the special proofs that
-- actually arise in the Kritchman-Raz / Chaitin machinery.
--
-- ConImage is WEAKER than ConOpenInt :  fromOpen exhibits the implication
-- ConOpenInt -> ConImage  ( one  ruleInst  per image point ).  There is NO
-- arrow back : ConImage constrains only the image of  gFunN , not all  x .

module T4.ConImageDef where

open import T4.Base
open import T4.Code using ( codeFalse )
open import T4.ThmT using ( thmT )
open import T4.ChaitinNumGIAbs using ( gFunN )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )

------------------------------------------------------------------------
-- The image-restricted consistency hypothesis.

ConImage : Set
ConImage = (w : Term) -> Deriv (neg (eqF (ap1 thmT (gFunN w)) codeFalse))

------------------------------------------------------------------------
-- Global open consistency implies image consistency ( the converse fails ).

fromOpen : ConOpenInt -> ConImage
fromOpen con w = ruleInst 0 (gFunN w) con
