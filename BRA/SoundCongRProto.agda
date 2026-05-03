{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundCongRProto
--
-- Verifying body for congR.  Mirrors SoundCongLProto with the inner Pair
-- swapped: output is
--
--   Pair (Pair tagAp2 (Pair payG (Pair payX payT_r)))
--        (Pair tagAp2 (Pair payG (Pair payX payU_r)))
--
-- (note  Pair payX partIH  vs  Pair partIH payX  in congL.)

module BRA.SoundCongRProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

getInnerArgs : Fun1
getInnerArgs = Comp Fst (Comp Snd Fst)

getPayG : Fun1
getPayG = Comp Fst getInnerArgs

getPayX : Fun1
getPayX = Comp Snd getInnerArgs

getIH : Fun1
getIH = Comp Snd (Comp Snd Snd)

getFstIH : Fun1
getFstIH = Comp Fst getIH

getSndIH : Fun1
getSndIH = Comp Snd getIH

-- congR's inner Pair: Pair payX partIH (swap from congL).

assemblyHalfR : Fun1 -> Fun1
assemblyHalfR getPart =
  Comp2 Pair (KT (reify tagAp2))
    (Comp2 Pair getPayG
      (Comp2 Pair getPayX getPart))

assemblyLeftF1 : Fun1
assemblyLeftF1 = assemblyHalfR getFstIH

assemblyRightF1 : Fun1
assemblyRightF1 = assemblyHalfR getSndIH

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair assemblyLeftF1 assemblyRightF1

verifierCRF1 : Fun1
verifierCRF1 =
  Comp2 IfLf getIH
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

body_congR_v : Fun2
body_congR_v = Post verifierCRF1 Pair
