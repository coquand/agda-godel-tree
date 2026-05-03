{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundCongLProto
--
-- Verifying body for congL.  Output:
--
--   Pair (Pair tagAp2 (Pair payG (Pair payT_r payX)))
--        (Pair tagAp2 (Pair payG (Pair payU_r payX)))
--
-- where  payG, payX  are extracted from  a  (closed) and  payT_r, payU_r
-- are  Fst, Snd  of  Snd(Snd bb)  (the IH).  Verifying version IfLf-
-- gates on the Pair-shape of  Snd(Snd bb) ; on fail outputs codeTriv.

module BRA.SoundCongLProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

----------------------------------------------------------------------
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Snd a            = Snd(Fst t)
--   Fst(Snd a)       = Fst(Snd(Fst t))   -- this is (Pair payG payX)
--   Fst(Fst(Snd a))  = Fst(Fst(Snd(Fst t))) = payG
--   Snd(Fst(Snd a))  = Snd(Fst(Snd(Fst t))) = payX
--   Snd(Snd bb)      = Snd(Snd(Snd t))   -- the IH

getInnerArgs : Fun1
getInnerArgs = Comp Fst (Comp Snd Fst)
  -- ap1 t = Fst(Snd(Fst t)) = Fst(Snd a) = (Pair payG payX)

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

----------------------------------------------------------------------
-- Half-assemblers : Pair tagAp2 (Pair payG (Pair partIH payX))
-- where partIH is either Fst(IH) or Snd(IH).

assemblyHalfL : Fun1 -> Fun1
assemblyHalfL getPart =
  Comp2 Pair (KT (reify tagAp2))
    (Comp2 Pair getPayG
      (Comp2 Pair getPart getPayX))

assemblyLeftF1 : Fun1
assemblyLeftF1 = assemblyHalfL getFstIH

assemblyRightF1 : Fun1
assemblyRightF1 = assemblyHalfL getSndIH

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair assemblyLeftF1 assemblyRightF1

verifierCLF1 : Fun1
verifierCLF1 =
  Comp2 IfLf getIH
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

body_congL_v : Fun2
body_congL_v = Post verifierCLF1 Pair
