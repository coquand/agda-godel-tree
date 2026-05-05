{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleTransProto
--
-- Verifying body for ruleTrans (2 IHs).  Original body:
--
--   body_ruleTrans = Fan (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair)
--                        (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
--                        Pair
--
-- builds  Pair (Fst(Fst(Snd bb))) (Snd(Snd(Snd bb))) .  Verifying version
-- IfLf-gates on the Pair-shape of  Snd bb  (= the IH distribution); on
-- fail outputs codeTriv.  Inner Pair-shape of each IH is trusted to
-- safe-defaults (axFstLf / axSndLf).

module BRA.SoundRuleTransProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

----------------------------------------------------------------------
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Snd t            = bb
--   Snd(Snd t)       = Snd bb               -- the IH distribution
--   Fst(Snd(Snd t))  = Fst(Snd bb) = tjY1
--   Fst(Fst(Snd(Snd t))) = Fst tjY1 = u1
--   Snd(Snd(Snd t))  = Snd(Snd bb) = tjY2
--   Snd(Snd(Snd(Snd t))) = Snd tjY2 = u4

getDisc : Fun1
getDisc = Comp Snd Snd

getU1 : Fun1
getU1 = Comp Fst (Comp Fst getDisc)

getU4 : Fun1
getU4 = Comp Snd (Comp Snd getDisc)

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair getU1 getU4

verifierRTF1 : Fun1
verifierRTF1 =
  Comp2 IfLf getDisc
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

body_ruleTrans_v : Fun2
body_ruleTrans_v = Post verifierRTF1 Pair
