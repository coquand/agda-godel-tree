{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundCong1Proto
--
-- Verifying body for cong1.  Original body:
--
--   body_cong1 = Fan
--     (Fan (Lift (KT (reify tagAp1)))
--          (Fan (Lift (Comp Fst Snd))
--               (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
--               Pair)
--          Pair)
--     (Fan (Lift (KT (reify tagAp1)))
--          (Fan (Lift (Comp Fst Snd))
--               (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
--               Pair)
--          Pair)
--     Pair
--
-- builds  Pair (Pair tagAp1 (Pair payF payT_r)) (Pair tagAp1 (Pair payF payU_r)) .
--
-- Verifying version IfLf-gates on the Pair-shape of  Snd(Snd bb)  (=
-- thmT y_h_r , the IH).  Pass: assemble.  Fail (leaf): codeTriv.
--
-- Implementation as Fun1 over t' = Pair a bb introduced by
-- Post verifierC1F1 Pair :
--
--   verifierC1F1 = Comp2 IfLf <ihExtractor>
--                    (Comp2 Pair (KT codeTriv) doAssemblyF1)
--
--   doAssemblyF1 = Comp2 Pair assemblyLeftF1 assemblyRightF1
--   assemblyLeftF1  = Pair tagAp1 (Pair payF (Fst IH))
--   assemblyRightF1 = Pair tagAp1 (Pair payF (Snd IH))
--
-- ASCII only.

module BRA.SoundCong1Proto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

----------------------------------------------------------------------
-- codeTriv: standard safe-default.

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Fst(Snd(Fst t))  = Fst(Snd a)   = payF
--   Snd(Snd(Snd t))  = Snd(Snd bb)  = thmT y_h_r  (the IH)

getPayF : Fun1
getPayF = Comp Fst (Comp Snd Fst)

getIH : Fun1
getIH = Comp Snd (Comp Snd Snd)

getFstIH : Fun1
getFstIH = Comp Fst getIH

getSndIH : Fun1
getSndIH = Comp Snd getIH

----------------------------------------------------------------------
-- Half-assemblers : build Pair tagAp1 (Pair payF X) where X = Fst(IH) or Snd(IH).

assemblyHalf : Fun1 -> Fun1
assemblyHalf getX = Comp2 Pair (KT (reify tagAp1)) (Comp2 Pair getPayF getX)

assemblyLeftF1 : Fun1
assemblyLeftF1 = assemblyHalf getFstIH

assemblyRightF1 : Fun1
assemblyRightF1 = assemblyHalf getSndIH

doAssemblyF1 : Fun1
doAssemblyF1 = Comp2 Pair assemblyLeftF1 assemblyRightF1

----------------------------------------------------------------------
-- Verifier: IfLf-gate on the IH (= Snd(Snd bb)).

verifierC1F1 : Fun1
verifierC1F1 =
  Comp2 IfLf getIH
    (Comp2 Pair (KT codeTriv) doAssemblyF1)

----------------------------------------------------------------------
-- The verifying body for cong1.

body_cong1_v : Fun2
body_cong1_v = Post verifierC1F1 Pair
