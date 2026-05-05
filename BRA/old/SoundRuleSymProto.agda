{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleSymProto
--
-- Verifying body for ruleSym.  Mirrors SoundMpProto / SoundRuleInstProto:
--
--   body_ruleSym = Fan (Post (Comp Snd (Comp Snd Snd)) Pair)
--                       (Post (Comp Fst (Comp Snd Snd)) Pair)
--                       Pair
--
-- body_ruleSym(a, bb) = Pair (Snd(Snd bb)) (Fst(Snd bb))
-- (the equation-flip: from code(eqn t u) = Pair payT payU to
-- code(eqn u t) = Pair payU payT).
--
-- The verifying version IfLf-gates on the Pair-shape of Snd bb (the
-- IH).  If Snd bb is leaf O (malformed sub-proof), output codeTriv =
-- falseT = Pair O O.  Else (Pair-shaped), do the swap.
--
-- Implementation as Fun1 over t' = Pair a bb introduced by
-- Post verifierRSF1 Pair :
--
--   verifierRSF1 = Comp2 IfLf (Comp Snd Snd)               -- discriminant: Snd bb
--                    (Comp2 Pair (KT codeTriv)             -- fail branch: codeTriv
--                                doSwapF1)                 -- pass branch: do swap
--
--   doSwapF1 = Comp2 Pair (Comp Snd (Comp Snd Snd))        -- Snd(Snd bb)
--                          (Comp Fst (Comp Snd Snd))        -- Fst(Snd bb)
--
-- Identifier convention: camelCase throughout.  ASCII only.

module BRA.SoundRuleSymProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

----------------------------------------------------------------------
-- codeTriv: same as in SoundMpProto / SoundRuleInstProto.

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Snd t = bb              ;  Snd(Snd t) = Snd bb     (= IH)
--   Snd(Snd(Snd t)) = Snd(Snd bb) = payU (after eqn-distribution)
--   Fst(Snd(Snd t)) = Fst(Snd bb) = payT

getIH : Fun1
getIH = Comp Snd Snd

getSndIH : Fun1
getSndIH = Comp Snd (Comp Snd Snd)

getFstIH : Fun1
getFstIH = Comp Fst (Comp Snd Snd)

----------------------------------------------------------------------
-- doSwapF1 : Fun1 over t = Pair a bb.
--   ap1 doSwapF1 t = ap2 Pair (Snd(Snd bb)) (Fst(Snd bb))
-- (the actual ruleSym swap, ready to be selected by axIfLfN on pass).

doSwapF1 : Fun1
doSwapF1 = Comp2 Pair getSndIH getFstIH

----------------------------------------------------------------------
-- verifierRSF1 : Fun1 over t = Pair a bb.
--   ap1 verifierRSF1 t
--     = ap2 IfLf (Snd(Snd bb)) (Pair codeTriv (ap1 doSwapF1 t))
--     = ap2 IfLf (Snd bb)      (Pair codeTriv (Pair (Snd(Snd bb)) (Fst(Snd bb))))
--   pass (Snd bb is Pair _ _) -> Pair (Snd(Snd bb)) (Fst(Snd bb)) = swap
--   fail (Snd bb = O leaf)    -> codeTriv

verifierRSF1 : Fun1
verifierRSF1 =
  Comp2 IfLf getIH
    (Comp2 Pair (KT codeTriv) doSwapF1)

----------------------------------------------------------------------
-- The verifying body for ruleSym.

body_ruleSym_v : Fun2
body_ruleSym_v = Post verifierRSF1 Pair
