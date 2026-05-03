{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleIndBTProto
--
-- Verifying body for ruleIndBT.  Original body:
--
--   body_ruleIndBT = Lift (Comp Fst Snd)
--
-- which extracts  Fst(Snd a) = codeFP  directly from the encoding.
-- The body does NOT consume the IH sub-proofs; the conclusion
--   codeFormula P  is recorded explicitly in the encoding (Parts/RuleIndBT).
--
-- Soundification IfLf-gates on  Snd a  being Pair-shaped.  On pass:
-- output  Fst(Snd a) = codeFP .  On fail: output codeTriv.  This is the
-- minimum sound verifier: the only attack vector is forging a leaf at
-- the outer Snd of the encoding (which would otherwise propagate via
-- safe-default axFstLf to a leaf output).
--
-- Implementation as Fun1 over t = Pair a bb introduced by
--   Post verifierBTF1 Pair :
--
--   verifierBTF1 = Comp2 IfLf <discriminant>
--                    (Comp2 Pair (KT codeTriv) doAssemblyF1)
--
-- where the discriminant is  Snd(Fst t) = Snd a  and the assembly is
-- Fst(Snd(Fst t)) = Fst(Snd a) = codeFP.
--
-- ASCII only.

module BRA.SoundRuleIndBTProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)

----------------------------------------------------------------------
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- Extractors over t = Pair a bb.
--   Fst t            = a
--   Snd(Fst t)       = Snd a               -- the discriminant
--   Fst(Snd(Fst t))  = Fst(Snd a)         -- = codeFP

getDisc : Fun1
getDisc = Comp Snd Fst

getCodeFP : Fun1
getCodeFP = Comp Fst getDisc

verifierBTF1 : Fun1
verifierBTF1 =
  Comp2 IfLf getDisc
    (Comp2 Pair (KT codeTriv) getCodeFP)

body_ruleIndBT_v : Fun2
body_ruleIndBT_v = Post verifierBTF1 Pair
