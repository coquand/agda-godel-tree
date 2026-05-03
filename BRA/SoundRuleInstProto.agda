{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleInstProto
--
-- Verifying body for ruleInst.  Mirrors SoundMpProto pattern:
--
--   body_ruleInst = Fan
--                     (Lift (Comp Fst Snd))                     -- args extractor
--                     (Post (Comp Snd (Comp Snd Snd)) Pair)     -- thmT y_h extractor
--                     subT                                      -- ran unconditionally
--
-- Replace the unconditional  subT  with a verifying  verifyAndRun
-- combinator that first checks  thmT y_h  is Pair-shaped (i.e. not a
-- leaf  O ).  On pass, run the existing  subT  pipeline.  On fail,
-- output  codeTriv = falseT .
--
-- The verification is a single  IfLf  gate on the second extracted
-- value (thmT y_h):
--
--   IfLf thmT_y_h  (Pair codeTriv  (subT argsPair thmT_y_h))
--     thmT_y_h = O          -> codeTriv         (axIfLfL)
--     thmT_y_h = Pair p q   -> subT args ...    (axIfLfN)
--
-- Implementation as Fun1 over the synthesized inner pair
--   t' = Pair argsPair thmT_y_h
-- introduced by  Post verifierRIF1 Pair :
--
--   verifierRIF1 = Comp2 IfLf Snd
--                    (Comp2 Pair (KT codeTriv)
--                                (Comp2 subT Fst Snd))
--
-- Identifier convention: camelCase throughout.  ASCII only.

module BRA.SoundRuleInstProto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)
open import BRA.SubT  using (subT)

----------------------------------------------------------------------
-- codeTriv: the safe-default output on verification failure.
--
-- Definitionally equal to  falseT = ap2 Pair O O  (the encoding of
-- the trivially-true atomic equation  0 = 0 ).

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- The verifying inner combinator.  Fun1 over t' = (Pair argsPair thmT_y_h).
--
--   ap1 verifierRIF1 t'
--     = ap2 IfLf (Snd t') (Pair codeTriv (subT (Fst t') (Snd t')))
--     = ap2 IfLf thmT_y_h (Pair codeTriv (subT argsPair thmT_y_h))

verifierRIF1 : Fun1
verifierRIF1 =
  Comp2 IfLf Snd
    (Comp2 Pair (KT codeTriv) (Comp2 subT Fst Snd))

----------------------------------------------------------------------
-- Verifying-then-running helper.  Fun2.
--
--   ap2 verifyAndRun argsPair thmT_y_h
--     = ap1 verifierRIF1 (Pair argsPair thmT_y_h)
--     = IfLf thmT_y_h (Pair codeTriv (subT argsPair thmT_y_h))

verifyAndRun : Fun2
verifyAndRun = Post verifierRIF1 Pair

----------------------------------------------------------------------
-- The verifying body for ruleInst.  Fun2.
--
--   body_ruleInst_v a bb
--     = ap2 verifyAndRun argsPair_extracted thmT_y_h_extracted
-- where
--   argsPair_extracted   = ap2 (Lift (Comp Fst Snd)) a bb
--                        = Fst (Snd a)                      (closed extractor)
--   thmT_y_h_extracted  = ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb
--                        = Snd (Snd bb)                     (after distrib)

body_ruleInst_v : Fun2
body_ruleInst_v =
  Fan
    (Lift (Comp Fst Snd))
    (Post (Comp Snd (Comp Snd Snd)) Pair)
    verifyAndRun
