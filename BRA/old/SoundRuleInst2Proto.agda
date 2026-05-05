{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.SoundRuleInst2Proto
--
-- Verifying body for ruleInst2.  Mirrors SoundRuleInstProto with TWO
-- (var, term) pairs and  subT2  in place of  subT .
--
-- Original body:
--
--   body_ruleInst2 = Fan
--     (Fan (Fan (Lift (Comp Fst Snd))
--               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
--               Pair)
--          (Fan (Lift (Comp Fst (Comp Snd Snd)))
--               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
--               Pair)
--          Pair)                                    -- argsPair extractor
--     (Post (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair)
--                                                  -- codeFP (= thmT y_h_r) extractor
--     subT2                                         -- ran unconditionally
--
-- Verifying version replaces  subT2  with a verifying combinator that
-- IfLf-gates on  codeFP  (the IH).  Pass: run  subT2 .  Fail: codeTriv.
--
-- ASCII only.  No  with .

module BRA.SoundRuleInst2Proto where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv using (falseT)
open import BRA.Sb2 using (subT2)

----------------------------------------------------------------------
codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

----------------------------------------------------------------------
-- argsExtractor : Fun2 over (a, bb).  Returns  Pair (Pair payVarA payTA)
-- (Pair payVarB payTB) .  Closed extractor (depends only on a).

argsExtractor : Fun2
argsExtractor =
  Fan
    (Fan (Lift (Comp Fst Snd))
         (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
         Pair)
    (Fan (Lift (Comp Fst (Comp Snd Snd)))
         (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
         Pair)
    Pair

----------------------------------------------------------------------
-- codepExtractor : Fun2 over (a, bb).  Returns  thmT y_h_r .

codepExtractor : Fun2
codepExtractor =
  Post (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair

----------------------------------------------------------------------
-- The verifying inner combinator.  Fun1 over t' = (Pair argsPair codeFP).
--
--   ap1 verifierRI2F1 t'
--     = ap2 IfLf (Snd t') (Pair codeTriv (subT2 (Fst t') (Snd t')))

verifierRI2F1 : Fun1
verifierRI2F1 =
  Comp2 IfLf Snd
    (Comp2 Pair (KT codeTriv) (Comp2 subT2 Fst Snd))

verifyAndRun2 : Fun2
verifyAndRun2 = Post verifierRI2F1 Pair

----------------------------------------------------------------------
body_ruleInst2_v : Fun2
body_ruleInst2_v =
  Fan argsExtractor codepExtractor verifyAndRun2
