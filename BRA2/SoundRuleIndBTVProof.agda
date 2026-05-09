{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SoundRuleIndBTVProof
--
-- Verifying body  body_ruleIndBT_v  + its evaluation proof.
--
-- (Merged from former  SoundRuleIndBTProto + SoundRuleIndBTVProof  pair.)
--
-- Body shape (no IH consumed; only an encoding-level Pair-shape on
-- Snd a is required):
--
--   body_ruleIndBT_v = Post verifierBTF1 Pair
--
--   verifierBTF1 = Comp2 IfLf getDisc
--                    (Comp2 Pair (KT codeTriv) getCodeFP)
--
-- where the discriminant getDisc extracts  Snd a  and the assembly
-- getCodeFP extracts  Fst (Snd a) = codeFP .  Soundification IfLf-gates
-- on  Snd a  being Pair-shaped.  On pass: output codeFP .  On fail:
-- output codeTriv .

module BRA2.SoundRuleIndBTVProof where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold

----------------------------------------------------------------------
-- Body and helpers (formerly in SoundRuleIndBTProto).

codeTriv : Term
codeTriv = reify (codeFormula (atomic (eqn O O)))

codeTriv_eq_falseT : Eq codeTriv falseT
codeTriv_eq_falseT = refl

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

body_ruleIndBT_v_eval_pass :
  (a bb : Term) (codeFP rest : Term) ->
  Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair codeFP rest))) ->
  Deriv (atomic (eqn (ap2 body_ruleIndBT_v a bb) codeFP))
body_ruleIndBT_v_eval_pass a bb codeFP rest encShape =
  let
      t : Term
      t = ap2 Pair a bb

      ----------------------------------------------------------------
      -- Section A: getDisc t = Snd a  (then = Pair codeFP rest).

      a1 : Deriv (atomic (eqn (ap1 getDisc t) (ap1 Snd (ap1 Fst t))))
      a1 = axComp Snd Fst t

      a2 : Deriv (atomic (eqn (ap1 Fst t) a))
      a2 = axFst a bb

      a3 : Deriv (atomic (eqn (ap1 Snd (ap1 Fst t)) (ap1 Snd a)))
      a3 = cong1 Snd a2

      discEqA : Deriv (atomic (eqn (ap1 getDisc t) (ap1 Snd a)))
      discEqA = ruleTrans a1 a3

      discPair : Deriv (atomic (eqn (ap1 getDisc t) (ap2 Pair codeFP rest)))
      discPair = ruleTrans discEqA encShape

      ----------------------------------------------------------------
      -- Section B: getCodeFP t = codeFP.

      b1 : Deriv (atomic (eqn (ap1 getCodeFP t) (ap1 Fst (ap1 getDisc t))))
      b1 = axComp Fst getDisc t

      b2 : Deriv (atomic (eqn (ap1 Fst (ap1 getDisc t))
                              (ap1 Fst (ap2 Pair codeFP rest))))
      b2 = cong1 Fst discPair

      b3 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair codeFP rest)) codeFP))
      b3 = axFst codeFP rest

      getCodeFPEq : Deriv (atomic (eqn (ap1 getCodeFP t) codeFP))
      getCodeFPEq = ruleTrans b1 (ruleTrans b2 b3)

      ----------------------------------------------------------------
      -- Section C: verifierBTF1 t = codeFP via axIfLfN.

      branchesF1 : Fun1
      branchesF1 = Comp2 Pair (KT codeTriv) getCodeFP

      c1 : Deriv (atomic (eqn (ap1 verifierBTF1 t)
                               (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))))
      c1 = axComp2 IfLf getDisc branchesF1 t

      c2 : Deriv (atomic (eqn (ap1 branchesF1 t)
                               (ap2 Pair (ap1 (KT codeTriv) t) (ap1 getCodeFP t))))
      c2 = axComp2 Pair (KT codeTriv) getCodeFP t

      c3 : Deriv (atomic (eqn (ap1 (KT codeTriv) t) codeTriv))
      c3 = axKT (codeFormula (atomic (eqn O O))) (codeFormula_isValue (atomic (eqn O O))) t

      c4 : Deriv (atomic (eqn (ap2 Pair (ap1 (KT codeTriv) t) (ap1 getCodeFP t))
                               (ap2 Pair codeTriv (ap1 getCodeFP t))))
      c4 = congL Pair (ap1 getCodeFP t) c3

      c5 : Deriv (atomic (eqn (ap2 Pair codeTriv (ap1 getCodeFP t))
                               (ap2 Pair codeTriv codeFP)))
      c5 = congR Pair codeTriv getCodeFPEq

      branchesEq : Deriv (atomic (eqn (ap1 branchesF1 t) (ap2 Pair codeTriv codeFP)))
      branchesEq = ruleTrans c2 (ruleTrans c4 c5)

      c6 : Deriv (atomic (eqn (ap2 IfLf (ap1 getDisc t) (ap1 branchesF1 t))
                               (ap2 IfLf (ap2 Pair codeFP rest) (ap1 branchesF1 t))))
      c6 = congL IfLf (ap1 branchesF1 t) discPair

      c7 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair codeFP rest) (ap1 branchesF1 t))
                               (ap2 IfLf (ap2 Pair codeFP rest)
                                          (ap2 Pair codeTriv codeFP))))
      c7 = congR IfLf (ap2 Pair codeFP rest) branchesEq

      c8 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair codeFP rest)
                                          (ap2 Pair codeTriv codeFP))
                               codeFP))
      c8 = axIfLfN codeFP rest codeTriv codeFP

      verifierEq : Deriv (atomic (eqn (ap1 verifierBTF1 t) codeFP))
      verifierEq = ruleTrans c1 (ruleTrans c6 (ruleTrans c7 c8))

      ----------------------------------------------------------------
      i1 : Deriv (atomic (eqn (ap2 body_ruleIndBT_v a bb) (ap1 verifierBTF1 t)))
      i1 = axPost verifierBTF1 Pair a bb
  in ruleTrans i1 verifierEq
