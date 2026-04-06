{-# OPTIONS --safe --without-K --exact-split #-}

-- EvalCode.agda
-- A ground-term evaluator on coded terms.
--
-- evalCode : Fun1 = Rec O evalStep
--
-- Dispatches on the term tag in the coded term:
--   tagO   (= O)                   : return O
--   tagAp1 (= Pair(O, Pair(O, O))) : return evalCode of the argument
--                                     (strips the functor, correct for I)
--   default                        : passthrough (Pair of recursive results)
--
-- Design: the passthrough means evalCode on internal tree nodes
-- (like functor codes) returns Pair(evalCode(left), evalCode(right)).
-- For tagAp1 case, Snd(Snd(recs)) extracts evalCode of the argument
-- code through the passthrough chain:
--   recs = Pair(evalCode(tag), evalCode(nd(fCode, tCode)))
--   evalCode(nd(fCode, tCode)) = Pair(evalCode(fCode), evalCode(tCode))
--     [passthrough, since fCode tag doesn't match tagO/tagAp1]
--   Snd(evalCode(nd(fCode, tCode))) = evalCode(tCode)
--   So Snd(Snd(recs)) = evalCode(tCode)
--
-- Limitation: tagAp1 always returns the evaluated argument, which is
-- correct for I but wrong for Fst, Snd, Comp, etc. A full evaluator
-- would need secondary dispatch on the functor code.

module Guard.EvalCode where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs

------------------------------------------------------------------------
-- Tag constants as Terms

tagOT : Term
tagOT = O

tagAp1T : Term
tagAp1T = reify tagAp1

------------------------------------------------------------------------
-- Tag checks as Fun2

isTagO : Fun2
isTagO = Fan (Lift Fst) (kF2 tagOT) TreeEq

isTagAp1 : Fun2
isTagAp1 = Fan (Lift Fst) (kF2 tagAp1T) TreeEq

------------------------------------------------------------------------
-- Case handlers

-- tagO: return O (the value of the constant O)
tagOCase : Fun2
tagOCase = kF2 O

-- tagAp1: return Snd(Snd(recs)) = evalCode(argCode)
-- Via passthrough: recs = Pair(evalCode(tag), evalCode(nd(fCode, argCode)))
-- evalCode(nd(fCode, argCode)) = Pair(junk, evalCode(argCode))
-- So Snd(Snd(recs)) = evalCode(argCode)
tagAp1Case : Fun2
tagAp1Case = Post Snd (Post Snd sndArg2)

------------------------------------------------------------------------
-- evalStep : Fun2

evalStep : Fun2
evalStep = branch isTagO tagOCase (branch isTagAp1 tagAp1Case sndArg2)

------------------------------------------------------------------------
-- evalCode : Fun1

evalCode : Fun1
evalCode = Rec O evalStep
