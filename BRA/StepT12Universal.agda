{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.StepT12Universal
--
-- Universal evalCorrect dispatcher over Fun1/Fun2 EXCLUDING the Rec
-- constructor.  Rec is the only Fun1 case where evalFun1's behaviour is
-- conditional on z being canonical (= reify zT for some Tree zT); the
-- placeholder evalFun1 (Rec z s) lf = lf is incorrect for non-canonical z,
-- so a uniform evalCorrectFun1 over all of Fun1 cannot exist.
--
-- However, in our codebase the ONLY Rec is the outermost thmT = Rec O stepProto.
-- Every sub-functor of stepProto (discComb, branchesTop, dispatch, body_X,
-- branch_X, next_X, checkTag_X for ~30 axioms) is built from
--   I, Fst, Snd, Z, Comp, Comp2, Pair, Const, Lift, Post, Fan, IfLf, TreeEq,
--   RecP, KT(closed-Term).
-- None of these are Rec.  We carve out this Rec-free fragment via NoRec1/NoRec2
-- witnesses, dispatching at the witness level: for each non-Rec constructor,
-- call the corresponding evalCorrect_X helper.
--
-- KT(t) reduces to Z or Comp2 Pair (KT a) (KT b) recursively, so NoRec1 (KT t)
-- holds uniformly via  noRec1_KT  (recursion on t).
--
-- No postulates, no holes.

module BRA.StepT12Universal where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.StepT12

------------------------------------------------------------------------
-- NoRec1 / NoRec2 : inductive certification that a Fun1/Fun2 contains no Rec.

data NoRec1 : Fun1 -> Set
data NoRec2 : Fun2 -> Set

data NoRec1 where
  nr_I     : NoRec1 I
  nr_Fst   : NoRec1 Fst
  nr_Snd   : NoRec1 Snd
  nr_Z     : NoRec1 Z
  nr_Comp  : {f g : Fun1} -> NoRec1 f -> NoRec1 g ->
             NoRec1 (Comp f g)
  nr_Comp2 : {h : Fun2} {f g : Fun1} ->
             NoRec2 h -> NoRec1 f -> NoRec1 g ->
             NoRec1 (Comp2 h f g)

data NoRec2 where
  nr_Pair   : NoRec2 Pair
  nr_Const  : NoRec2 Const
  nr_Lift   : {f : Fun1} -> NoRec1 f -> NoRec2 (Lift f)
  nr_Post   : {f : Fun1} {h : Fun2} ->
              NoRec1 f -> NoRec2 h -> NoRec2 (Post f h)
  nr_Fan    : {h1 h2 h : Fun2} ->
              NoRec2 h1 -> NoRec2 h2 -> NoRec2 h ->
              NoRec2 (Fan h1 h2 h)
  nr_IfLf   : NoRec2 IfLf
  nr_TreeEq : NoRec2 TreeEq
  nr_RecP   : {s : Fun2} -> NoRec2 s -> NoRec2 (RecP s)

------------------------------------------------------------------------
-- noRec1_KT : NoRec1 (KT t) for any closed Term t.
--
-- KT's pattern match in BRA.Term.agda:
--   KT O                       = Z
--   KT (ap2 Pair a b)          = Comp2 Pair (KT a) (KT b)
--   KT (var n)                 = Z
--   KT (ap1 f t)               = Z
--   KT (ap2 Const a b)         = Z
--   KT (ap2 (Lift f) a b)      = Z
--   KT (ap2 (Post f h) a b)    = Z
--   KT (ap2 (Fan h1 h2 h) a b) = Z

noRec1_KT : (t : Term) -> NoRec1 (KT t)
noRec1_KT O                       = nr_Z
noRec1_KT (ap2 Pair a b)          = nr_Comp2 nr_Pair (noRec1_KT a) (noRec1_KT b)
noRec1_KT (var n)                 = nr_Z
noRec1_KT (ap1 f t)               = nr_Z
noRec1_KT (ap2 Const a b)         = nr_Z
noRec1_KT (ap2 (Lift f) a b)      = nr_Z
noRec1_KT (ap2 (Post f h) a b)    = nr_Z
noRec1_KT (ap2 (Fan h1 h2 h) a b) = nr_Z
noRec1_KT (ap2 IfLf a b)          = nr_Z
noRec1_KT (ap2 TreeEq a b)        = nr_Z
noRec1_KT (ap2 (RecP s) a b)      = nr_Z

------------------------------------------------------------------------
-- Universal dispatchers, mutually recursive over Fun1/Fun2 + NoRec witness.

evalCorrectFun1NoRec :
  {F : Fun1} -> NoRec1 F ->
  (i : Tree) -> EvalCorrect1 F i

evalCorrectFun2NoRec :
  {G : Fun2} -> NoRec2 G ->
  (a b : Tree) -> EvalCorrect2 G a b

evalCorrectFun1NoRec nr_I               i = evalCorrect_I i
evalCorrectFun1NoRec nr_Fst             i = evalCorrect_Fst i
evalCorrectFun1NoRec nr_Snd             i = evalCorrect_Snd i
evalCorrectFun1NoRec nr_Z               i = evalCorrect_Z i
evalCorrectFun1NoRec (nr_Comp {f} {g} nf ng) i =
  evalCorrect_Comp f g (evalCorrectFun1NoRec nf) (evalCorrectFun1NoRec ng) i
evalCorrectFun1NoRec (nr_Comp2 {h} {f} {g} nh nf ng) i =
  evalCorrect_Comp2 h f g
    (evalCorrectFun1NoRec nf) (evalCorrectFun1NoRec ng)
    (evalCorrectFun2NoRec nh) i

evalCorrectFun2NoRec nr_Pair             a b = evalCorrect_Pair a b
evalCorrectFun2NoRec nr_Const            a b = evalCorrect_Const a b
evalCorrectFun2NoRec (nr_Lift {f} nf)    a b =
  evalCorrect_Lift f (evalCorrectFun1NoRec nf) a b
evalCorrectFun2NoRec (nr_Post {f} {h} nf nh) a b =
  evalCorrect_Post f h
    (evalCorrectFun2NoRec nh) (evalCorrectFun1NoRec nf) a b
evalCorrectFun2NoRec (nr_Fan {h1} {h2} {h} nh1 nh2 nh) a b =
  evalCorrect_Fan h1 h2 h
    (evalCorrectFun2NoRec nh1) (evalCorrectFun2NoRec nh2) (evalCorrectFun2NoRec nh)
    a b
evalCorrectFun2NoRec nr_IfLf             a b = evalCorrect_IfLf a b
evalCorrectFun2NoRec nr_TreeEq           a b = evalCorrect_TreeEq a b
evalCorrectFun2NoRec (nr_RecP {s} ns)    a b =
  evalCorrect_RecP s (evalCorrectFun2NoRec ns) a b
