{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.SubstTFor where

open import Guard.Base
open import Guard.Term

------------------------------------------------------------------------
-- Variable conventions: var 11 = replacement, var 12 = target

private
  v11 : Nat
  v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

  v12 : Nat
  v12 = suc v11

------------------------------------------------------------------------
-- tagVarT : the tagVar tree embedded as a Term

tagVarT : Term
tagVarT = reify tagVar

------------------------------------------------------------------------
-- Helper Fun2 combinators

-- sndArg(orig, recs) = recs
sndArg : Fun2
sndArg = Post Snd Pair

-- constF1 t : Fun1 that always returns t (using KT)
-- constF2 t : Fun2 that always returns t
constF2 : Term -> Fun2
constF2 t = Lift (KT t)

------------------------------------------------------------------------
-- Step function components

-- isVarF(orig, recs) = TreeEq(Fst(orig), tagVarT)
-- "is the left child of this node the variable tag?"
isVarF : Fun2
isVarF = Fan (Lift Fst) (constF2 tagVarT) TreeEq

-- matchTgtF(orig, recs) = TreeEq(Snd(orig), var 12)
-- "does the right child match the target?"
matchTgtF : Fun2
matchTgtF = Fan (Lift Snd) (constF2 (var v12)) TreeEq

-- replOrigF(orig, recs) = Pair(var 11, orig)
-- "pair of (replacement, original) for IfLf selection"
replOrigF : Fun2
replOrigF = Fan (constF2 (var v11)) Const Pair

-- innerBranchF(orig, recs) = IfLf(matchTgt, Pair(var 11, orig))
-- "if target matches: replacement, else: original node"
innerBranchF : Fun2
innerBranchF = Fan matchTgtF replOrigF IfLf

-- outerPairF(orig, recs) = Pair(innerBranch, recs)
-- "pair of (variable-case result, non-variable-case result)"
outerPairF : Fun2
outerPairF = Fan innerBranchF sndArg Pair

------------------------------------------------------------------------
-- The full step function for substTFor
--
-- stepSubst(orig, recs) = IfLf(isVar, Pair(innerBranch, recs))
--
-- If isVar = O (tag is tagVar):
--   return innerBranch = IfLf(matchTgt, Pair(replacement, orig))
-- Else (tag is not tagVar):
--   return recs (recursive results)

stepSubst : Fun2
stepSubst = Fan isVarF outerPairF IfLf

------------------------------------------------------------------------
-- substTFor : Fun1
-- Tree recursion with O as base (for lf -> lf) and stepSubst.
-- Applied to a coded term with var 11 = replacement, var 12 = target.

substTFor : Fun1
substTFor = Rec O stepSubst
