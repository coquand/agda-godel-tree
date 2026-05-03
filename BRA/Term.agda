{-# OPTIONS --safe --without-K --exact-split #-}

module BRA.Term where

open import BRA.Base

------------------------------------------------------------------------
-- Mutual data types: Fun1 (1-ary functors), Fun2 (2-ary functors), Term

data Fun1 : Set
data Fun2 : Set
data Term : Set

data Fun1 where
  I     : Fun1
  Fst   : Fun1
  Snd   : Fun1
  Comp  : Fun1 -> Fun1 -> Fun1
  Comp2 : Fun2 -> Fun1 -> Fun1 -> Fun1
  Z     : Fun1                        -- constant-leaf functor (= Guard's o).
                                      -- KT t (was a constructor) is now a
                                      -- defined function below.
                                      -- Rec (was a constructor) is now a
                                      -- defined function below, on top of
                                      -- treeRec.

data Fun2 where
  Pair    : Fun2
  Const   : Fun2
  Lift    : Fun1 -> Fun2
  Post    : Fun1 -> Fun2 -> Fun2
  Fan     : Fun2 -> Fun2 -> Fun2 -> Fun2
  IfLf    : Fun2
  TreeEq  : Fun2
  treeRec : Fun1 -> Fun2 -> Fun2
  -- treeRec f s p O          = ap1 f p
  -- treeRec f s p (Pair a b) = ap2 s (Pair p (Pair a b))
  --                                  (Pair (treeRec f s p a) (treeRec f s p b))
  -- Mirrors Guard's Rfgh (guard15.pdf p.10, axioms 9-10).  RecP and Rec
  -- below are Agda definitions on top of treeRec.

data Term where
  O   : Term
  var : Nat -> Term
  ap1 : Fun1 -> Term -> Term
  ap2 : Fun2 -> Term -> Term -> Term

------------------------------------------------------------------------
-- RecP: legacy parameterised tree-recursor.  Defined in terms of
-- treeRec (since Z p = O makes the leaf cases match exactly).

RecP : Fun2 -> Fun2
RecP s = treeRec Z s

------------------------------------------------------------------------
-- Rec: legacy 1-ary tree-recursor with leaf payload z = O.  Defined as
--   Rec s = Comp2 (treeRec Z s) Z I
-- so that  ap1 (Rec s) x = ap2 (treeRec Z s) (ap1 Z x) (ap1 I x)
--                        BRA-equational to ap2 (treeRec Z s) O x.
--
-- Only z = O is used in the codebase (cor, thmT).  The previous
-- z-parameterised  Rec : Term -> Fun2 -> Fun1  constructor was unsound
-- in conjunction with  KT  for open  z  and is no longer needed.

Rec : Fun2 -> Fun1
Rec s = Comp2 (treeRec Z s) Z I

------------------------------------------------------------------------
-- Equations

data Equation : Set where
  eqn : Term -> Term -> Equation

eqnL : Equation -> Term
eqnL (eqn l r) = l

eqnR : Equation -> Term
eqnR (eqn l r) = r

------------------------------------------------------------------------
-- reify : Tree -> Term

reify : Tree -> Term
reify lf       = O
reify (nd a b) = ap2 Pair (reify a) (reify b)

------------------------------------------------------------------------
-- Tag constants
-- tagVar is distinct from all natCode values (which start with lf).

-- tagO removed in 2026-04-26 refactor: code O = lf directly,
-- so cor O = O (transparency for the leaf constant).

tagVar : Tree
tagVar = nd (nd (nd lf lf) lf) lf

tagAp1 : Tree
tagAp1 = nd lf (nd lf lf)

tagAp2 : Tree
tagAp2 = nd lf (nd lf (nd lf lf))

------------------------------------------------------------------------
-- Coding functions (mutual)

codeF1 : Fun1 -> Tree
codeF2 : Fun2 -> Tree
code   : Term -> Tree

-- Tags start at natCode 26 to avoid collision with proof-encoding tags (0..25).
-- This ensures codeF1/codeF2 values never match any natCode 0..25 at intermediate
-- dispatch levels.

codeF1 I             = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) lf
codeF1 Fst           = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) lf
codeF1 Snd           = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) lf
codeF1 (Comp f g)    = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) (nd (codeF1 f) (codeF1 g))
codeF1 (Comp2 h f g) = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) (nd (codeF2 h) (nd (codeF1 f) (codeF1 g)))
codeF1 Z             = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))) lf

codeF2 Pair          = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) lf
codeF2 Const         = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) lf
codeF2 (Lift f)      = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) (codeF1 f)
codeF2 (Post f h)    = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) (nd (codeF1 f) (codeF2 h))
codeF2 (Fan h1 h2 h) = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) (nd (codeF2 h1) (nd (codeF2 h2) (codeF2 h)))
codeF2 IfLf          = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))) lf
codeF2 TreeEq        = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))) lf
codeF2 (treeRec f s) = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))))) (nd (codeF1 f) (codeF2 s))

code O             = lf
code (var n)       = nd tagVar (natCode n)
code (ap1 f t)     = nd tagAp1 (nd (codeF1 f) (code t))
code (ap2 g t1 t2) = nd tagAp2 (nd (codeF2 g) (nd (code t1) (code t2)))

------------------------------------------------------------------------
-- Coded-term helpers

mkAp1 : Tree -> Tree -> Tree
mkAp1 fCode tCode = nd tagAp1 (nd fCode tCode)

mkAp2 : Tree -> Tree -> Tree -> Tree
mkAp2 gCode aCode bCode = nd tagAp2 (nd gCode (nd aCode bCode))

------------------------------------------------------------------------
-- Substitution (mutual, metalevel)

subst   : Nat -> Term -> Term -> Term
substF1 : Nat -> Term -> Fun1 -> Fun1
substF2 : Nat -> Term -> Fun2 -> Fun2

subst x r O           = O
subst x r (var n)     = boolCase (natEq n x) r (var n)
subst x r (ap1 f t)   = ap1 (substF1 x r f) (subst x r t)
subst x r (ap2 g a b) = ap2 (substF2 x r g) (subst x r a) (subst x r b)

substF1 x r I             = I
substF1 x r Fst           = Fst
substF1 x r Snd           = Snd
substF1 x r (Comp f g)    = Comp (substF1 x r f) (substF1 x r g)
substF1 x r (Comp2 h f g) = Comp2 (substF2 x r h) (substF1 x r f) (substF1 x r g)
substF1 x r Z             = Z

substF2 x r Pair          = Pair
substF2 x r Const         = Const
substF2 x r (Lift f)      = Lift (substF1 x r f)
substF2 x r (Post f h)    = Post (substF1 x r f) (substF2 x r h)
substF2 x r (Fan h1 h2 h) = Fan (substF2 x r h1) (substF2 x r h2) (substF2 x r h)
substF2 x r IfLf          = IfLf
substF2 x r TreeEq        = TreeEq
substF2 x r (treeRec f s) = treeRec (substF1 x r f) (substF2 x r s)

substEq : Nat -> Term -> Equation -> Equation
substEq x r (eqn l r') = eqn (subst x r l) (subst x r r')

------------------------------------------------------------------------
-- KT : Term -> Fun1   (constant-t functor; defined, not primitive).
--
-- For canonical t = reify v (built from O and ap2 Pair only), this
-- builds a Fun1 expression that, applied to any Term, evaluates to t.
-- For non-canonical t, defaults to Z (returns O); used only at canonical
-- inputs in the codebase.
--
-- Mirrors Guard's framework: he has only o (= our Z) primitive, and
-- builds other constants by composition.

KT : Term -> Fun1
KT O                       = Z
KT (ap2 Pair a b)          = Comp2 Pair (KT a) (KT b)
KT (var n)                 = Z
KT (ap1 f t)               = Z
KT (ap2 Const a b)         = Z
KT (ap2 (Lift f) a b)      = Z
KT (ap2 (Post f h) a b)    = Z
KT (ap2 (Fan h1 h2 h) a b) = Z
KT (ap2 IfLf a b)          = Z
KT (ap2 TreeEq a b)        = Z
KT (ap2 (treeRec f s) a b) = Z


------------------------------------------------------------------------
-- Coded substitution (on trees).
--
-- codedSubst repl varCode t: in coded term t, replace any subtree
-- equal to varCode with repl, recursing into children otherwise.
-- Typically varCode = code (var n).
--
-- Whole-node test: matches the combinator-level subT (BRA/SubT.agda),
-- whose stepSubT uses TreeEq on the full current node.  On well-formed
-- term codes the only subtrees equal to code (var n) appear at variable
-- nodes, so this agrees with the term-level subst on Term.

codedSubst : Tree -> Tree -> Tree -> Tree
codedSubst repl varCode lf = lf
codedSubst repl varCode (nd a b) =
  boolCase (treeEq varCode (nd a b))
    repl
    (nd (codedSubst repl varCode a) (codedSubst repl varCode b))
