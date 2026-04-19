{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.Term where

open import Guard.Base

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
  Rec   : Term -> Fun2 -> Fun1
  KT    : Term -> Fun1

data Fun2 where
  Pair   : Fun2
  Const  : Fun2
  Lift   : Fun1 -> Fun2
  Post   : Fun1 -> Fun2 -> Fun2
  Fan    : Fun2 -> Fun2 -> Fun2 -> Fun2
  IfLf   : Fun2
  TreeEq : Fun2
  RecP   : Fun2 -> Fun2
  -- RecP s: parameterised tree recursion.
  --   ap2 (RecP s) p O           = O
  --   ap2 (RecP s) p (Pair a b) = ap2 s (Pair p (Pair a b))
  --                                    (Pair (ap2 (RecP s) p a) (ap2 (RecP s) p b))
  -- Used by V3 case23 to construct closedSubstTFor dynamically from encoded
  -- substitution parameters — see Guard/Thm14EV3.agda (ruleInst case).

data Term where
  O   : Term
  var : Nat -> Term
  ap1 : Fun1 -> Term -> Term
  ap2 : Fun2 -> Term -> Term -> Term

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

tagO   : Tree
tagO   = lf

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
-- dispatch levels, allowing sndArg2 passthrough in thFunTFor's Rec structure.

codeF1 I             = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) lf
codeF1 Fst           = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) lf
codeF1 Snd           = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) lf
codeF1 (Comp f g)    = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) (nd (codeF1 f) (codeF1 g))
codeF1 (Comp2 h f g) = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) (nd (codeF2 h) (nd (codeF1 f) (codeF1 g)))
codeF1 (Rec z s)     = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))) (nd (code z) (codeF2 s))
codeF1 (KT t)        = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))) (code t)

codeF2 Pair          = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) lf
codeF2 Const         = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) lf
codeF2 (Lift f)      = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) (codeF1 f)
codeF2 (Post f h)    = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) (nd (codeF1 f) (codeF2 h))
codeF2 (Fan h1 h2 h) = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) (nd (codeF2 h1) (nd (codeF2 h2) (codeF2 h)))
codeF2 IfLf          = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))) lf
codeF2 TreeEq        = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))) lf
codeF2 (RecP s)      = nd (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))) (codeF2 s)

code O             = nd tagO lf
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
substF1 x r (Rec z s)     = Rec (subst x r z) (substF2 x r s)
substF1 x r (KT t)        = KT (subst x r t)

substF2 x r Pair          = Pair
substF2 x r Const         = Const
substF2 x r (Lift f)      = Lift (substF1 x r f)
substF2 x r (Post f h)    = Post (substF1 x r f) (substF2 x r h)
substF2 x r (Fan h1 h2 h) = Fan (substF2 x r h1) (substF2 x r h2) (substF2 x r h)
substF2 x r IfLf          = IfLf
substF2 x r TreeEq        = TreeEq
substF2 x r (RecP s)      = RecP (substF2 x r s)

substEq : Nat -> Term -> Equation -> Equation
substEq x r (eqn l r') = eqn (subst x r l) (subst x r r')

------------------------------------------------------------------------
-- Coded substitution (on trees)
-- codedSubst repl tgt t: in coded term t, replace (nd tagVar tgt) with repl.
-- Only tagVar nodes trigger replacement; all other nodes recurse into children.

codedSubst : Tree -> Tree -> Tree -> Tree
codedSubst repl tgt lf = lf
codedSubst repl tgt (nd a b) =
  boolCase (treeEq a tagVar)
    (boolCase (treeEq b tgt) repl (nd a b))
    (nd (codedSubst repl tgt a) (codedSubst repl tgt b))
