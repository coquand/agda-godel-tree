{-# OPTIONS --safe --without-K --exact-split #-}

module BRA2.Term where

open import BRA2.Base

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

data Fun2 where
  Pair    : Fun2
  Const   : Fun2
  Lift    : Fun1 -> Fun2
  Post    : Fun1 -> Fun2 -> Fun2
  Fan     : Fun2 -> Fun2 -> Fun2 -> Fun2
  IfLf    : Fun2
  TreeEq  : Fun2
  treeRec : Fun1 -> Fun2 -> Fun2

data Term where
  O   : Term
  var : Nat -> Term
  ap1 : Fun1 -> Term -> Term
  ap2 : Fun2 -> Term -> Term -> Term

------------------------------------------------------------------------
-- Tree = Term : type alias collapsing the old Tree datatype.

Tree : Set
Tree = Term

lf : Term
lf = O

nd : Term -> Term -> Term
nd a b = ap2 Pair a b

------------------------------------------------------------------------
-- IsValue : value-shape predicate.  Built only from O and ap2 Pair.

data IsValue : Term -> Set where
  valO  : IsValue O
  valNd : (a b : Term) -> IsValue a -> IsValue b -> IsValue (ap2 Pair a b)

------------------------------------------------------------------------
-- Tree-style helpers, Term-typed, with safe defaults on non-value shapes.

leftT : Term -> Term
leftT O           = O
leftT (var _)     = O
leftT (ap1 _ _)   = O
leftT (ap2 _ a _) = a

rightT : Term -> Term
rightT O           = O
rightT (var _)     = O
rightT (ap1 _ _)   = O
rightT (ap2 _ _ b) = b

treeEq : Term -> Term -> Bool
treeEq O                            O                            = true
treeEq O                            (var _)                      = false
treeEq O                            (ap1 _ _)                    = false
treeEq O                            (ap2 _ _ _)                  = false
treeEq (var _)                      _                            = false
treeEq (ap1 _ _)                    _                            = false
treeEq (ap2 _ _ _)                  O                            = false
treeEq (ap2 _ _ _)                  (var _)                      = false
treeEq (ap2 _ _ _)                  (ap1 _ _)                    = false
treeEq (ap2 Pair a b)               (ap2 Pair c d)               = boolAnd (treeEq a c) (treeEq b d)
treeEq (ap2 Pair _ _)               (ap2 Const _ _)              = false
treeEq (ap2 Pair _ _)               (ap2 (Lift _) _ _)           = false
treeEq (ap2 Pair _ _)               (ap2 (Post _ _) _ _)         = false
treeEq (ap2 Pair _ _)               (ap2 (Fan _ _ _) _ _)        = false
treeEq (ap2 Pair _ _)               (ap2 IfLf _ _)               = false
treeEq (ap2 Pair _ _)               (ap2 TreeEq _ _)             = false
treeEq (ap2 Pair _ _)               (ap2 (treeRec _ _) _ _)      = false
treeEq (ap2 Const _ _)              (ap2 _ _ _)                  = false
treeEq (ap2 (Lift _) _ _)           (ap2 _ _ _)                  = false
treeEq (ap2 (Post _ _) _ _)         (ap2 _ _ _)                  = false
treeEq (ap2 (Fan _ _ _) _ _)        (ap2 _ _ _)                  = false
treeEq (ap2 IfLf _ _)               (ap2 _ _ _)                  = false
treeEq (ap2 TreeEq _ _)             (ap2 _ _ _)                  = false
treeEq (ap2 (treeRec _ _) _ _)      (ap2 _ _ _)                  = false

treeRecMeta : {A : Set} -> A -> (Term -> Term -> A -> A -> A) -> Term -> A
treeRecMeta z s O                       = z
treeRecMeta z s (var _)                 = z
treeRecMeta z s (ap1 _ _)               = z
treeRecMeta z s (ap2 Pair a b)          = s a b (treeRecMeta z s a) (treeRecMeta z s b)
treeRecMeta z s (ap2 Const _ _)         = z
treeRecMeta z s (ap2 (Lift _) _ _)      = z
treeRecMeta z s (ap2 (Post _ _) _ _)    = z
treeRecMeta z s (ap2 (Fan _ _ _) _ _)   = z
treeRecMeta z s (ap2 IfLf _ _)          = z
treeRecMeta z s (ap2 TreeEq _ _)        = z
treeRecMeta z s (ap2 (treeRec _ _) _ _) = z

natCode : Nat -> Term
natCode zero    = O
natCode (suc n) = ap2 Pair O (natCode n)

------------------------------------------------------------------------
-- RecP: legacy parameterised tree-recursor.  Defined in terms of
-- treeRec (since Z p = O makes the leaf cases match exactly).

RecP : Fun2 -> Fun2
RecP s = treeRec Z s

------------------------------------------------------------------------
-- Rec: legacy 1-ary tree-recursor with leaf payload z = O.

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
-- reify : Tree -> Term.  After the Tree=Term collapse, this is identity.

reify : Term -> Term
reify t = t

------------------------------------------------------------------------
-- Tag constants

tagVar : Term
tagVar = nd (nd (nd lf lf) lf) lf

tagAp1 : Term
tagAp1 = nd lf (nd lf lf)

tagAp2 : Term
tagAp2 = nd lf (nd lf (nd lf lf))

------------------------------------------------------------------------
-- Coding functions (mutual)

codeF1 : Fun1 -> Term
codeF2 : Fun2 -> Term
code   : Term -> Term

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

mkAp1 : Term -> Term -> Term
mkAp1 fCode tCode = nd tagAp1 (nd fCode tCode)

mkAp2 : Term -> Term -> Term -> Term
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
-- Coded substitution (on Term, value-shaped at variable nodes).

codedSubst : Term -> Term -> Term -> Term
codedSubst repl varCode O                       = O
codedSubst repl varCode (var n)                 = var n
codedSubst repl varCode (ap1 f t)               = ap1 f t
codedSubst repl varCode (ap2 Pair a b)          =
  boolCase (treeEq varCode (ap2 Pair a b))
    repl
    (ap2 Pair (codedSubst repl varCode a) (codedSubst repl varCode b))
codedSubst repl varCode (ap2 Const a b)         = ap2 Const a b
codedSubst repl varCode (ap2 (Lift f) a b)      = ap2 (Lift f) a b
codedSubst repl varCode (ap2 (Post f h) a b)    = ap2 (Post f h) a b
codedSubst repl varCode (ap2 (Fan h1 h2 h) a b) = ap2 (Fan h1 h2 h) a b
codedSubst repl varCode (ap2 IfLf a b)          = ap2 IfLf a b
codedSubst repl varCode (ap2 TreeEq a b)        = ap2 TreeEq a b
codedSubst repl varCode (ap2 (treeRec f s) a b) = ap2 (treeRec f s) a b

------------------------------------------------------------------------
-- IsValue helpers.

natCode_isValue : (n : Nat) -> IsValue (natCode n)
natCode_isValue zero    = valO
natCode_isValue (suc n) = valNd O (natCode n) valO (natCode_isValue n)

tagVar_isValue : IsValue tagVar
tagVar_isValue =
  valNd (nd (nd lf lf) lf) lf
        (valNd (nd lf lf) lf (valNd lf lf valO valO) valO)
        valO

tagAp1_isValue : IsValue tagAp1
tagAp1_isValue = valNd lf (nd lf lf) valO (valNd lf lf valO valO)

tagAp2_isValue : IsValue tagAp2
tagAp2_isValue =
  valNd lf (nd lf (nd lf lf)) valO
        (valNd lf (nd lf lf) valO (valNd lf lf valO valO))

codeF1_isValue : (f : Fun1) -> IsValue (codeF1 f)
codeF2_isValue : (g : Fun2) -> IsValue (codeF2 g)

codeF1_isValue I             = valNd _ lf (natCode_isValue _) valO
codeF1_isValue Fst           = valNd _ lf (natCode_isValue _) valO
codeF1_isValue Snd           = valNd _ lf (natCode_isValue _) valO
codeF1_isValue (Comp f g)    =
  valNd _ _ (natCode_isValue _)
        (valNd _ _ (codeF1_isValue f) (codeF1_isValue g))
codeF1_isValue (Comp2 h f g) =
  valNd _ _ (natCode_isValue _)
        (valNd _ _ (codeF2_isValue h)
               (valNd _ _ (codeF1_isValue f) (codeF1_isValue g)))
codeF1_isValue Z             = valNd _ lf (natCode_isValue _) valO

codeF2_isValue Pair          = valNd _ lf (natCode_isValue _) valO
codeF2_isValue Const         = valNd _ lf (natCode_isValue _) valO
codeF2_isValue (Lift f)      =
  valNd _ _ (natCode_isValue _) (codeF1_isValue f)
codeF2_isValue (Post f h)    =
  valNd _ _ (natCode_isValue _)
        (valNd _ _ (codeF1_isValue f) (codeF2_isValue h))
codeF2_isValue (Fan h1 h2 h) =
  valNd _ _ (natCode_isValue _)
        (valNd _ _ (codeF2_isValue h1)
               (valNd _ _ (codeF2_isValue h2) (codeF2_isValue h)))
codeF2_isValue IfLf          = valNd _ lf (natCode_isValue _) valO
codeF2_isValue TreeEq        = valNd _ lf (natCode_isValue _) valO
codeF2_isValue (treeRec f s) =
  valNd _ _ (natCode_isValue _)
        (valNd _ _ (codeF1_isValue f) (codeF2_isValue s))

code_isValue : (t : Term) -> IsValue (code t)
code_isValue O           = valO
code_isValue (var n)     =
  valNd tagVar (natCode n) tagVar_isValue (natCode_isValue n)
code_isValue (ap1 f t)   =
  valNd tagAp1 _ tagAp1_isValue
        (valNd _ _ (codeF1_isValue f) (code_isValue t))
code_isValue (ap2 g a b) =
  valNd tagAp2 _ tagAp2_isValue
        (valNd _ _ (codeF2_isValue g)
               (valNd _ _ (code_isValue a) (code_isValue b)))

------------------------------------------------------------------------
-- leftT / rightT preserve value-shape.

leftT_isValue : (t : Term) -> IsValue t -> IsValue (leftT t)
leftT_isValue .O                 valO                = valO
leftT_isValue (ap2 Pair a b)    (valNd .a .b va vb)  = va

rightT_isValue : (t : Term) -> IsValue t -> IsValue (rightT t)
rightT_isValue .O                 valO                = valO
rightT_isValue (ap2 Pair a b)    (valNd .a .b va vb)  = vb
