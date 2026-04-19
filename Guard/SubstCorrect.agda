{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.SubstCorrect where

open import Guard.Base
open import Guard.Term

------------------------------------------------------------------------
-- natCodeEq: treeEq on natCodes agrees with natEq

natCodeEq : (n m : Nat) -> Eq (treeEq (natCode n) (natCode m)) (natEq n m)
natCodeEq zero    zero    = refl
natCodeEq zero    (suc m) = refl
natCodeEq (suc n) zero    = refl
natCodeEq (suc n) (suc m) = natCodeEq n m

------------------------------------------------------------------------
-- boolCaseCode: code distributes over boolCase for the var case

boolCaseCode : (b : Bool) (r : Term) (n : Nat) ->
  Eq (boolCase b (code r) (nd tagVar (natCode n)))
     (code (boolCase b r (var n)))
boolCaseCode true  r n = refl
boolCaseCode false r n = refl

------------------------------------------------------------------------
-- codedSubstNd: when left child is NOT tagVar, codedSubst recurses

codedSubstNd : (repl tgt a b : Tree) -> Eq (treeEq a tagVar) false ->
  Eq (codedSubst repl tgt (nd a b))
     (nd (codedSubst repl tgt a) (codedSubst repl tgt b))
codedSubstNd repl tgt a b pf =
  eqSubst (\v -> Eq (boolCase v (boolCase (treeEq b tgt) repl (nd a b))
                                 (nd (codedSubst repl tgt a) (codedSubst repl tgt b)))
                     (nd (codedSubst repl tgt a) (codedSubst repl tgt b)))
           (eqSym pf) refl

------------------------------------------------------------------------
-- codedSubstVar: the variable case

codedSubstVar : (repl tgt : Tree) (payload : Tree) ->
  Eq (codedSubst repl tgt (nd tagVar payload))
     (boolCase (treeEq payload tgt) repl (nd tagVar payload))
codedSubstVar repl tgt payload = refl

------------------------------------------------------------------------
-- codeF1NotVar / codeF2NotVar: functor codes never have tagVar as left child

codeF1NotVar : (f : Fun1) -> Eq (treeEq (codeF1 f) tagVar) false
codeF1NotVar I             = refl
codeF1NotVar Fst           = refl
codeF1NotVar Snd           = refl
codeF1NotVar (Comp f g)    = refl
codeF1NotVar (Comp2 h f g) = refl
codeF1NotVar (Rec z s)     = refl
codeF1NotVar (KT t)        = refl

codeF2NotVar : (g : Fun2) -> Eq (treeEq (codeF2 g) tagVar) false
codeF2NotVar Pair          = refl
codeF2NotVar Const         = refl
codeF2NotVar (Lift f)      = refl
codeF2NotVar (Post f h)    = refl
codeF2NotVar (Fan h1 h2 h) = refl
codeF2NotVar IfLf          = refl
codeF2NotVar TreeEq        = refl
codeF2NotVar (RecP s)      = refl

------------------------------------------------------------------------
-- codeNotVar: term codes never equal tagVar (including var!)
-- code(t) has form nd tag payload where tag != tagVar as a TREE.

codeNotVar : (t : Term) -> Eq (treeEq (code t) tagVar) false
codeNotVar O           = refl
codeNotVar (var n)     = refl
codeNotVar (ap1 f t)   = refl
codeNotVar (ap2 g a b) = refl

------------------------------------------------------------------------
-- Tag extractors for codeF1/codeF2

f1t : Fun1 -> Tree
f1t f = leftT (codeF1 f)

f2t : Fun2 -> Tree
f2t g = leftT (codeF2 g)

------------------------------------------------------------------------
-- Main theorem: codedSubst correctness (mutual induction)

csCorrect   : (r : Term) (x : Nat) (t : Term) ->
              Eq (codedSubst (code r) (natCode x) (code t)) (code (subst x r t))
csF1Correct : (r : Term) (x : Nat) (f : Fun1) ->
              Eq (codedSubst (code r) (natCode x) (codeF1 f)) (codeF1 (substF1 x r f))
csF2Correct : (r : Term) (x : Nat) (g : Fun2) ->
              Eq (codedSubst (code r) (natCode x) (codeF2 g)) (codeF2 (substF2 x r g))

-- O case: definitional
csCorrect r x O = refl

-- var case: needs natCodeEq
csCorrect r x (var n) =
  eqTrans (eqCong (\b -> boolCase b (code r) (nd tagVar (natCode n))) (natCodeEq n x))
          (boolCaseCode (natEq n x) r n)

-- ap1 case
csCorrect r x (ap1 f t) =
  eqTrans (codedSubstNd (code r) (natCode x) tagAp1 (nd (codeF1 f) (code t)) refl)
  (eqTrans (eqCong (\inner -> nd tagAp1 inner)
    (eqTrans (codedSubstNd (code r) (natCode x) (codeF1 f) (code t) (codeF1NotVar f))
             (eqCong2 nd (csF1Correct r x f) (csCorrect r x t))))
  refl)

-- ap2 case
csCorrect r x (ap2 g t1 t2) =
  eqTrans (codedSubstNd (code r) (natCode x) tagAp2 (nd (codeF2 g) (nd (code t1) (code t2))) refl)
  (eqTrans (eqCong (\inner -> nd tagAp2 inner)
    (eqTrans (codedSubstNd (code r) (natCode x) (codeF2 g) (nd (code t1) (code t2)) (codeF2NotVar g))
             (eqCong2 nd (csF2Correct r x g)
               (eqTrans (codedSubstNd (code r) (natCode x) (code t1) (code t2) (codeNotVar t1))
                        (eqCong2 nd (csCorrect r x t1) (csCorrect r x t2))))))
  refl)

-- Fun1 constant cases
csF1Correct r x I   = refl
csF1Correct r x Fst = refl
csF1Correct r x Snd = refl

-- Fun1 Comp
csF1Correct r x (Comp f g) =
  let tag = f1t (Comp I I) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (nd (codeF1 f) (codeF1 g)) refl)
  (eqCong (\p -> nd tag p)
    (eqTrans (codedSubstNd (code r) (natCode x) (codeF1 f) (codeF1 g) (codeF1NotVar f))
             (eqCong2 nd (csF1Correct r x f) (csF1Correct r x g))))

-- Fun1 Comp2
csF1Correct r x (Comp2 h f g) =
  let tag = f1t (Comp2 Pair I I) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (nd (codeF2 h) (nd (codeF1 f) (codeF1 g))) refl)
  (eqCong (\p -> nd tag p)
    (eqTrans (codedSubstNd (code r) (natCode x) (codeF2 h) (nd (codeF1 f) (codeF1 g)) (codeF2NotVar h))
             (eqCong2 nd (csF2Correct r x h)
               (eqTrans (codedSubstNd (code r) (natCode x) (codeF1 f) (codeF1 g) (codeF1NotVar f))
                        (eqCong2 nd (csF1Correct r x f) (csF1Correct r x g))))))

-- Fun1 KT
csF1Correct r x (KT t) =
  let tag = f1t (KT O) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (code t) refl)
  (eqCong (nd tag) (csCorrect r x t))

-- Fun1 Rec
csF1Correct r x (Rec z s) =
  let tag = f1t (Rec O Pair) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (nd (code z) (codeF2 s)) refl)
  (eqCong (\p -> nd tag p)
    (eqTrans (codedSubstNd (code r) (natCode x) (code z) (codeF2 s) (codeNotVar z))
             (eqCong2 nd (csCorrect r x z) (csF2Correct r x s))))

-- Fun2 constant cases
csF2Correct r x Pair   = refl
csF2Correct r x Const  = refl
csF2Correct r x IfLf   = refl
csF2Correct r x TreeEq = refl

-- Fun2 RecP s: tag at offset 33, one Fun2 child.
csF2Correct r x (RecP s) =
  let tag = f2t (RecP Pair) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (codeF2 s) refl)
  (eqCong (nd tag) (csF2Correct r x s))

-- Fun2 Lift
csF2Correct r x (Lift f) =
  let tag = f2t (Lift I) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (codeF1 f) refl)
  (eqCong (nd tag) (csF1Correct r x f))

-- Fun2 Post
csF2Correct r x (Post f h) =
  let tag = f2t (Post I Pair) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (nd (codeF1 f) (codeF2 h)) refl)
  (eqCong (\p -> nd tag p)
    (eqTrans (codedSubstNd (code r) (natCode x) (codeF1 f) (codeF2 h) (codeF1NotVar f))
             (eqCong2 nd (csF1Correct r x f) (csF2Correct r x h))))

-- Fun2 Fan
csF2Correct r x (Fan h1 h2 h) =
  let tag = f2t (Fan Pair Pair Pair) in
  eqTrans (codedSubstNd (code r) (natCode x) tag (nd (codeF2 h1) (nd (codeF2 h2) (codeF2 h))) refl)
  (eqCong (\p -> nd tag p)
    (eqTrans (codedSubstNd (code r) (natCode x) (codeF2 h1) (nd (codeF2 h2) (codeF2 h)) (codeF2NotVar h1))
             (eqCong2 nd (csF2Correct r x h1)
               (eqTrans (codedSubstNd (code r) (natCode x) (codeF2 h2) (codeF2 h) (codeF2NotVar h2))
                        (eqCong2 nd (csF2Correct r x h2) (csF2Correct r x h))))))
