{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SubstClosure -- structural substitution-closure lemmas.
--
-- These lemmas establish that subst / substF1 / substF2 are identity on
-- Terms / Fun1's / Fun2's that contain no free variables.  They are
-- needed to discharge the substitutional residues that arise when
-- ruleInst-ing universally quantified Theorem 12 statements at
-- specific terms, particularly for cases like  treeRec  whose encoded
-- D-functor mentions  reify (codeF1 f) ,  reify (codeF2 s) , and  cor .
--
-- Three lemmas:
--   * subst_reify         : subst k r (reify t) = reify t .
--   * substF1_KT_of_reify : substF1 k r (KT (reify t)) = KT (reify t) .
--   * cor_closed          : substF1 k r cor = cor .
--
-- All by induction on the appropriate structure.  No postulates, no holes.

module BRA2.SubstClosure where

open import BRA2.Base
open import BRA2.Term

------------------------------------------------------------------------
-- Lemma 1: reify of any Tree is a closed Term, so subst leaves it.

subst_reify : (k : Nat) (r : Term) (t : Term) -> IsValue t ->
  Eq (subst k r t) t
subst_reify k r .O                 valO                = refl
subst_reify k r (ap2 Pair a b)    (valNd .a .b va vb)  =
  eqTrans (eqCong (\ A -> ap2 Pair A (subst k r b))
                   (subst_reify k r a va))
          (eqCong (\ B -> ap2 Pair a B)
                   (subst_reify k r b vb))

------------------------------------------------------------------------
-- Lemma 2: KT (reify t) is a closed Fun1, so substF1 leaves it.
--
-- Pattern-match goes through KT's definition.  At reify t , KT pattern-
-- matches on  reify t 's outermost shape:
--   reify lf       = O          --> KT O = Z
--   reify (nd a b) = ap2 Pair _ _  --> KT (Pair a' b') = Comp2 Pair (KT a') (KT b')
-- Recursive case folds via substF1 on the Comp2 and IH on a, b.

substF1_KT_of_reify : (k : Nat) (r : Term) (t : Term) -> IsValue t ->
  Eq (substF1 k r (KT t)) (KT t)
substF1_KT_of_reify k r .O                 valO                = refl
substF1_KT_of_reify k r (ap2 Pair a b)    (valNd .a .b va vb)  =
  eqTrans (eqCong (\ A -> Comp2 Pair A (substF1 k r (KT b)))
                   (substF1_KT_of_reify k r a va))
          (eqCong (\ B -> Comp2 Pair (KT a) B)
                   (substF1_KT_of_reify k r b vb))

------------------------------------------------------------------------
-- Lemma 4 / 5: Fun1 / Fun2 grammars contain no  var  / Term  arguments,
-- so substF1 / substF2 leave any Fun1 / Fun2 untouched.  Mutual
-- structural recursion on Fun1 / Fun2.

Fun1_closed : (k : Nat) (r : Term) (f : Fun1) ->
  Eq (substF1 k r f) f
Fun2_closed : (k : Nat) (r : Term) (g : Fun2) ->
  Eq (substF2 k r g) g

Fun1_closed k r I             = refl
Fun1_closed k r Fst           = refl
Fun1_closed k r Snd           = refl
Fun1_closed k r (Comp f g)    =
  eqTrans (eqCong (\ A -> Comp A (substF1 k r g)) (Fun1_closed k r f))
          (eqCong (\ B -> Comp f B) (Fun1_closed k r g))
Fun1_closed k r (Comp2 h f g) =
  eqTrans (eqCong (\ A -> Comp2 A (substF1 k r f) (substF1 k r g))
                   (Fun2_closed k r h))
          (eqTrans (eqCong (\ B -> Comp2 h B (substF1 k r g))
                            (Fun1_closed k r f))
                   (eqCong (\ C -> Comp2 h f C) (Fun1_closed k r g)))
Fun1_closed k r Z             = refl

Fun2_closed k r Pair          = refl
Fun2_closed k r Const         = refl
Fun2_closed k r (Lift f)      = eqCong Lift (Fun1_closed k r f)
Fun2_closed k r (Post f h)    =
  eqTrans (eqCong (\ A -> Post A (substF2 k r h)) (Fun1_closed k r f))
          (eqCong (\ B -> Post f B) (Fun2_closed k r h))
Fun2_closed k r (Fan h1 h2 h) =
  eqTrans (eqCong (\ A -> Fan A (substF2 k r h2) (substF2 k r h))
                   (Fun2_closed k r h1))
          (eqTrans (eqCong (\ B -> Fan h1 B (substF2 k r h))
                            (Fun2_closed k r h2))
                   (eqCong (\ C -> Fan h1 h2 C) (Fun2_closed k r h)))
Fun2_closed k r IfLf          = refl
Fun2_closed k r TreeEq        = refl
Fun2_closed k r (treeRec f s) =
  eqTrans (eqCong (\ A -> treeRec A (substF2 k r s)) (Fun1_closed k r f))
          (eqCong (\ B -> treeRec f B) (Fun2_closed k r s))
