{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DerivTBounded -- bounded threshold derivations.
--
-- DerivTBounded r l P  =  derivations of  P  in BRA2.DerivT whose
--   - induction rank      is <= r , and
--   - mp-chain depth      is <= l .
--
-- Bookkeeping (the simplest design that goes in first; refine in
-- BoundedReduction.agda if Step 3 demands sharper arithmetic):
--   * Atomic axioms / propositional axioms / ruleInst preserve both
--     ranks: they are leaves of the derivation tree, and increasing
--     ranks at leaves loses information.
--   * mp combines its premises with  max  on r , and increments l by 1.
--   * indBT / indBT2 combine their premises with  max  on l , and
--     increment r by 1.
--
-- Open consistency (ConBounded) :
--   ConBounded r l = DerivTBounded r l bot -> Empty .
--
-- The forgetful embedding  forgetB : DerivTBounded r l P -> DerivT P
-- drops the rank/level indices and lifts each constructor to its
-- DerivT counterpart.
--
-- This file is the Step-2 deliverable of BRA2/BOUNDED-REFLECTION-PLAN.md.

module BRA2.DerivTBounded where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.NatMax public using (natMax)
open import BRA2.WellFormedIndBT using (WellFormedIndBT)
import BRA2.DerivT as T

------------------------------------------------------------------------
-- DerivTBounded : indexed by rank r and level l.

data DerivTBounded : Nat -> Nat -> Formula -> Set where

  ------------------------------------------------------------------
  -- Computation axioms (rank 0, level 0).

  axIB      : (r l : Nat) (t : Term) ->
               DerivTBounded r l (atomic (eqn (ap1 I t) t))
  axFstB    : (r l : Nat) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
  axSndB    : (r l : Nat) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
  axFstLfB  : (r l : Nat) ->
               DerivTBounded r l (atomic (eqn (ap1 Fst O) O))
  axSndLfB  : (r l : Nat) ->
               DerivTBounded r l (atomic (eqn (ap1 Snd O) O))
  axConstB  : (r l : Nat) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 Const a b) a))
  axCompB   : (r l : Nat) (f g : Fun1) (t : Term) ->
               DerivTBounded r l (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
  axComp2B  : (r l : Nat) (h : Fun2) (f g : Fun1) (t : Term) ->
               DerivTBounded r l (atomic (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))
  axLiftB   : (r l : Nat) (f : Fun1) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
  axPostB   : (r l : Nat) (f : Fun1) (h : Fun2) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))
  axFanB    : (r l : Nat) (h1 h2 h : Fun2) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                                              (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
  axZB      : (r l : Nat) (x : Term) ->
               DerivTBounded r l (atomic (eqn (ap1 Z x) O))

  axTreeRecLfB : (r l : Nat) (f : Fun1) (s : Fun2) (p : Term) ->
                  DerivTBounded r l (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))
  axTreeRecNdB : (r l : Nat) (f : Fun1) (s : Fun2) (p a b : Term) ->
                  DerivTBounded r l (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a b))
                                                 (ap2 s (ap2 Pair p (ap2 Pair a b))
                                                        (ap2 Pair (ap2 (treeRec f s) p a)
                                                                  (ap2 (treeRec f s) p b)))))

  axIfLfLB  : (r l : Nat) (a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
  axIfLfNB  : (r l : Nat) (x y a b : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))
  axIfLfLLB : (r l : Nat) ->
               DerivTBounded r l (atomic (eqn (ap2 IfLf O O) O))
  axIfLfNLB : (r l : Nat) (x y : Term) ->
               DerivTBounded r l (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))

  axTreeEqLLB : (r l : Nat) ->
                 DerivTBounded r l (atomic (eqn (ap2 TreeEq O O) O))
  axTreeEqLNB : (r l : Nat) (a b : Term) ->
                 DerivTBounded r l (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
  axTreeEqNLB : (r l : Nat) (a b : Term) ->
                 DerivTBounded r l (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
  axTreeEqNNB : (r l : Nat) (a1 a2 b1 b2 : Term) ->
                 DerivTBounded r l (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                                                (ap2 IfLf (ap2 TreeEq a1 b1)
                                                          (ap2 Pair (ap2 TreeEq a2 b2)
                                                                    (ap2 Pair O O)))))

  axGoodsteinB : (r l : Nat) (a b : Term) ->
                  DerivTBounded r l (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                                                 (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

  ------------------------------------------------------------------
  -- Structural rules on atomic equations.
  --
  -- Symmetry/transitivity/congruence are unary or binary combiners
  -- on derivations.  We let them preserve the indices of the inputs
  -- (taking max on binary cases).  This is the simplest sound choice;
  -- BoundedReduction.agda may revisit if the reduction needs sharper
  -- accounting on these.

  axReflB   : (r l : Nat) (t : Term) -> DerivTBounded r l (atomic (eqn t t))
  ruleSymB  : {r l : Nat} {t u : Term} ->
               DerivTBounded r l (atomic (eqn t u)) ->
               DerivTBounded r l (atomic (eqn u t))
  ruleTransB : {r1 l1 r2 l2 : Nat} {t u v : Term} ->
                DerivTBounded r1 l1 (atomic (eqn t u)) ->
                DerivTBounded r2 l2 (atomic (eqn u v)) ->
                DerivTBounded (natMax r1 r2) (natMax l1 l2) (atomic (eqn t v))
  cong1B    : {r l : Nat} (f : Fun1) {t u : Term} ->
               DerivTBounded r l (atomic (eqn t u)) ->
               DerivTBounded r l (atomic (eqn (ap1 f t) (ap1 f u)))
  congLB    : {r l : Nat} (g : Fun2) {t u : Term} (x : Term) ->
               DerivTBounded r l (atomic (eqn t u)) ->
               DerivTBounded r l (atomic (eqn (ap2 g t x) (ap2 g u x)))
  congRB    : {r l : Nat} (g : Fun2) (x : Term) {t u : Term} ->
               DerivTBounded r l (atomic (eqn t u)) ->
               DerivTBounded r l (atomic (eqn (ap2 g x t) (ap2 g x u)))

  axEqTransB : (r l : Nat) (a b c : Term) ->
                DerivTBounded r l ((atomic (eqn a b))
                                   imp ((atomic (eqn a c))
                                         imp (atomic (eqn b c))))
  axEqCong1B : (r l : Nat) (f : Fun1) (a b : Term) ->
                DerivTBounded r l ((atomic (eqn a b))
                                   imp (atomic (eqn (ap1 f a) (ap1 f b))))
  axEqCongLB : (r l : Nat) (g : Fun2) (a b c : Term) ->
                DerivTBounded r l ((atomic (eqn a b))
                                   imp (atomic (eqn (ap2 g a c) (ap2 g b c))))
  axEqCongRB : (r l : Nat) (g : Fun2) (a b c : Term) ->
                DerivTBounded r l ((atomic (eqn a b))
                                   imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

  ------------------------------------------------------------------
  -- Propositional axioms (Guard Ax 11, 12, 13).

  axKB      : (r l : Nat) (P Q : Formula) ->
               DerivTBounded r l (P imp (Q imp P))
  axSB      : (r l : Nat) (P Q R : Formula) ->
               DerivTBounded r l ((P imp (Q imp R))
                                  imp ((P imp Q) imp (P imp R)))
  axNegB    : (r l : Nat) (P Q : Formula) ->
               DerivTBounded r l (((not P) imp (not Q)) imp (Q imp P))

  ------------------------------------------------------------------
  -- Rules of inference.
  --
  -- mp combines on max(r), increments level.

  mpB       : {r1 l1 r2 l2 : Nat} {P Q : Formula} ->
               DerivTBounded r1 l1 (P imp Q) ->
               DerivTBounded r2 l2 P ->
               DerivTBounded (natMax r1 r2) (suc (natMax l1 l2)) Q

  ruleInstB : {r l : Nat} (x : Nat) (t : Term) {P : Formula} ->
               DerivTBounded r l P ->
               DerivTBounded r l (substF x t P)

  ------------------------------------------------------------------
  -- Atomic-only binary-tree induction.  Each indBT/indBT2 combines
  -- premises on max(l) and increments rank by 1.

  indBTB    : {r1 l1 r2 l2 : Nat}
               (e : Equation) (v1 v2 : Nat) ->
               WellFormedIndBT e v1 v2 ->
               DerivTBounded r1 l1 (atomic (substEq zero O e)) ->
               DerivTBounded r2 l2
                 ((atomic (substEq zero (var v1) e)) imp
                  ((atomic (substEq zero (var v2) e)) imp
                   (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
               DerivTBounded (suc (natMax r1 r2)) (natMax l1 l2) (atomic e)

  indBT2B   : {r1 l1 r2 l2 r3 l3 r4 l4 : Nat}
               (e : Equation) (v1 v2 v3 v4 : Nat) ->
               DerivTBounded r1 l1
                 (atomic (substEq (suc zero) O (substEq zero O e))) ->
               DerivTBounded r2 l2
                 ((atomic (substEq (suc zero) (var v3) (substEq zero O e))) imp
                  ((atomic (substEq (suc zero) (var v4) (substEq zero O e))) imp
                   (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                                (substEq zero O e))))) ->
               DerivTBounded r3 l3
                 ((atomic (substEq (suc zero) O (substEq zero (var v1) e))) imp
                  ((atomic (substEq (suc zero) O (substEq zero (var v2) e))) imp
                   (atomic (substEq (suc zero) O
                                                (substEq zero (ap2 Pair (var v1) (var v2)) e))))) ->
               DerivTBounded r4 l4
                 ((atomic (substEq (suc zero) (var v3) (substEq zero (var v1) e))) imp
                  ((atomic (substEq (suc zero) (var v4) (substEq zero (var v2) e))) imp
                   (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                                (substEq zero (ap2 Pair (var v1) (var v2)) e))))) ->
               DerivTBounded
                 (suc (natMax (natMax r1 r2) (natMax r3 r4)))
                 (natMax (natMax l1 l2) (natMax l3 l4))
                 (atomic e)

------------------------------------------------------------------------
-- forgetB : DerivTBounded r l P -> DerivT P
--
-- Drops the rank/level indices.  Structural recursion: each
-- constructor maps to its same-named DerivT counterpart.

forgetB : {r l : Nat} {P : Formula} -> DerivTBounded r l P -> T.DerivT P
forgetB (axIB _ _ t)              = T.axI t
forgetB (axFstB _ _ a b)          = T.axFst a b
forgetB (axSndB _ _ a b)          = T.axSnd a b
forgetB (axFstLfB _ _)            = T.axFstLf
forgetB (axSndLfB _ _)            = T.axSndLf
forgetB (axConstB _ _ a b)        = T.axConst a b
forgetB (axCompB _ _ f g t)       = T.axComp f g t
forgetB (axComp2B _ _ h f g t)    = T.axComp2 h f g t
forgetB (axLiftB _ _ f a b)       = T.axLift f a b
forgetB (axPostB _ _ f h a b)     = T.axPost f h a b
forgetB (axFanB _ _ h1 h2 h a b)  = T.axFan h1 h2 h a b
forgetB (axZB _ _ x)              = T.axZ x
forgetB (axTreeRecLfB _ _ f s p)         = T.axTreeRecLf f s p
forgetB (axTreeRecNdB _ _ f s p a b)     = T.axTreeRecNd f s p a b
forgetB (axIfLfLB _ _ a b)        = T.axIfLfL a b
forgetB (axIfLfNB _ _ x y a b)    = T.axIfLfN x y a b
forgetB (axIfLfLLB _ _)           = T.axIfLfLL
forgetB (axIfLfNLB _ _ x y)       = T.axIfLfNL x y
forgetB (axTreeEqLLB _ _)         = T.axTreeEqLL
forgetB (axTreeEqLNB _ _ a b)     = T.axTreeEqLN a b
forgetB (axTreeEqNLB _ _ a b)     = T.axTreeEqNL a b
forgetB (axTreeEqNNB _ _ a1 a2 b1 b2) = T.axTreeEqNN a1 a2 b1 b2
forgetB (axGoodsteinB _ _ a b)    = T.axGoodstein a b
forgetB (axReflB _ _ t)           = T.axRefl t
forgetB (ruleSymB d)              = T.ruleSym (forgetB d)
forgetB (ruleTransB d1 d2)        = T.ruleTrans (forgetB d1) (forgetB d2)
forgetB (cong1B f d)              = T.cong1 f (forgetB d)
forgetB (congLB g x d)            = T.congL g x (forgetB d)
forgetB (congRB g x d)            = T.congR g x (forgetB d)
forgetB (axEqTransB _ _ a b c)    = T.axEqTrans a b c
forgetB (axEqCong1B _ _ f a b)    = T.axEqCong1 f a b
forgetB (axEqCongLB _ _ g a b c)  = T.axEqCongL g a b c
forgetB (axEqCongRB _ _ g a b c)  = T.axEqCongR g a b c
forgetB (axKB _ _ P Q)            = T.axK P Q
forgetB (axSB _ _ P Q R)          = T.axS P Q R
forgetB (axNegB _ _ P Q)          = T.axNeg P Q
forgetB (mpB d1 d2)               = T.mp (forgetB d1) (forgetB d2)
forgetB (ruleInstB x t d)         = T.ruleInst x t (forgetB d)
forgetB (indBTB e v1 v2 _ base step) =
  T.indBT e v1 v2 (forgetB base) (forgetB step)
forgetB (indBT2B e v1 v2 v3 v4 baseLL baseLN baseNL basePP) =
  T.indBT2 e v1 v2 v3 v4
    (forgetB baseLL) (forgetB baseLN) (forgetB baseNL) (forgetB basePP)

------------------------------------------------------------------------
-- Bounded consistency : no proof of bot at rank <= r and level <= l.

open import BRA2.DerivThreshold using (trueT ; falseT)

bot : Formula
bot = atomic (eqn trueT falseT)

ConBounded : (r l : Nat) -> Set
ConBounded r l = DerivTBounded r l bot -> Empty
