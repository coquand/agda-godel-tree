{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DerivT0 -- open fragment of the threshold derivation type.
--
-- DerivT0 mirrors BRA2.DerivT verbatim EXCEPT it omits the two
-- atomic-only binary-tree induction constructors  indBT  and  indBT2.
-- This is the "open" / "induction-free" sub-language of the threshold
-- system.
--
-- Open consistency is then  OpenCon0 = DerivT0 bot -> Empty.
--
-- The forgetful embedding  forget0 : DerivT0 P -> DerivT P  witnesses
-- that every open-fragment proof lifts to the full threshold system;
-- it is the obvious structural recursion (each constructor maps to the
-- same-named DerivT constructor).
--
-- This file is the Step-1 deliverable of BRA2/BOUNDED-REFLECTION-PLAN.md.

module BRA2.DerivT0 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT as T

------------------------------------------------------------------------
-- DerivT0 : open fragment of the threshold derivation relation.
--
-- All constructors of DerivT EXCEPT indBT and indBT2.

data DerivT0 : Formula -> Set where

  ------------------------------------------------------------------
  -- Computation axioms (defining equations of the primitive functors).

  axI      : (t : Term) -> DerivT0 (atomic (eqn (ap1 I t) t))
  axFst    : (a b : Term) -> DerivT0 (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
  axSnd    : (a b : Term) -> DerivT0 (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
  axFstLf  : DerivT0 (atomic (eqn (ap1 Fst O) O))
  axSndLf  : DerivT0 (atomic (eqn (ap1 Snd O) O))
  axConst  : (a b : Term) -> DerivT0 (atomic (eqn (ap2 Const a b) a))
  axComp   : (f g : Fun1) (t : Term) ->
             DerivT0 (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
  axComp2  : (h : Fun2) (f g : Fun1) (t : Term) ->
             DerivT0 (atomic (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))
  axLift   : (f : Fun1) (a b : Term) ->
             DerivT0 (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
  axPost   : (f : Fun1) (h : Fun2) (a b : Term) ->
             DerivT0 (atomic (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))
  axFan    : (h1 h2 h : Fun2) (a b : Term) ->
             DerivT0 (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                                  (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
  axZ      : (x : Term) -> DerivT0 (atomic (eqn (ap1 Z x) O))

  axTreeRecLf : (f : Fun1) (s : Fun2) (p : Term) ->
                DerivT0 (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))
  axTreeRecNd : (f : Fun1) (s : Fun2) (p a b : Term) ->
                DerivT0 (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a b))
                                     (ap2 s (ap2 Pair p (ap2 Pair a b))
                                            (ap2 Pair (ap2 (treeRec f s) p a)
                                                      (ap2 (treeRec f s) p b)))))

  axIfLfL  : (a b : Term) ->
             DerivT0 (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
  axIfLfN  : (x y a b : Term) ->
             DerivT0 (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))
  axIfLfLL : DerivT0 (atomic (eqn (ap2 IfLf O O) O))
  axIfLfNL : (x y : Term) ->
             DerivT0 (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))

  axTreeEqLL : DerivT0 (atomic (eqn (ap2 TreeEq O O) O))
  axTreeEqLN : (a b : Term) ->
               DerivT0 (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
  axTreeEqNL : (a b : Term) ->
               DerivT0 (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
  axTreeEqNN : (a1 a2 b1 b2 : Term) ->
               DerivT0 (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                                    (ap2 IfLf (ap2 TreeEq a1 b1)
                                              (ap2 Pair (ap2 TreeEq a2 b2)
                                                        (ap2 Pair O O)))))

  axGoodstein : (a b : Term) ->
                DerivT0 (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                                     (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

  ------------------------------------------------------------------
  -- Structural rules on atomic equations.

  axRefl     : (t : Term) -> DerivT0 (atomic (eqn t t))
  ruleSym    : {t u : Term} ->
               DerivT0 (atomic (eqn t u)) ->
               DerivT0 (atomic (eqn u t))
  ruleTrans  : {t u v : Term} ->
               DerivT0 (atomic (eqn t u)) ->
               DerivT0 (atomic (eqn u v)) ->
               DerivT0 (atomic (eqn t v))
  cong1      : (f : Fun1) {t u : Term} ->
               DerivT0 (atomic (eqn t u)) ->
               DerivT0 (atomic (eqn (ap1 f t) (ap1 f u)))
  congL      : (g : Fun2) {t u : Term} (x : Term) ->
               DerivT0 (atomic (eqn t u)) ->
               DerivT0 (atomic (eqn (ap2 g t x) (ap2 g u x)))
  congR      : (g : Fun2) (x : Term) {t u : Term} ->
               DerivT0 (atomic (eqn t u)) ->
               DerivT0 (atomic (eqn (ap2 g x t) (ap2 g x u)))

  axEqTrans  : (a b c : Term) ->
               DerivT0 ((atomic (eqn a b))
                        imp ((atomic (eqn a c))
                              imp (atomic (eqn b c))))
  axEqCong1  : (f : Fun1) (a b : Term) ->
               DerivT0 ((atomic (eqn a b))
                        imp (atomic (eqn (ap1 f a) (ap1 f b))))
  axEqCongL  : (g : Fun2) (a b c : Term) ->
               DerivT0 ((atomic (eqn a b))
                        imp (atomic (eqn (ap2 g a c) (ap2 g b c))))
  axEqCongR  : (g : Fun2) (a b c : Term) ->
               DerivT0 ((atomic (eqn a b))
                        imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

  ------------------------------------------------------------------
  -- Propositional axioms (Guard Ax 11, 12, 13).

  axK        : (P Q : Formula) ->
               DerivT0 (P imp (Q imp P))
  axS        : (P Q R : Formula) ->
               DerivT0 ((P imp (Q imp R))
                       imp ((P imp Q) imp (P imp R)))
  axNeg      : (P Q : Formula) ->
               DerivT0 (((not P) imp (not Q)) imp (Q imp P))

  ------------------------------------------------------------------
  -- Rules of inference.

  mp         : {P Q : Formula} ->
               DerivT0 (P imp Q) ->
               DerivT0 P ->
               DerivT0 Q

  ruleInst   : (x : Nat) (t : Term) {P : Formula} ->
               DerivT0 P ->
               DerivT0 (substF x t P)

  ------------------------------------------------------------------
  -- NO indBT, NO indBT2.  This is the open fragment.

------------------------------------------------------------------------
-- forget0 : DerivT0 P -> DerivT P
--
-- Soundness embedding from the open fragment into the full threshold
-- system.  Every constructor maps to its same-named DerivT counterpart.

forget0 : {P : Formula} -> DerivT0 P -> T.DerivT P
forget0 (axI t)              = T.axI t
forget0 (axFst a b)          = T.axFst a b
forget0 (axSnd a b)          = T.axSnd a b
forget0 axFstLf              = T.axFstLf
forget0 axSndLf              = T.axSndLf
forget0 (axConst a b)        = T.axConst a b
forget0 (axComp f g t)       = T.axComp f g t
forget0 (axComp2 h f g t)    = T.axComp2 h f g t
forget0 (axLift f a b)       = T.axLift f a b
forget0 (axPost f h a b)     = T.axPost f h a b
forget0 (axFan h1 h2 h a b)  = T.axFan h1 h2 h a b
forget0 (axZ x)              = T.axZ x
forget0 (axTreeRecLf f s p)         = T.axTreeRecLf f s p
forget0 (axTreeRecNd f s p a b)     = T.axTreeRecNd f s p a b
forget0 (axIfLfL a b)        = T.axIfLfL a b
forget0 (axIfLfN x y a b)    = T.axIfLfN x y a b
forget0 axIfLfLL             = T.axIfLfLL
forget0 (axIfLfNL x y)       = T.axIfLfNL x y
forget0 axTreeEqLL           = T.axTreeEqLL
forget0 (axTreeEqLN a b)     = T.axTreeEqLN a b
forget0 (axTreeEqNL a b)     = T.axTreeEqNL a b
forget0 (axTreeEqNN a1 a2 b1 b2) = T.axTreeEqNN a1 a2 b1 b2
forget0 (axGoodstein a b)    = T.axGoodstein a b
forget0 (axRefl t)           = T.axRefl t
forget0 (ruleSym d)          = T.ruleSym (forget0 d)
forget0 (ruleTrans d1 d2)    = T.ruleTrans (forget0 d1) (forget0 d2)
forget0 (cong1 f d)          = T.cong1 f (forget0 d)
forget0 (congL g x d)        = T.congL g x (forget0 d)
forget0 (congR g x d)        = T.congR g x (forget0 d)
forget0 (axEqTrans a b c)    = T.axEqTrans a b c
forget0 (axEqCong1 f a b)    = T.axEqCong1 f a b
forget0 (axEqCongL g a b c)  = T.axEqCongL g a b c
forget0 (axEqCongR g a b c)  = T.axEqCongR g a b c
forget0 (axK P Q)            = T.axK P Q
forget0 (axS P Q R)          = T.axS P Q R
forget0 (axNeg P Q)          = T.axNeg P Q
forget0 (mp d1 d2)           = T.mp (forget0 d1) (forget0 d2)
forget0 (ruleInst x t d)     = T.ruleInst x t (forget0 d)

------------------------------------------------------------------------
-- Open consistency : no proof of bot in the open fragment.
--
-- bot is the false atomic equation (eqn trueT falseT) used throughout
-- the codebase (cf. BRA2.Thm11Abstract).

open import BRA2.DerivThreshold using (trueT ; falseT)

bot : Formula
bot = atomic (eqn trueT falseT)

OpenCon0 : Set
OpenCon0 = DerivT0 bot -> Empty
