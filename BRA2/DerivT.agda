{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DerivT -- threshold derivation type for BRA2.
--
-- Same as BRA2.Deriv except the binary-tree induction constructors
--   ruleIndBT  : (P : Formula) -> ... -> Deriv P
--   ruleIndBT2 : (P : Formula) -> ... -> Deriv P
-- are replaced by their atomic-only fragments
--   indBT  : (e : Equation) -> ... -> DerivT (atomic e)
--   indBT2 : (e : Equation) -> ... -> DerivT (atomic e)
--
-- This pins down the "threshold formal system" identified by the audit
-- in godelI-II-summary.tex (Section "Induction calibration:
-- atomic-predicate tree induction only"): tree induction is restricted
-- to atomic-equation predicates.  Compound-formula induction is not
-- available.  Every other rule of BRA's Deriv is mirrored verbatim.
--
-- forget : DerivT P -> Deriv P  is the soundness embedding (every
-- threshold-derivation lifts to a full BRA-derivation).
--
-- The full GoedelIIFull closure has been refactored
-- (BRA2.TreeEqReflParam, BRA2.Th12TreeEqUniv, BRA2.Th12TreeRecInternal)
-- to use ruleIndBTAtomic / ruleIndBT2Atomic (derived lemmas in
-- BRA2.Deriv) at every induction site.  The remaining work, beyond
-- this file, is to lift the entire 147-file closure across forget,
-- producing  godelII : DerivT Con -> DerivT bot ; that refactor is
-- mechanical (every BRA2.Deriv constructor mirrors a DerivT one) but
-- not yet performed.

module BRA2.DerivT where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.Deriv as D

------------------------------------------------------------------------
-- DerivT : threshold derivation relation.

data DerivT : Formula -> Set where

  ------------------------------------------------------------------
  -- Computation axioms (defining equations of the primitive functors).

  axI      : (t : Term) -> DerivT (atomic (eqn (ap1 I t) t))
  axFst    : (a b : Term) -> DerivT (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
  axSnd    : (a b : Term) -> DerivT (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
  axFstLf  : DerivT (atomic (eqn (ap1 Fst O) O))
  axSndLf  : DerivT (atomic (eqn (ap1 Snd O) O))
  axConst  : (a b : Term) -> DerivT (atomic (eqn (ap2 Const a b) a))
  axComp   : (f g : Fun1) (t : Term) ->
             DerivT (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
  axComp2  : (h : Fun2) (f g : Fun1) (t : Term) ->
             DerivT (atomic (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))
  axLift   : (f : Fun1) (a b : Term) ->
             DerivT (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
  axPost   : (f : Fun1) (h : Fun2) (a b : Term) ->
             DerivT (atomic (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))
  axFan    : (h1 h2 h : Fun2) (a b : Term) ->
             DerivT (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                                  (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
  axZ      : (x : Term) -> DerivT (atomic (eqn (ap1 Z x) O))

  axTreeRecLf : (f : Fun1) (s : Fun2) (p : Term) ->
                DerivT (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))
  axTreeRecNd : (f : Fun1) (s : Fun2) (p a b : Term) ->
                DerivT (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a b))
                                     (ap2 s (ap2 Pair p (ap2 Pair a b))
                                            (ap2 Pair (ap2 (treeRec f s) p a)
                                                      (ap2 (treeRec f s) p b)))))

  axIfLfL  : (a b : Term) ->
             DerivT (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
  axIfLfN  : (x y a b : Term) ->
             DerivT (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))
  axIfLfLL : DerivT (atomic (eqn (ap2 IfLf O O) O))
  axIfLfNL : (x y : Term) ->
             DerivT (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))

  axTreeEqLL : DerivT (atomic (eqn (ap2 TreeEq O O) O))
  axTreeEqLN : (a b : Term) ->
               DerivT (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
  axTreeEqNL : (a b : Term) ->
               DerivT (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
  axTreeEqNN : (a1 a2 b1 b2 : Term) ->
               DerivT (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                                    (ap2 IfLf (ap2 TreeEq a1 b1)
                                              (ap2 Pair (ap2 TreeEq a2 b2)
                                                        (ap2 Pair O O)))))

  axGoodstein : (a b : Term) ->
                DerivT (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                                     (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

  ------------------------------------------------------------------
  -- Structural rules on atomic equations.

  axRefl     : (t : Term) -> DerivT (atomic (eqn t t))
  ruleSym    : {t u : Term} ->
               DerivT (atomic (eqn t u)) ->
               DerivT (atomic (eqn u t))
  ruleTrans  : {t u v : Term} ->
               DerivT (atomic (eqn t u)) ->
               DerivT (atomic (eqn u v)) ->
               DerivT (atomic (eqn t v))
  cong1      : (f : Fun1) {t u : Term} ->
               DerivT (atomic (eqn t u)) ->
               DerivT (atomic (eqn (ap1 f t) (ap1 f u)))
  congL      : (g : Fun2) {t u : Term} (x : Term) ->
               DerivT (atomic (eqn t u)) ->
               DerivT (atomic (eqn (ap2 g t x) (ap2 g u x)))
  congR      : (g : Fun2) (x : Term) {t u : Term} ->
               DerivT (atomic (eqn t u)) ->
               DerivT (atomic (eqn (ap2 g x t) (ap2 g x u)))

  axEqTrans  : (a b c : Term) ->
               DerivT ((atomic (eqn a b))
                        imp ((atomic (eqn a c))
                              imp (atomic (eqn b c))))
  axEqCong1  : (f : Fun1) (a b : Term) ->
               DerivT ((atomic (eqn a b))
                        imp (atomic (eqn (ap1 f a) (ap1 f b))))
  axEqCongL  : (g : Fun2) (a b c : Term) ->
               DerivT ((atomic (eqn a b))
                        imp (atomic (eqn (ap2 g a c) (ap2 g b c))))
  axEqCongR  : (g : Fun2) (a b c : Term) ->
               DerivT ((atomic (eqn a b))
                        imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

  ------------------------------------------------------------------
  -- Propositional axioms (Guard Ax 11, 12, 13).

  axK        : (P Q : Formula) ->
               DerivT (P imp (Q imp P))
  axS        : (P Q R : Formula) ->
               DerivT ((P imp (Q imp R))
                       imp ((P imp Q) imp (P imp R)))
  axNeg      : (P Q : Formula) ->
               DerivT (((not P) imp (not Q)) imp (Q imp P))

  ------------------------------------------------------------------
  -- Rules of inference.

  mp         : {P Q : Formula} ->
               DerivT (P imp Q) ->
               DerivT P ->
               DerivT Q

  ruleInst   : (x : Nat) (t : Term) {P : Formula} ->
               DerivT P ->
               DerivT (substF x t P)

  ------------------------------------------------------------------
  -- Atomic-only binary-tree induction.  This is the THRESHOLD
  -- restriction: the induction predicate must be an atomic equation,
  -- not a compound formula.

  indBT      : (e : Equation) (v1 v2 : Nat) ->
               DerivT (atomic (substEq zero O e)) ->
               DerivT ((atomic (substEq zero (var v1) e)) imp
                       ((atomic (substEq zero (var v2) e)) imp
                        (atomic (substEq zero (ap2 Pair (var v1) (var v2)) e)))) ->
               DerivT (atomic e)

  indBT2     : (e : Equation) (v1 v2 v3 v4 : Nat) ->
               DerivT (atomic (substEq (suc zero) O (substEq zero O e))) ->
               DerivT ((atomic (substEq (suc zero) (var v3) (substEq zero O e))) imp
                       ((atomic (substEq (suc zero) (var v4) (substEq zero O e))) imp
                        (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                                     (substEq zero O e))))) ->
               DerivT ((atomic (substEq (suc zero) O (substEq zero (var v1) e))) imp
                       ((atomic (substEq (suc zero) O (substEq zero (var v2) e))) imp
                        (atomic (substEq (suc zero) O
                                                     (substEq zero (ap2 Pair (var v1) (var v2)) e))))) ->
               DerivT ((atomic (substEq (suc zero) (var v3) (substEq zero (var v1) e))) imp
                       ((atomic (substEq (suc zero) (var v4) (substEq zero (var v2) e))) imp
                        (atomic (substEq (suc zero) (ap2 Pair (var v3) (var v4))
                                                     (substEq zero (ap2 Pair (var v1) (var v2)) e))))) ->
               DerivT (atomic e)

------------------------------------------------------------------------
-- forget : DerivT P -> Deriv P
--
-- Soundness embedding: every threshold-derivation lifts to a full BRA
-- derivation.  Structural recursion over DerivT: each constructor maps
-- to its same-named counterpart in BRA2.Deriv, except indBT / indBT2
-- which map to ruleIndBT / ruleIndBT2 with motive (atomic e).

forget : {P : Formula} -> DerivT P -> D.Deriv P
forget (axI t)              = D.axI t
forget (axFst a b)          = D.axFst a b
forget (axSnd a b)          = D.axSnd a b
forget axFstLf              = D.axFstLf
forget axSndLf              = D.axSndLf
forget (axConst a b)        = D.axConst a b
forget (axComp f g t)       = D.axComp f g t
forget (axComp2 h f g t)    = D.axComp2 h f g t
forget (axLift f a b)       = D.axLift f a b
forget (axPost f h a b)     = D.axPost f h a b
forget (axFan h1 h2 h a b)  = D.axFan h1 h2 h a b
forget (axZ x)              = D.axZ x
forget (axTreeRecLf f s p)         = D.axTreeRecLf f s p
forget (axTreeRecNd f s p a b)     = D.axTreeRecNd f s p a b
forget (axIfLfL a b)        = D.axIfLfL a b
forget (axIfLfN x y a b)    = D.axIfLfN x y a b
forget axIfLfLL             = D.axIfLfLL
forget (axIfLfNL x y)       = D.axIfLfNL x y
forget axTreeEqLL           = D.axTreeEqLL
forget (axTreeEqLN a b)     = D.axTreeEqLN a b
forget (axTreeEqNL a b)     = D.axTreeEqNL a b
forget (axTreeEqNN a1 a2 b1 b2) = D.axTreeEqNN a1 a2 b1 b2
forget (axGoodstein a b)    = D.axGoodstein a b
forget (axRefl t)           = D.axRefl t
forget (ruleSym d)          = D.ruleSym (forget d)
forget (ruleTrans d1 d2)    = D.ruleTrans (forget d1) (forget d2)
forget (cong1 f d)          = D.cong1 f (forget d)
forget (congL g x d)        = D.congL g x (forget d)
forget (congR g x d)        = D.congR g x (forget d)
forget (axEqTrans a b c)    = D.axEqTrans a b c
forget (axEqCong1 f a b)    = D.axEqCong1 f a b
forget (axEqCongL g a b c)  = D.axEqCongL g a b c
forget (axEqCongR g a b c)  = D.axEqCongR g a b c
forget (axK P Q)            = D.axK P Q
forget (axS P Q R)          = D.axS P Q R
forget (axNeg P Q)          = D.axNeg P Q
forget (mp d1 d2)           = D.mp (forget d1) (forget d2)
forget (ruleInst x t d)     = D.ruleInst x t (forget d)
forget (indBT e v1 v2 base step) =
  D.ruleIndBT (atomic e) v1 v2 (forget base) (forget step)
forget (indBT2 e v1 v2 v3 v4 baseLL baseLN baseNL basePP) =
  D.ruleIndBT2 (atomic e) v1 v2 v3 v4
    (forget baseLL) (forget baseLN) (forget baseNL) (forget basePP)
