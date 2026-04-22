{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.DerivFDedThm -- deduction theorem for the unified hyp-less
-- Deriv (Guard Exercise 19).
--
-- Theorem:  if  Y  is derivable treating  A  as an additional axiom,
-- then  A ⊃ Y  is derivable in plain BRA.  Formally:
--
--   deductionTheorem : (A B : Formula) -> DerivAssuming A B ->
--                      Deriv (A imp B)
--
-- Where  DerivAssuming A  mirrors the non-quantifier-like part of
--  Deriv  (equational axioms, structural rules, propositional
-- axioms, mp) and adds one extra constructor  ruleHypAux :
-- DerivAssuming A A .
--
-- DESIGN CHOICE:  DerivAssuming does NOT include  ruleInst' ,
--  ruleIndBT' , or  ruleF' .  The standard Hilbert deduction
-- theorem requires a side condition on these (the variable being
-- substituted/inducted-on must not be free in A), which would
-- pollute the API.  Our chain construction never needs these rules
-- under a hypothesis — hypothetical reasoning is always about
-- propositional composition (axK, axS, axNeg, mp) and structural
-- equational manipulation (ruleTrans, cong1, etc.).  If a future
-- chain step requires  ruleInst  under a hypothesis, it must be
-- applied OUTSIDE the  deductionTheorem  call (i.e., at the
-- hyp-less  Deriv  level), which is always possible for our use
-- cases.
--
-- This matches Guard.ProvableLemmas.deductionThm's scope (Provable
-- has no ruleInst constructor either; substitution is a meta-level
-- function).
--
-- The proof is a standard Hilbert-system structural induction.
-- Each  Deriv  constructor  c  that produces  Deriv Y  is mapped via
--  axK :  Y ⊃ (A ⊃ Y) , so  c  lifted gives  Deriv (A imp Y) .  The
--  ruleHypAux  case gives  provI A  (provable  A ⊃ A ).  The  mp
-- case uses  axS  to distribute  A ⊃  through modus ponens.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.DerivFDedThm where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF

------------------------------------------------------------------------
-- DerivAssuming A P : P is derivable using  A  as an extra axiom,
-- restricted to the subset of  Deriv  constructors that interact
-- cleanly with the deduction theorem.

data DerivAssuming (A : Formula) : Formula -> Set where

  -- Computation axioms (mirror Deriv's equational constructors)
  axI'      : (t : Term) -> DerivAssuming A (atomic (eqn (ap1 I t) t))
  axFst'    : (a b : Term) -> DerivAssuming A (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
  axSnd'    : (a b : Term) -> DerivAssuming A (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
  axConst'  : (a b : Term) -> DerivAssuming A (atomic (eqn (ap2 Const a b) a))
  axComp'   : (f g : Fun1) (t : Term) ->
              DerivAssuming A (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
  axComp2'  : (h : Fun2) (f g : Fun1) (t : Term) ->
              DerivAssuming A (atomic (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))
  axLift'   : (f : Fun1) (a b : Term) ->
              DerivAssuming A (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
  axPost'   : (f : Fun1) (h : Fun2) (a b : Term) ->
              DerivAssuming A (atomic (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))
  axFan'    : (h1 h2 h : Fun2) (a b : Term) ->
              DerivAssuming A (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                                            (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
  axKT'     : (t x : Term) -> DerivAssuming A (atomic (eqn (ap1 (KT t) x) t))
  axRecLf'  : (z : Term) (s : Fun2) ->
              DerivAssuming A (atomic (eqn (ap1 (Rec z s) O) z))
  axRecNd'  : (z : Term) (s : Fun2) (a b : Term) ->
              DerivAssuming A (atomic (eqn (ap1 (Rec z s) (ap2 Pair a b))
                                            (ap2 s (ap2 Pair a b)
                                                   (ap2 Pair (ap1 (Rec z s) a)
                                                             (ap1 (Rec z s) b)))))
  axRecPLf' : (s : Fun2) (p : Term) ->
              DerivAssuming A (atomic (eqn (ap2 (RecP s) p O) O))
  axRecPNd' : (s : Fun2) (p a b : Term) ->
              DerivAssuming A (atomic (eqn (ap2 (RecP s) p (ap2 Pair a b))
                                            (ap2 s (ap2 Pair p (ap2 Pair a b))
                                                   (ap2 Pair (ap2 (RecP s) p a)
                                                             (ap2 (RecP s) p b)))))
  axIfLfL'  : (a b : Term) ->
              DerivAssuming A (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
  axIfLfN'  : (x y a b : Term) ->
              DerivAssuming A (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))
  axTreeEqLL' : DerivAssuming A (atomic (eqn (ap2 TreeEq O O) O))
  axTreeEqLN' : (a b : Term) ->
                DerivAssuming A (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
  axTreeEqNL' : (a b : Term) ->
                DerivAssuming A (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
  axTreeEqNN' : (a1 a2 b1 b2 : Term) ->
                DerivAssuming A (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                                              (ap2 IfLf (ap2 TreeEq a1 b1)
                                                        (ap2 Pair (ap2 TreeEq a2 b2)
                                                                  (ap2 Pair O O)))))
  axGoodstein' : (a b : Term) ->
                 DerivAssuming A (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                                               (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

  -- Structural rules
  axRefl'   : (t : Term) -> DerivAssuming A (atomic (eqn t t))
  ruleSym'  : {t u : Term} ->
              DerivAssuming A (atomic (eqn t u)) ->
              DerivAssuming A (atomic (eqn u t))
  ruleTrans' : {t u v : Term} ->
               DerivAssuming A (atomic (eqn t u)) ->
               DerivAssuming A (atomic (eqn u v)) ->
               DerivAssuming A (atomic (eqn t v))
  cong1'    : (f : Fun1) {t u : Term} ->
              DerivAssuming A (atomic (eqn t u)) ->
              DerivAssuming A (atomic (eqn (ap1 f t) (ap1 f u)))
  congL'    : (g : Fun2) {t u : Term} (x : Term) ->
              DerivAssuming A (atomic (eqn t u)) ->
              DerivAssuming A (atomic (eqn (ap2 g t x) (ap2 g u x)))
  congR'    : (g : Fun2) (x : Term) {t u : Term} ->
              DerivAssuming A (atomic (eqn t u)) ->
              DerivAssuming A (atomic (eqn (ap2 g x t) (ap2 g x u)))

  -- Formula-level equality axioms (Guard Ax 4-7)
  axEqTrans' : (a b c : Term) ->
               DerivAssuming A ((atomic (eqn a b))
                                 imp ((atomic (eqn a c))
                                       imp (atomic (eqn b c))))
  axEqCong1' : (f : Fun1) (a b : Term) ->
               DerivAssuming A ((atomic (eqn a b))
                                 imp (atomic (eqn (ap1 f a) (ap1 f b))))
  axEqCongL' : (g : Fun2) (a b c : Term) ->
               DerivAssuming A ((atomic (eqn a b))
                                 imp (atomic (eqn (ap2 g a c) (ap2 g b c))))
  axEqCongR' : (g : Fun2) (a b c : Term) ->
               DerivAssuming A ((atomic (eqn a b))
                                 imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

  -- Propositional axioms
  axK'      : (P Q : Formula) -> DerivAssuming A (P imp (Q imp P))
  axS'      : (P Q R : Formula) ->
              DerivAssuming A ((P imp (Q imp R))
                                imp ((P imp Q) imp (P imp R)))
  axNeg'    : (P Q : Formula) ->
              DerivAssuming A ((not P) imp ((not Q) imp (Q imp P)))

  -- Modus ponens
  mp'       : {P Q : Formula} ->
              DerivAssuming A (P imp Q) ->
              DerivAssuming A P ->
              DerivAssuming A Q

  -- Hypothesis use (the only new constructor vs  Deriv )
  ruleHypAux : DerivAssuming A A

------------------------------------------------------------------------
-- provI A : Deriv (A imp A)  (identity implication).
--
-- Standard Hilbert derivation via K + S:
--   axS A (A imp A) A : (A ⊃ ((A imp A) ⊃ A)) ⊃ ((A ⊃ (A imp A)) ⊃ (A ⊃ A))
--   axK A (A imp A)   : A ⊃ ((A imp A) ⊃ A)
--   mp above          : (A ⊃ (A imp A)) ⊃ (A ⊃ A)
--   axK A A           : A ⊃ (A ⊃ A)
--   mp above          : A ⊃ A

provI : (A : Formula) -> Deriv (A imp A)
provI A = mp (mp (axS A (A imp A) A) (axK A (A imp A))) (axK A A)

------------------------------------------------------------------------
-- Helpers.

private
  -- dedThmMp : combine (A ⊃ (R ⊃ Q)) and (A ⊃ R) to get (A ⊃ Q) via axS.
  dedThmMp : (A R Q : Formula) ->
             Deriv (A imp (R imp Q)) ->
             Deriv (A imp R) ->
             Deriv (A imp Q)
  dedThmMp A R Q dPRQ dPR = mp (mp (axS A R Q) dPRQ) dPR

-- liftK : lift any theorem to (A ⊃ theorem) via axK.
liftK : (A X : Formula) -> Deriv X -> Deriv (A imp X)
liftK A X dX = mp (axK X A) dX

------------------------------------------------------------------------
-- Deduction theorem.
--
-- Structural recursion on the  DerivAssuming  tree.

deductionTheorem : (A B : Formula) -> DerivAssuming A B -> Deriv (A imp B)

-- Equational axioms: lift via axK.
deductionTheorem A ._ (axI' t) = liftK A _ (axI t)
deductionTheorem A ._ (axFst' a b) = liftK A _ (axFst a b)
deductionTheorem A ._ (axSnd' a b) = liftK A _ (axSnd a b)
deductionTheorem A ._ (axConst' a b) = liftK A _ (axConst a b)
deductionTheorem A ._ (axComp' f g t) = liftK A _ (axComp f g t)
deductionTheorem A ._ (axComp2' h f g t) = liftK A _ (axComp2 h f g t)
deductionTheorem A ._ (axLift' f a b) = liftK A _ (axLift f a b)
deductionTheorem A ._ (axPost' f h a b) = liftK A _ (axPost f h a b)
deductionTheorem A ._ (axFan' h1 h2 h a b) = liftK A _ (axFan h1 h2 h a b)
deductionTheorem A ._ (axKT' t x) = liftK A _ (axKT t x)
deductionTheorem A ._ (axRecLf' z s) = liftK A _ (axRecLf z s)
deductionTheorem A ._ (axRecNd' z s a b) = liftK A _ (axRecNd z s a b)
deductionTheorem A ._ (axRecPLf' s p) = liftK A _ (axRecPLf s p)
deductionTheorem A ._ (axRecPNd' s p a b) = liftK A _ (axRecPNd s p a b)
deductionTheorem A ._ (axIfLfL' a b) = liftK A _ (axIfLfL a b)
deductionTheorem A ._ (axIfLfN' x y a b) = liftK A _ (axIfLfN x y a b)
deductionTheorem A ._ axTreeEqLL' = liftK A _ axTreeEqLL
deductionTheorem A ._ (axTreeEqLN' a b) = liftK A _ (axTreeEqLN a b)
deductionTheorem A ._ (axTreeEqNL' a b) = liftK A _ (axTreeEqNL a b)
deductionTheorem A ._ (axTreeEqNN' a1 a2 b1 b2) = liftK A _ (axTreeEqNN a1 a2 b1 b2)
deductionTheorem A ._ (axGoodstein' a b) = liftK A _ (axGoodstein a b)

-- Structural (equation-level) rules.  For these, the IH is at the
-- atomic-equation level; we apply the corresponding axEqCong / axEqTrans
-- via dedThmMp.
deductionTheorem A ._ (axRefl' t) = liftK A _ (axRefl t)

deductionTheorem A ._ (ruleSym' {t} {u} dtu) =
  let ih = deductionTheorem A _ dtu
      -- axEqTrans t u t : (t=u) ⊃ ((t=t) ⊃ (u=t))
      aTrans = liftK A _ (axEqTrans t u t)
      step1 : Deriv (A imp ((atomic (eqn t t)) imp (atomic (eqn u t))))
      step1 = dedThmMp A (atomic (eqn t u))
                ((atomic (eqn t t)) imp (atomic (eqn u t)))
                aTrans ih
      step2 : Deriv (A imp atomic (eqn t t))
      step2 = liftK A _ (axRefl t)
  in dedThmMp A (atomic (eqn t t)) (atomic (eqn u t)) step1 step2

deductionTheorem A ._ (ruleTrans' {t} {u} {v} dtu duv) =
  let ih1 = deductionTheorem A _ dtu                 -- A imp (t=u)
      ih2 = deductionTheorem A _ duv                 -- A imp (u=v)
      -- Derive A imp (u=t) inline (avoid recursive call on a constructed term).
      -- axEqTrans t u t : (t=u) ⊃ ((t=t) ⊃ (u=t))
      aTransSym = liftK A _ (axEqTrans t u t)
      ih1symStep1 : Deriv (A imp ((atomic (eqn t t)) imp (atomic (eqn u t))))
      ih1symStep1 = dedThmMp A (atomic (eqn t u))
                      ((atomic (eqn t t)) imp (atomic (eqn u t)))
                      aTransSym ih1
      ih1symStep2 = liftK A _ (axRefl t)
      ih1sym : Deriv (A imp atomic (eqn u t))
      ih1sym = dedThmMp A (atomic (eqn t t)) (atomic (eqn u t))
                 ih1symStep1 ih1symStep2
      -- axEqTrans u t v : (u=t) ⊃ ((u=v) ⊃ (t=v))
      aTrans = liftK A _ (axEqTrans u t v)
      step1 : Deriv (A imp ((atomic (eqn u v)) imp (atomic (eqn t v))))
      step1 = dedThmMp A (atomic (eqn u t))
                ((atomic (eqn u v)) imp (atomic (eqn t v)))
                aTrans ih1sym
  in dedThmMp A (atomic (eqn u v)) (atomic (eqn t v)) step1 ih2

deductionTheorem A ._ (cong1' f {t} {u} dtu) =
  let ih = deductionTheorem A _ dtu
      aCong = liftK A _ (axEqCong1 f t u)
  in dedThmMp A (atomic (eqn t u))
       (atomic (eqn (ap1 f t) (ap1 f u))) aCong ih

deductionTheorem A ._ (congL' g {t} {u} x dtu) =
  let ih = deductionTheorem A _ dtu
      aCong = liftK A _ (axEqCongL g t u x)
  in dedThmMp A (atomic (eqn t u))
       (atomic (eqn (ap2 g t x) (ap2 g u x))) aCong ih

deductionTheorem A ._ (congR' g x {t} {u} dtu) =
  let ih = deductionTheorem A _ dtu
      aCong = liftK A _ (axEqCongR g t u x)
  in dedThmMp A (atomic (eqn t u))
       (atomic (eqn (ap2 g x t) (ap2 g x u))) aCong ih

-- Formula-level axioms (lift via axK).
deductionTheorem A ._ (axEqTrans' a b c) = liftK A _ (axEqTrans a b c)
deductionTheorem A ._ (axEqCong1' f a b) = liftK A _ (axEqCong1 f a b)
deductionTheorem A ._ (axEqCongL' g a b c) = liftK A _ (axEqCongL g a b c)
deductionTheorem A ._ (axEqCongR' g a b c) = liftK A _ (axEqCongR g a b c)
deductionTheorem A ._ (axK' P Q) = liftK A _ (axK P Q)
deductionTheorem A ._ (axS' P Q R) = liftK A _ (axS P Q R)
deductionTheorem A ._ (axNeg' P Q) = liftK A _ (axNeg P Q)

-- Modus ponens: the classical deduction-theorem case.
deductionTheorem A B (mp' {R} pq p) =
  dedThmMp A R B
    (deductionTheorem A (R imp B) pq)
    (deductionTheorem A R p)

-- Hypothesis: A ⊃ A, the identity implication.
deductionTheorem A .A ruleHypAux = provI A
