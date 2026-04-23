{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.DerivF -- unified, hyp-less derivation relation on formulas.
--
-- This is the new core derivation type for the unified-design
-- redesign (see Guard/UNIFIED-DESIGN.md).  It replaces the old
--   Guard.Step.Deriv      (equation-level, hyp-carrying)
--   Guard.Provable        (propositional layer above Deriv)
--   Guard.BRA             (Option G propositional layer)
-- with a single  Deriv : Formula -> Set  matching Guard 1963 BRA
-- (Def 7, pp.9-10) as a pure Hilbert system.
--
-- Key differences from Guard.Step.Deriv:
--
--   * No  hyp  parameter.  Guard's BRA has  ⊢ P ; hypothetical
--     reasoning "X ⊢ Y" is encoded as  ⊢ X ⊃ Y  via the deduction
--     theorem (see Guard.DerivFDedThm).
--
--   * Conclusion is a  Formula  (not an  Equation ), so the
--     propositional connectives  not  and  _imp_  live at the object
--     level.
--
--   * Propositional axioms Ax 11-13 (K, S, Neg) and modus ponens are
--     constructors, not derived external layers.
--
--   *  ruleInst  has no side condition (no hyp to constrain).
--
--   *  ruleIndBT  is binary-tree induction matching our  Rec
--     primitive:  P(O) + P(x_1) ⊃ P(x_2) ⊃ P(Pair x_1 x_2) .
--
-- Migration note: this file is the  [unify-1]  commit.  Old  Deriv  +
-- Provable + BRA remain in place during migration; downstream modules
-- port to DerivF incrementally ( [unify-2] onward).  After  [unify-6] ,
--  DerivF  is renamed to  Deriv  and the old modules are removed.
--
-- No postulates, no holes.  Compiles under --safe --without-K
-- --exact-split.

module Guard.DerivF where

open import Guard.Base
open import Guard.Term
open import Guard.Formula

------------------------------------------------------------------------
-- Convenience abbreviation:  eqF t u  =  atomic (eqn t u) .  Used in
-- port modules to keep equational conclusions readable.

eqF : Term -> Term -> Formula
eqF t u = atomic (eqn t u)

------------------------------------------------------------------------
-- Deriv P : P is a theorem of BRA (hyp-less, formula-level).

data Deriv : Formula -> Set where

  ------------------------------------------------------------------
  -- Computation axioms (defining equations of the primitive
  -- functors).  Each concludes an  atomic  equation.
  --
  -- These are our project-specific extensions over Guard's minimal
  -- BRA (which only has  s , v , u  as primitive functors; we add
  --  Pair, Fst, Snd, IfLf, TreeEq, Rec, RecP, Goodstein, etc.).
  -- They play the same role Guard's  Ax 0-3, 8-10  play: direct
  -- equational definitions of the primitive operations.

  axI      : (t : Term) -> Deriv (atomic (eqn (ap1 I t) t))
  axFst    : (a b : Term) -> Deriv (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
  axSnd    : (a b : Term) -> Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
  axConst  : (a b : Term) -> Deriv (atomic (eqn (ap2 Const a b) a))
  axComp   : (f g : Fun1) (t : Term) ->
             Deriv (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))
  axComp2  : (h : Fun2) (f g : Fun1) (t : Term) ->
             Deriv (atomic (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))
  axLift   : (f : Fun1) (a b : Term) ->
             Deriv (atomic (eqn (ap2 (Lift f) a b) (ap1 f a)))
  axPost   : (f : Fun1) (h : Fun2) (a b : Term) ->
             Deriv (atomic (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))
  axFan    : (h1 h2 h : Fun2) (a b : Term) ->
             Deriv (atomic (eqn (ap2 (Fan h1 h2 h) a b)
                                 (ap2 h (ap2 h1 a b) (ap2 h2 a b))))
  axKT     : (t x : Term) -> Deriv (atomic (eqn (ap1 (KT t) x) t))

  ------------------------------------------------------------------
  -- Primitive recursion on trees (Guard Ax 9-10 analog for binary
  -- trees instead of naturals).

  axRecLf  : (z : Term) (s : Fun2) ->
             Deriv (atomic (eqn (ap1 (Rec z s) O) z))
  axRecNd  : (z : Term) (s : Fun2) (a b : Term) ->
             Deriv (atomic (eqn (ap1 (Rec z s) (ap2 Pair a b))
                                 (ap2 s (ap2 Pair a b)
                                        (ap2 Pair (ap1 (Rec z s) a)
                                                  (ap1 (Rec z s) b)))))
  axRecPLf : (s : Fun2) (p : Term) ->
             Deriv (atomic (eqn (ap2 (RecP s) p O) O))
  axRecPNd : (s : Fun2) (p a b : Term) ->
             Deriv (atomic (eqn (ap2 (RecP s) p (ap2 Pair a b))
                                 (ap2 s (ap2 Pair p (ap2 Pair a b))
                                        (ap2 Pair (ap2 (RecP s) p a)
                                                  (ap2 (RecP s) p b)))))

  ------------------------------------------------------------------
  -- Conditional and equality primitives.

  axIfLfL  : (a b : Term) ->
             Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
  axIfLfN  : (x y a b : Term) ->
             Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))
  axTreeEqLL : Deriv (atomic (eqn (ap2 TreeEq O O) O))
  axTreeEqLN : (a b : Term) ->
               Deriv (atomic (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))
  axTreeEqNL : (a b : Term) ->
               Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))
  axTreeEqNN : (a1 a2 b1 b2 : Term) ->
               Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                                   (ap2 IfLf (ap2 TreeEq a1 b1)
                                             (ap2 Pair (ap2 TreeEq a2 b2)
                                                       (ap2 Pair O O)))))

  -- Goodstein-characteristic equation (tree analog, see
  -- Guard.Step.axGoodstein for rationale).

  axGoodstein : (a b : Term) ->
                Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                                    (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

  ------------------------------------------------------------------
  -- Structural rules on atomic equations.
  --
  -- These are derivable from Guard's  Ax 4-7 + mp + ruleInst  (see
  -- Guard Exercises 17-18), but we keep them as primitive
  -- constructors for proof ergonomics.  Sound (the validity of
  -- equational reasoning is not in doubt).

  axRefl     : (t : Term) -> Deriv (atomic (eqn t t))
  ruleSym    : {t u : Term} ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn u t))
  ruleTrans  : {t u v : Term} ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn u v)) ->
               Deriv (atomic (eqn t v))
  cong1      : (f : Fun1) {t u : Term} ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn (ap1 f t) (ap1 f u)))
  congL      : (g : Fun2) {t u : Term} (x : Term) ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn (ap2 g t x) (ap2 g u x)))
  congR      : (g : Fun2) (x : Term) {t u : Term} ->
               Deriv (atomic (eqn t u)) ->
               Deriv (atomic (eqn (ap2 g x t) (ap2 g x u)))

  ------------------------------------------------------------------
  -- Formula-level equality axioms (Guard Ax 4-7), stated as
  -- implications on atomic formulas.  Used by the Thm 14 chain for
  -- hypothesis-discharging via  mp  on implication form.

  -- Ax 4:  a = b ⊃ . a = c ⊃ b = c .
  axEqTrans  : (a b c : Term) ->
               Deriv ((atomic (eqn a b))
                       imp ((atomic (eqn a c))
                             imp (atomic (eqn b c))))

  -- Ax 5:  a = b ⊃ f(a) = f(b) .
  axEqCong1  : (f : Fun1) (a b : Term) ->
               Deriv ((atomic (eqn a b))
                       imp (atomic (eqn (ap1 f a) (ap1 f b))))

  -- Ax 6:  a = b ⊃ g(a, c) = g(b, c) .
  axEqCongL  : (g : Fun2) (a b c : Term) ->
               Deriv ((atomic (eqn a b))
                       imp (atomic (eqn (ap2 g a c) (ap2 g b c))))

  -- Ax 7:  a = b ⊃ g(c, a) = g(c, b) .
  axEqCongR  : (g : Fun2) (a b c : Term) ->
               Deriv ((atomic (eqn a b))
                       imp (atomic (eqn (ap2 g c a) (ap2 g c b))))

  ------------------------------------------------------------------
  -- Propositional axioms (Guard Ax 11, 12, 13).

  -- Ax 11 (K):  P ⊃ . Q ⊃ P .
  axK        : (P Q : Formula) ->
               Deriv (P imp (Q imp P))

  -- Ax 12 (S):  P ⊃ (Q ⊃ R) ⊃ . P ⊃ Q ⊃ . P ⊃ R .
  axS        : (P Q R : Formula) ->
               Deriv ((P imp (Q imp R))
                       imp ((P imp Q) imp (P imp R)))

  -- Ax 13 (classical contraposition):  ~P ⊃ ~Q ⊃ . Q ⊃ P .
  axNeg      : (P Q : Formula) ->
               Deriv ((not P) imp ((not Q) imp (Q imp P)))

  -- Ex falso quodlibet:  P ⊃ ~P ⊃ Q .
  --
  -- CLASSICALLY DERIVABLE from axK / axS / axNeg / mp (~20 Hilbert
  -- steps through double-negation).  Added as a primitive so that
  --  Guard.Thm14TPrime.tPrimeDeriv  is a one-line axiom instance
  -- rather than an inline classical derivation.  Philosophically
  -- redundant but not unsound.
  axExFalso  : (P Q : Formula) ->
               Deriv (P imp ((not P) imp Q))

  ------------------------------------------------------------------
  -- Rules of inference (no side conditions).

  -- Modus ponens (Guard Def 7 rule 1).
  mp         : {P Q : Formula} ->
               Deriv (P imp Q) ->
               Deriv P ->
               Deriv Q

  -- Substitution of a term for a variable (Guard Def 7 rule 2).
  -- In a hyp-less system, substitution is unconditionally sound: if
  --  P  is a theorem then every instance  P[t/x]  is a theorem.
  ruleInst   : (x : Nat) (t : Term) {P : Formula} ->
               Deriv P ->
               Deriv (substF x t P)

  -- Binary-tree induction (Guard Def 7 rule 3 analog for trees).
  -- From  P(O)  and  P(x_1) ⊃ P(x_2) ⊃ P(Pair x_1 x_2) , conclude
  --  P(x_0) .  The fresh variables  v1 , v2  are parameters; the
  -- rule has no side condition (no hyp).
  ruleIndBT  : (P : Formula) (v1 v2 : Nat) ->
               Deriv (substF zero O P) ->
               Deriv ((substF zero (var v1) P) imp
                      ((substF zero (var v2) P) imp
                       (substF zero (ap2 Pair (var v1) (var v2)) P))) ->
               Deriv P

  ------------------------------------------------------------------
  -- Schema F (uniqueness of tree recursion).
  --
  -- If  f  and  g  both satisfy the Rec defining equations (same z,
  -- same s), then  f  and  g  agree on all trees.  Guard 1963 does
  -- not have this as a primitive axiom; we add it because our
  -- primitive recursion discipline benefits from it (see
  -- notes in  Guard.Step ).  Stated on atomic equations.

  ruleF      : (f g : Fun1) (z : Term) (s : Fun2) ->
               Deriv (atomic (eqn (ap1 f O) z)) ->
               Deriv (atomic (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
                                   (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                                          (ap2 Pair (ap1 f (var zero))
                                                    (ap1 f (var (suc zero))))))) ->
               Deriv (atomic (eqn (ap1 g O) z)) ->
               Deriv (atomic (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
                                   (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                                          (ap2 Pair (ap1 g (var zero))
                                                    (ap1 g (var (suc zero))))))) ->
               Deriv (atomic (eqn (ap1 f (var zero)) (ap1 g (var zero))))

------------------------------------------------------------------------
-- Consistency (hyp-less form).
--
-- "BRA is consistent" means:  0 = 1  is not a theorem.  In our tree
-- encoding,  trueT = O  and  falseT = ap2 Pair O O ,  so this is
-- not (Deriv (atomic (eqn O falseT))) .

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

Consistent : Set
Consistent = Deriv (atomic (eqn trueT falseT)) -> Empty
