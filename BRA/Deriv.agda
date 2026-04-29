{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Deriv -- hyp-less, formula-level derivation relation matching
-- Guard 1963 BRA (Def 7, lecture notes pp.9-10).
--
--   * No  hyp  parameter.  Guard's BRA has  ⊢ P ; hypothetical
--     reasoning "X ⊢ Y" is encoded as  ⊢ X ⊃ Y  via the deduction
--     theorem.
--
--   * Conclusion is a  Formula  (not an  Equation ), so the
--     propositional connectives  not  and  _imp_  live at the object
--     level.
--
--   * Propositional axioms Ax 11-13 (K, S, Neg) and modus ponens are
--     constructors, not derived external layers.
--
--   *  ruleInst  has no side condition.
--
--   *  ruleIndBT  is binary-tree induction matching our  Rec
--     primitive:  P(O) + P(x_1) ⊃ P(x_2) ⊃ P(Pair x_1 x_2) .
--
-- The tree-specialised axioms (axRecLf / axRecNd / axTreeEq* /
-- axIfLf*) replace Guard's Ax 9-10 on naturals with their
-- binary-tree analogs, matching the project's guiding idea of
-- "replace 0 | S(x) by leaf | nd(a,b) to avoid some coding."
--
-- No postulates, no holes.

module BRA.Deriv where

open import BRA.Base
open import BRA.Term
open import BRA.Formula

------------------------------------------------------------------------
-- Convenience abbreviation:  eqF t u  =  atomic (eqn t u) .

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
  -- Safe-default totality on leaf input.  Combined with axFst / axSnd,
  -- Fst and Snd are total on canonical trees (O and Pair _ _).  Required
  -- for Theorem 12 base cases at x = O.  See feedback_thm12_totality...
  axFstLf  : Deriv (atomic (eqn (ap1 Fst O) O))
  axSndLf  : Deriv (atomic (eqn (ap1 Snd O) O))
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
  axZ      : (x : Term) -> Deriv (atomic (eqn (ap1 Z x) O))

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
  -- Safe-default totality when second arg is leaf.  Required for
  -- Theorem 12 base cases at x = O for IfLf.
  axIfLfLL : Deriv (atomic (eqn (ap2 IfLf O O) O))
  axIfLfNL : (x y : Term) ->
             Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O))
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

  -- Goodstein-characteristic equation (tree analog).

  axGoodstein : (a b : Term) ->
                Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O))
                                    (ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O))))

  ------------------------------------------------------------------
  -- Structural rules on atomic equations.
  --
  -- These are derivable from Guard's  Ax 4-7 + mp + ruleInst  (see
  -- Guard Exercises 17-18), but we keep them as primitive
  -- constructors for proof ergonomics.

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
  -- implications on atomic formulas.

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
  -- CLASSICALLY DERIVABLE from axK / axS / axNeg / mp.  Added as a
  -- primitive so that downstream tPrime-style derivations are
  -- one-line axiom instances rather than inline classical
  -- derivations.  Philosophically redundant but not unsound.
  axExFalso  : (P Q : Formula) ->
               Deriv (P imp ((not P) imp Q))

  -- Classical contrapositive:  (P ⊃ Q) ⊃ (~Q ⊃ ~P) .
  --
  -- Classical tautology.  The curried  axNeg  above is intuitionistically
  -- derivable from  axExFalso , so it is too weak to derive this.  Added
  -- as a primitive so that transport-inside-a-negation steps (used in
  -- the Thm 11 diagonal) are one-line axiom instances.
  axContrapos : (P Q : Formula) ->
                Deriv ((P imp Q) imp ((not Q) imp (not P)))

  ------------------------------------------------------------------
  -- Rules of inference (no side conditions).

  -- Modus ponens (Guard Def 7 rule 1).
  mp         : {P Q : Formula} ->
               Deriv (P imp Q) ->
               Deriv P ->
               Deriv Q

  -- Substitution of a term for a variable (Guard Def 7 rule 2).
  ruleInst   : (x : Nat) (t : Term) {P : Formula} ->
               Deriv P ->
               Deriv (substF x t P)

  -- Binary-tree induction (Guard Def 7 rule 3 analog for trees).
  -- From  P(O)  and  P(x_1) ⊃ P(x_2) ⊃ P(Pair x_1 x_2) , conclude
  --  P(x_0) .  The fresh variables  v1 , v2  are parameters.
  ruleIndBT  : (P : Formula) (v1 v2 : Nat) ->
               Deriv (substF zero O P) ->
               Deriv ((substF zero (var v1) P) imp
                      ((substF zero (var v2) P) imp
                       (substF zero (ap2 Pair (var v1) (var v2)) P))) ->
               Deriv P

------------------------------------------------------------------------
-- Derived axKT (Tree-indexed): for canonical input t = reify v, KT t
-- (defined as a function in BRA.Term) reduces to a Z + Comp2-Pair tree.
-- Transparency is provable by induction on v.

axKT : (v : Tree) (x : Term) ->
       Deriv (atomic (eqn (ap1 (KT (reify v)) x) (reify v)))
axKT lf       x = axZ x
axKT (nd a b) x =
  let s1 : Deriv (atomic (eqn (ap1 (Comp2 Pair (KT (reify a)) (KT (reify b))) x)
                              (ap2 Pair (ap1 (KT (reify a)) x)
                                        (ap1 (KT (reify b)) x))))
      s1 = axComp2 Pair (KT (reify a)) (KT (reify b)) x
      ihA = axKT a x
      ihB = axKT b x
      s2 = congL Pair (ap1 (KT (reify b)) x) ihA
      s3 = congR Pair (reify a) ihB
  in ruleTrans s1 (ruleTrans s2 s3)

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
