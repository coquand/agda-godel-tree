{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.CorF
--
-- Parallel structural recursion on Fun1/Fun2 producing simplified
-- BRA-equation forms for `cor (ap1 f x)` and `cor (ap2 g x v)`.
--
-- Motivation: Th12RecUniv.RecPairCase needs a bridge
--    mkAp2T sT (cor a)(cor b)  =  cor (s a b)
-- (called `ih_s_bra`).  In its full BRA-Deriv form this equation is
-- not universally true (it fails for s = Const, where the encoded LHS
-- is Pair-shaped but the decoded RHS = cor a is opaque).
--
-- The right object is a meta-function corF*:
--   corF1 f x : a Term that BRA-equals cor (ap1 f x), simplified using
--              f's defining axiom + sub-Fun's corF*.
-- with a proof object showing cor (ap1 f x) = corF1 f x in BRA.
--
-- Each constructor case unfolds via the corresponding defining axiom
-- (cong1 cor of the axiom).  Recursive cases (Comp, Comp2, Lift, Post,
-- Fan, Rec, RecP, IfLf, TreeEq) recurse via the mutual companion.
--
-- For non-canonical inputs (var n, ap1 _ _, etc.) where a constructor's
-- axiom doesn't apply, the trivial result `ap1 cor (ap1 f x)` is
-- emitted with axRefl.  The recursion is sound but produces unhelpful
-- forms at non-canonical positions; consumers should call corF* only
-- at canonical-shape inputs (O or ap2 Pair _ _ at the relevant level).
--
-- For Th12RecUniv's specific use case (input always `ap2 Pair v1 v2`
-- at the top level), the recursion gives meaningful forms at all
-- relevant positions.
--
-- No postulates, no holes, --safe --without-K --exact-split.

module BRA.CorF where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor             using (cor ; stepCor)
open import BRA.CorOfPair       using (corOfPair ; corOfFstPair ; corOfSndPair)
open import BRA.Thm14CodeFTeqAsym using (mkAp2T)

------------------------------------------------------------------------
-- Result record: the simplified Term and the BRA-Deriv proof that
-- `cor (ap1 f x)` (or `cor (ap2 g x v)`) BRA-equals the simplified Term.

record CorF1Result (f : Fun1) (x : Term) : Set where
  constructor mkCorF1
  field
    result : Term
    proof  : Deriv (atomic (eqn (ap1 cor (ap1 f x)) result))
open CorF1Result public

record CorF2Result (g : Fun2) (x v : Term) : Set where
  constructor mkCorF2
  field
    result2 : Term
    proof2  : Deriv (atomic (eqn (ap1 cor (ap2 g x v)) result2))
open CorF2Result public

------------------------------------------------------------------------
-- Trivial fallback (used at non-canonical inputs).

trivialF1 : (f : Fun1) (x : Term) -> CorF1Result f x
trivialF1 f x = mkCorF1 (ap1 cor (ap1 f x)) (axRefl (ap1 cor (ap1 f x)))

trivialF2 : (g : Fun2) (x v : Term) -> CorF2Result g x v
trivialF2 g x v = mkCorF2 (ap1 cor (ap2 g x v)) (axRefl (ap1 cor (ap2 g x v)))

------------------------------------------------------------------------
-- Cor on O reduces to O (via axRecLf, since cor = Rec stepCor).

corO_eq : Deriv (atomic (eqn (ap1 cor O) O))
corO_eq = axRecLf stepCor

------------------------------------------------------------------------
-- Mutual recursion.

corF1 : (f : Fun1) (x : Term) -> CorF1Result f x
corF2 : (g : Fun2) (x v : Term) -> CorF2Result g x v

------------------------------------------------------------------------
-- corF1 cases.

-- I: ap1 I x = x ; cor (I x) = cor x.
corF1 I x =
  mkCorF1 (ap1 cor x) (cong1 cor (axI x))

-- Z: ap1 Z x = O ; cor (Z x) = cor O = O.
corF1 Z x =
  mkCorF1 O (ruleTrans (cong1 cor (axZ x)) corO_eq)

-- Fst: shape-dispatched on x.
corF1 Fst O =
  mkCorF1 O (ruleTrans (cong1 cor axFstLf) corO_eq)
corF1 Fst (ap2 Pair a b) =
  mkCorF1 (ap1 cor a) (corOfFstPair a b)
corF1 Fst (var n)        = trivialF1 Fst (var n)
corF1 Fst (ap1 f' x')    = trivialF1 Fst (ap1 f' x')
corF1 Fst (ap2 Const a b)      = trivialF1 Fst (ap2 Const a b)
corF1 Fst (ap2 (Lift _) a b)   = trivialF1 Fst (ap2 (Lift _) a b)
corF1 Fst (ap2 (Post _ _) a b) = trivialF1 Fst (ap2 (Post _ _) a b)
corF1 Fst (ap2 (Fan _ _ _) a b) = trivialF1 Fst (ap2 (Fan _ _ _) a b)
corF1 Fst (ap2 IfLf a b)       = trivialF1 Fst (ap2 IfLf a b)
corF1 Fst (ap2 TreeEq a b)     = trivialF1 Fst (ap2 TreeEq a b)
corF1 Fst (ap2 (treeRec _ _) a b) = trivialF1 Fst (ap2 (treeRec _ _) a b)

-- Snd: shape-dispatched.
corF1 Snd O =
  mkCorF1 O (ruleTrans (cong1 cor axSndLf) corO_eq)
corF1 Snd (ap2 Pair a b) =
  mkCorF1 (ap1 cor b) (corOfSndPair a b)
corF1 Snd (var n)        = trivialF1 Snd (var n)
corF1 Snd (ap1 f' x')    = trivialF1 Snd (ap1 f' x')
corF1 Snd (ap2 Const a b)      = trivialF1 Snd (ap2 Const a b)
corF1 Snd (ap2 (Lift _) a b)   = trivialF1 Snd (ap2 (Lift _) a b)
corF1 Snd (ap2 (Post _ _) a b) = trivialF1 Snd (ap2 (Post _ _) a b)
corF1 Snd (ap2 (Fan _ _ _) a b) = trivialF1 Snd (ap2 (Fan _ _ _) a b)
corF1 Snd (ap2 IfLf a b)       = trivialF1 Snd (ap2 IfLf a b)
corF1 Snd (ap2 TreeEq a b)     = trivialF1 Snd (ap2 TreeEq a b)
corF1 Snd (ap2 (treeRec _ _) a b) = trivialF1 Snd (ap2 (treeRec _ _) a b)

-- Comp f g: ap1 (Comp f g) x = ap1 f (ap1 g x).
-- cor (Comp f g x) = cor (f (g x)) = corF1 f (g x).
corF1 (Comp f g) x =
  let
    sub : CorF1Result f (ap1 g x)
    sub = corF1 f (ap1 g x)

    bridge : Deriv (atomic (eqn (ap1 cor (ap1 (Comp f g) x))
                                 (ap1 cor (ap1 f (ap1 g x)))))
    bridge = cong1 cor (axComp f g x)
  in mkCorF1 (result sub) (ruleTrans bridge (proof sub))

-- Comp2 h f g: ap1 (Comp2 h f g) x = ap2 h (ap1 f x) (ap1 g x).
-- cor → corF2 h (f x) (g x).
corF1 (Comp2 h f g) x =
  let
    sub : CorF2Result h (ap1 f x) (ap1 g x)
    sub = corF2 h (ap1 f x) (ap1 g x)

    bridge : Deriv (atomic (eqn (ap1 cor (ap1 (Comp2 h f g) x))
                                 (ap1 cor (ap2 h (ap1 f x) (ap1 g x)))))
    bridge = cong1 cor (axComp2 h f g x)
  in mkCorF1 (result2 sub) (ruleTrans bridge (proof2 sub))

-- Rec is now an Agda function ( Rec s = Comp2 (treeRec Z s) Z I ); the
-- old per-Rec dispatch clauses are unreachable / not pattern-matchable
-- and have been deleted.  The Comp2 / treeRec sub-cases handle the
-- structure transparently when needed by callers.

------------------------------------------------------------------------
-- corF2 cases.

-- Pair: cor (Pair a b) = mkAp2T (codeF2 Pair) (cor a) (cor b).  corOfPair.
corF2 Pair a b =
  mkCorF2 (mkAp2T (reify (codeF2 Pair)) (ap1 cor a) (ap1 cor b))
          (corOfPair a b)

-- Const: ap2 Const a b = a.  cor (Const a b) = cor a.
corF2 Const a b =
  mkCorF2 (ap1 cor a) (cong1 cor (axConst a b))

-- Lift f: ap2 (Lift f) a b = ap1 f a.  Recurse into corF1 f a.
corF2 (Lift f) a b =
  let
    sub : CorF1Result f a
    sub = corF1 f a

    bridge : Deriv (atomic (eqn (ap1 cor (ap2 (Lift f) a b))
                                 (ap1 cor (ap1 f a))))
    bridge = cong1 cor (axLift f a b)
  in mkCorF2 (result sub) (ruleTrans bridge (proof sub))

-- Post f h: ap2 (Post f h) a b = ap1 f (ap2 h a b).  Recurse on f at (h a b).
corF2 (Post f h) a b =
  let
    sub : CorF1Result f (ap2 h a b)
    sub = corF1 f (ap2 h a b)

    bridge : Deriv (atomic (eqn (ap1 cor (ap2 (Post f h) a b))
                                 (ap1 cor (ap1 f (ap2 h a b)))))
    bridge = cong1 cor (axPost f h a b)
  in mkCorF2 (result sub) (ruleTrans bridge (proof sub))

-- Fan h1 h2 h: ap2 (Fan h1 h2 h) a b = ap2 h (ap2 h1 a b) (ap2 h2 a b).
corF2 (Fan h1 h2 h) a b =
  let
    h1ab : Term
    h1ab = ap2 h1 a b

    h2ab : Term
    h2ab = ap2 h2 a b

    sub : CorF2Result h h1ab h2ab
    sub = corF2 h h1ab h2ab

    bridge : Deriv (atomic (eqn (ap1 cor (ap2 (Fan h1 h2 h) a b))
                                 (ap1 cor (ap2 h h1ab h2ab))))
    bridge = cong1 cor (axFan h1 h2 h a b)
  in mkCorF2 (result2 sub) (ruleTrans bridge (proof2 sub))

-- IfLf: shape-dispatched on (a, b).
--   axIfLfLL : IfLf O O = O.
--   axIfLfL  : IfLf O (Pair c d) = c.
--   axIfLfNL : IfLf (Pair x y) O = O.
--   axIfLfN  : IfLf (Pair x y) (Pair c d) = d.
corF2 IfLf O O =
  mkCorF2 O (ruleTrans (cong1 cor axIfLfLL) corO_eq)
corF2 IfLf O (ap2 Pair c d) =
  mkCorF2 (ap1 cor c) (cong1 cor (axIfLfL c d))
corF2 IfLf O (var n)            = trivialF2 IfLf O (var n)
corF2 IfLf O (ap1 f' x')        = trivialF2 IfLf O (ap1 f' x')
corF2 IfLf O (ap2 Const a b)         = trivialF2 IfLf O (ap2 Const a b)
corF2 IfLf O (ap2 (Lift _) a b)      = trivialF2 IfLf O (ap2 (Lift _) a b)
corF2 IfLf O (ap2 (Post _ _) a b)    = trivialF2 IfLf O (ap2 (Post _ _) a b)
corF2 IfLf O (ap2 (Fan _ _ _) a b)   = trivialF2 IfLf O (ap2 (Fan _ _ _) a b)
corF2 IfLf O (ap2 IfLf a b)          = trivialF2 IfLf O (ap2 IfLf a b)
corF2 IfLf O (ap2 TreeEq a b)        = trivialF2 IfLf O (ap2 TreeEq a b)
corF2 IfLf O (ap2 (treeRec _ _) a b) = trivialF2 IfLf O (ap2 (treeRec _ _) a b)
corF2 IfLf (ap2 Pair x y) O =
  mkCorF2 O (ruleTrans (cong1 cor (axIfLfNL x y)) corO_eq)
corF2 IfLf (ap2 Pair x y) (ap2 Pair c d) =
  mkCorF2 (ap1 cor d) (cong1 cor (axIfLfN x y c d))
corF2 IfLf (ap2 Pair x y) (var n)            = trivialF2 IfLf (ap2 Pair x y) (var n)
corF2 IfLf (ap2 Pair x y) (ap1 f' x')        = trivialF2 IfLf (ap2 Pair x y) (ap1 f' x')
corF2 IfLf (ap2 Pair x y) (ap2 Const a b)         = trivialF2 IfLf (ap2 Pair x y) (ap2 Const a b)
corF2 IfLf (ap2 Pair x y) (ap2 (Lift _) a b)      = trivialF2 IfLf (ap2 Pair x y) (ap2 (Lift _) a b)
corF2 IfLf (ap2 Pair x y) (ap2 (Post _ _) a b)    = trivialF2 IfLf (ap2 Pair x y) (ap2 (Post _ _) a b)
corF2 IfLf (ap2 Pair x y) (ap2 (Fan _ _ _) a b)   = trivialF2 IfLf (ap2 Pair x y) (ap2 (Fan _ _ _) a b)
corF2 IfLf (ap2 Pair x y) (ap2 IfLf a b)          = trivialF2 IfLf (ap2 Pair x y) (ap2 IfLf a b)
corF2 IfLf (ap2 Pair x y) (ap2 TreeEq a b)        = trivialF2 IfLf (ap2 Pair x y) (ap2 TreeEq a b)
corF2 IfLf (ap2 Pair x y) (ap2 (treeRec _ _) a b) = trivialF2 IfLf (ap2 Pair x y) (ap2 (treeRec _ _) a b)
corF2 IfLf (var n)        v                  = trivialF2 IfLf (var n) v
corF2 IfLf (ap1 f' x')    v                  = trivialF2 IfLf (ap1 f' x') v
corF2 IfLf (ap2 Const a b)        v          = trivialF2 IfLf (ap2 Const a b) v
corF2 IfLf (ap2 (Lift _) a b)     v          = trivialF2 IfLf (ap2 (Lift _) a b) v
corF2 IfLf (ap2 (Post _ _) a b)   v          = trivialF2 IfLf (ap2 (Post _ _) a b) v
corF2 IfLf (ap2 (Fan _ _ _) a b)  v          = trivialF2 IfLf (ap2 (Fan _ _ _) a b) v
corF2 IfLf (ap2 IfLf a b)         v          = trivialF2 IfLf (ap2 IfLf a b) v
corF2 IfLf (ap2 TreeEq a b)       v          = trivialF2 IfLf (ap2 TreeEq a b) v
corF2 IfLf (ap2 (treeRec _ _) a b) v         = trivialF2 IfLf (ap2 (treeRec _ _) a b) v

-- TreeEq: shape-dispatched on (a, b).  Uses axTreeEq{LL, LN, NL, NN}.
-- For NN inputs, axTreeEqNN gives an IfLf-form result that further
-- evaluates via TreeEq on smaller pairs.  We don't recurse on (a1, b1)
-- and (a2, b2) here -- we just emit the IfLf-form Term (which is
-- structurally smaller and the consumer can simplify further).
corF2 TreeEq O O =
  mkCorF2 O (ruleTrans (cong1 cor axTreeEqLL) corO_eq)
corF2 TreeEq O (ap2 Pair a b) =
  mkCorF2 (ap1 cor (ap2 Pair O O)) (cong1 cor (axTreeEqLN a b))
corF2 TreeEq O (var n)            = trivialF2 TreeEq O (var n)
corF2 TreeEq O (ap1 f' x')        = trivialF2 TreeEq O (ap1 f' x')
corF2 TreeEq O (ap2 Const a b)         = trivialF2 TreeEq O (ap2 Const a b)
corF2 TreeEq O (ap2 (Lift _) a b)      = trivialF2 TreeEq O (ap2 (Lift _) a b)
corF2 TreeEq O (ap2 (Post _ _) a b)    = trivialF2 TreeEq O (ap2 (Post _ _) a b)
corF2 TreeEq O (ap2 (Fan _ _ _) a b)   = trivialF2 TreeEq O (ap2 (Fan _ _ _) a b)
corF2 TreeEq O (ap2 IfLf a b)          = trivialF2 TreeEq O (ap2 IfLf a b)
corF2 TreeEq O (ap2 TreeEq a b)        = trivialF2 TreeEq O (ap2 TreeEq a b)
corF2 TreeEq O (ap2 (treeRec _ _) a b) = trivialF2 TreeEq O (ap2 (treeRec _ _) a b)
corF2 TreeEq (ap2 Pair a b) O =
  mkCorF2 (ap1 cor (ap2 Pair O O)) (cong1 cor (axTreeEqNL a b))
corF2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2) =
  mkCorF2 (ap1 cor (ap2 IfLf (ap2 TreeEq a1 b1)
                              (ap2 Pair (ap2 TreeEq a2 b2)
                                        (ap2 Pair O O))))
          (cong1 cor (axTreeEqNN a1 a2 b1 b2))
corF2 TreeEq (ap2 Pair x y) (var n)         = trivialF2 TreeEq (ap2 Pair x y) (var n)
corF2 TreeEq (ap2 Pair x y) (ap1 f' x')     = trivialF2 TreeEq (ap2 Pair x y) (ap1 f' x')
corF2 TreeEq (ap2 Pair x y) (ap2 Const a b)         = trivialF2 TreeEq (ap2 Pair x y) (ap2 Const a b)
corF2 TreeEq (ap2 Pair x y) (ap2 (Lift _) a b)      = trivialF2 TreeEq (ap2 Pair x y) (ap2 (Lift _) a b)
corF2 TreeEq (ap2 Pair x y) (ap2 (Post _ _) a b)    = trivialF2 TreeEq (ap2 Pair x y) (ap2 (Post _ _) a b)
corF2 TreeEq (ap2 Pair x y) (ap2 (Fan _ _ _) a b)   = trivialF2 TreeEq (ap2 Pair x y) (ap2 (Fan _ _ _) a b)
corF2 TreeEq (ap2 Pair x y) (ap2 IfLf a b)          = trivialF2 TreeEq (ap2 Pair x y) (ap2 IfLf a b)
corF2 TreeEq (ap2 Pair x y) (ap2 TreeEq a b)        = trivialF2 TreeEq (ap2 Pair x y) (ap2 TreeEq a b)
corF2 TreeEq (ap2 Pair x y) (ap2 (treeRec _ _) a b) = trivialF2 TreeEq (ap2 Pair x y) (ap2 (treeRec _ _) a b)
corF2 TreeEq (var n) v                              = trivialF2 TreeEq (var n) v
corF2 TreeEq (ap1 f' x') v                          = trivialF2 TreeEq (ap1 f' x') v
corF2 TreeEq (ap2 Const a b) v                      = trivialF2 TreeEq (ap2 Const a b) v
corF2 TreeEq (ap2 (Lift _) a b) v                   = trivialF2 TreeEq (ap2 (Lift _) a b) v
corF2 TreeEq (ap2 (Post _ _) a b) v                 = trivialF2 TreeEq (ap2 (Post _ _) a b) v
corF2 TreeEq (ap2 (Fan _ _ _) a b) v                = trivialF2 TreeEq (ap2 (Fan _ _ _) a b) v
corF2 TreeEq (ap2 IfLf a b) v                       = trivialF2 TreeEq (ap2 IfLf a b) v
corF2 TreeEq (ap2 TreeEq a b) v                     = trivialF2 TreeEq (ap2 TreeEq a b) v
corF2 TreeEq (ap2 (treeRec _ _) a b) v              = trivialF2 TreeEq (ap2 (treeRec _ _) a b) v

-- RecP is now an Agda function ( RecP s = treeRec Z s ); see the
-- treeRec branch below for how callers see RecP-applications at runtime.

-- treeRec f s: shape-dispatched on the second arg.  Until  axRLf, axRNd
-- are added to BRA.Deriv, all  treeRec  cases are trivial fall-throughs.
-- See BRA/NEXT-SESSION-R-UNIFICATION.md.
corF2 (treeRec f s) p O                     = trivialF2 (treeRec f s) p O
corF2 (treeRec f s) p (ap2 Pair a b)        = trivialF2 (treeRec f s) p (ap2 Pair a b)
corF2 (treeRec f s) p (var n)               = trivialF2 (treeRec f s) p (var n)
corF2 (treeRec f s) p (ap1 f' x')           = trivialF2 (treeRec f s) p (ap1 f' x')
corF2 (treeRec f s) p (ap2 Const a b)       = trivialF2 (treeRec f s) p (ap2 Const a b)
corF2 (treeRec f s) p (ap2 (Lift _) a b)    = trivialF2 (treeRec f s) p (ap2 (Lift _) a b)
corF2 (treeRec f s) p (ap2 (Post _ _) a b)  = trivialF2 (treeRec f s) p (ap2 (Post _ _) a b)
corF2 (treeRec f s) p (ap2 (Fan _ _ _) a b) = trivialF2 (treeRec f s) p (ap2 (Fan _ _ _) a b)
corF2 (treeRec f s) p (ap2 IfLf a b)        = trivialF2 (treeRec f s) p (ap2 IfLf a b)
corF2 (treeRec f s) p (ap2 TreeEq a b)      = trivialF2 (treeRec f s) p (ap2 TreeEq a b)
corF2 (treeRec f s) p (ap2 (treeRec _ _) a b) = trivialF2 (treeRec f s) p (ap2 (treeRec _ _) a b)
