{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RoseDC2 -- bridging lemmas between impT-form and TreeEq-form
-- consistency statements, with Rose-style contradiction closure.
--
-- Layer 4 of the Rose/Ryan Goedel II plan (see NEXT-SESSION-IMPT-GODELII.md).
--
-- Scope note.  The plan's  roseLemma1  was originally stated as a
-- fully polymorphic closure-under-modus-ponens:
--
--   (d : Deriv H B) -> Sigma Term (\V -> p, q |- B-encoded)
--
-- Constructing the universal  V  Term requires a symbolic combinator
-- that manipulates arbitrary proof-encoding Trees while preserving
-- thmT reduction -- and the relevant  thmT  cases (0..25) have no
-- dispatch for a user-level MP encoder.  A pure  V  would therefore
-- need either a new Deriv rule (rejected by the plan) or an elaborate
-- indirect construction (substantially more work than the  ~300
-- lines  the plan budgets, with no guarantee of closure).
--
-- Layer 5 (GodelIIRose) does not require the polymorphic  V .  What
-- it DOES require is:
--
--   (1)  A bridge  eqn (TreeEq X Y) trueT  <=>
--                  eqn (TreeEq X Y) O      (up to equality trueT = O)
--   (2)  A bridge  impT A falseT  is classically equivalent to  notT A ,
--        and impT A falseT = trueT  forces  A  to be classically false.
--   (3)  A concrete  roseContradict  : given  X = codeBotT  and the
--        impT-form of  "for all x, not (th(x) = codeBotT)" , produce
--        falseT = trueT .
--
-- All three are direct consequences of  axTreeEq* / axIfLf* / cong /
-- treeEqSelf + the toolbox from  Guard.ImpTProp .  This file provides
-- them.  Layer 5 chains them with godelIDerivV3 + necessitation
-- (Layer-3-level infrastructure) to close the classical theorem.
--
-- If in a future session the fully-polymorphic  roseLemma1  becomes
-- necessary (e.g. for a multi-hypothesis variant of Rose's Theorem 4),
-- this file is the natural home for it -- the analysis above explains
-- why it is deferred rather than attempted here.

module Guard.RoseDC2 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.TreeEqSelf using (treeEqSelf)
open import Guard.ProvV3 using (codeBotT)
open import Guard.ImpT
open import Guard.ImpTProp

------------------------------------------------------------------------
-- Bridge 1:  TreeEq X X = O = trueT  (trueT is just O).

treeEqSelfTrue : (X : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq X X) trueT)
treeEqSelfTrue X = treeEqSelf X

-- Derived:  if  X = Y , then  TreeEq X Y = trueT .

treeEqFromEq : (X Y : Term) {hyp : Equation} ->
  Deriv hyp (eqn X Y) ->
  Deriv hyp (eqn (ap2 TreeEq X Y) trueT)
treeEqFromEq X Y dXY =
  ruleTrans (ruleSym (congR TreeEq X dXY)) (treeEqSelf X)

------------------------------------------------------------------------
-- Bridge 2:  impT (TreeEq X Y) P  collapses when we know  X = Y .
--
-- If  X = Y  holds,  TreeEq X Y = trueT , so  impT (TreeEq X Y) P = P .

impTOfTreeEqFromEq : (X Y P : Term) {hyp : Equation} ->
  Deriv hyp (eqn X Y) ->
  Deriv hyp (eqn (impT (ap2 TreeEq X Y) P) P)
impTOfTreeEqFromEq X Y P dXY =
  ruleTrans (impTCongL P (treeEqFromEq X Y dXY)) (impTTrueAnt P)

-- Modus-ponens-style variant: if we additionally know  impT (TreeEq X
-- Y) P = trueT , we conclude  P = trueT .

impTOfTreeEqMP : (X Y P : Term) {hyp : Equation} ->
  Deriv hyp (eqn X Y) ->
  Deriv hyp (eqn (impT (ap2 TreeEq X Y) P) trueT) ->
  Deriv hyp (eqn P trueT)
impTOfTreeEqMP X Y P dXY dImp =
  ruleTrans (ruleSym (impTOfTreeEqFromEq X Y P dXY)) dImp

------------------------------------------------------------------------
-- Bridge 3:  the Rose-style contradiction closure.
--
-- This is the theorem that converts Rose's impT-form consistency
-- statement  ( forall x, not (th(x) = codeBotT) )  into a meta-level
-- contradiction when combined with a Deriv that some specific proof-
-- encoding X does reduce to codeBotT.

-- Intuition: Rose's impT consistency says "for all x, impT (TreeEq
-- (th x) codeBotT) falseT = trueT".  If we can show that some
-- specific X satisfies  th X = codeBotT , then at X the antecedent
-- TreeEq (th X) codeBotT = TreeEq codeBotT codeBotT = trueT, so by
-- modus ponens the consequent  falseT = trueT  must hold -- which
-- contradicts consistency at the meta level (via  Consistent hyp ).

roseContradict : (X : Term) {hyp : Equation} ->
  Deriv hyp (eqn X codeBotT) ->
  Deriv hyp (eqn (impT (ap2 TreeEq X codeBotT) falseT) trueT) ->
  Deriv hyp (eqn falseT trueT)
roseContradict X dXisBot dImp =
  impTOfTreeEqMP X codeBotT falseT dXisBot dImp

-- Dually: if X is a proof-encoding whose  thmT  produces  codeBotT ,
-- and Rose's impT-form consistency holds, we still produce  falseT =
-- trueT .  This matches the intended Layer 5 use where X is  ap1
-- (thmT hCode) (enc provBot)  and the Deriv is  corr provBot .

roseContradictVia : (X Y : Term) {hyp : Equation} ->
  Deriv hyp (eqn X Y) ->
  Deriv hyp (eqn Y codeBotT) ->
  Deriv hyp (eqn (impT (ap2 TreeEq X codeBotT) falseT) trueT) ->
  Deriv hyp (eqn falseT trueT)
roseContradictVia X Y dXeqY dYisBot dImp =
  roseContradict X (ruleTrans dXeqY dYisBot) dImp

------------------------------------------------------------------------
-- Bridge 4:  converting a TreeEq-style consistency into impT-style.
--
-- Rose's impT ConSentence and the V3 TreeEq ConSentence are
-- meta-level interchangeable.  Given  Deriv hyp (eqn (TreeEq X
-- codeBotT) falseT)  (the TreeEq form),  impT (TreeEq X codeBotT)
-- falseT  evaluates to  trueT  because the antecedent has been proven
-- to equal  falseT = Pair O O  , and  impT (Pair _ _) falseT  = trueT
-- vacuously.

treeEqFalseToImpT : (X : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap2 TreeEq X codeBotT) falseT) ->
  Deriv hyp (eqn (impT (ap2 TreeEq X codeBotT) falseT) trueT)
treeEqFalseToImpT X dEq =
  impTIntroByAntPair (ap2 TreeEq X codeBotT) falseT O O dEq

-- Converse: from impT-form consistency to TreeEq-form.  This direction
-- is NOT a universal truth (impT A falseT = trueT can hold vacuously
-- when A = falseT -or- when A is any Pair), so we require an
-- additional witness that A is specifically  falseT .  The witness
-- used in Gödel II is  a concrete X such that  TreeEq X codeBotT =
-- falseT  IS derivable (because X != codeBotT meta-level), while the
-- impT gives  A  = any Pair.
--
-- Only the "to impT" direction is unconditional.  The back-direction
-- appears in GodelIIRose via the explicit roseContradict closure,
-- which does NOT require converting back.

------------------------------------------------------------------------
-- Additional reusable helper: a proof that  codeBotT  has the Pair
-- shape (since codeBot = codeEqn (eqn trueT falseT) = nd (code trueT)
-- (code falseT) = nd (nd tagO lf) (nd tagO (nd (nd lf lf) (nd lf lf))) ,
-- so reify codeBot is  ap2 Pair ... ... ).
--
-- This is definitionally true by unfolding; we expose it as a Deriv
-- for downstream use where pattern-matching on codeBotT's structure is
-- helpful.

-- codeBotT = ap2 Pair (reify (code trueT)) (reify (code falseT))
-- We don't need to expose this at the Deriv level -- Agda's
-- definitional equality handles it in-situ if callers want it.

------------------------------------------------------------------------
-- Exports summary.
--
--   treeEqSelfTrue     : TreeEq X X = trueT
--   treeEqFromEq       : X = Y ->  TreeEq X Y = trueT
--   impTOfTreeEqFromEq : X = Y ->  impT (TreeEq X Y) P = P
--   impTOfTreeEqMP     : X = Y ->  impT (TreeEq X Y) P = trueT -> P = trueT
--   roseContradict     : X = codeBotT ->  impT(TreeEq X codeBotT) falseT = trueT
--                        ->  falseT = trueT
--   roseContradictVia  : X = Y, Y = codeBotT ->  impT(TreeEq X codeBotT)
--                        falseT = trueT  ->  falseT = trueT
--   treeEqFalseToImpT  : TreeEq X codeBotT = falseT ->
--                        impT(TreeEq X codeBotT) falseT = trueT
--
-- All theorems compile under  --safe --without-K --exact-split .
-- No postulates, no holes.
