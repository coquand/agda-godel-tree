{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.IndBTContext0 -- one-hole proof contexts at the DerivT0
-- (open-fragment) level.
--
-- Mirrors  BRA2.IndBTContext  but with  DerivT0  derivations in the
-- "fixed non-hole premise" positions of binary frames.
--
-- Design: snoc-style inductive datatype.  Each non- hole  constructor
-- stacks ONE outer frame on top of an existing  IndBTContext0 .  The
-- outermost constructor is the LAST structural rule applied; plug0
-- walks from the outside inward, applying the result of plugging the
-- inner context first.
--
-- Used for the bounded-reduction handler:  given an indBT premises
-- in DerivT0 and an  IndBTContext0 (atomic e) bot , derive  DerivT0
-- bot  by composing  unfoldAtValue + stepCombinerFromStep  (yielding
-- DerivT0 (atomic (substEq 0 t e))  for the closing  t ) with
-- plug0 .  The closing  t  itself is extracted from the context by
-- a separate  extractDemand  function (next session).

module BRA2.IndBTContext0 where

open import BRA2.Base
open import BRA2.Term using (Term ; Equation ; eqn ; ap1 ; ap2 ; Pair ; Fun1 ; Fun2 ; substEq)
open import BRA2.Formula
import BRA2.DerivT0 as O
open import BRA2.DerivT0 using (DerivT0)

------------------------------------------------------------------------
-- IndBTContext0 P Q : "given a derivation of P, this context produces
-- a derivation of Q via a sequence of structural rules".
--
-- Constructors mirror the seven non-rank-introducing structural
-- rules of DerivT0; binary frames carry the fixed non-hole premise
-- as a  DerivT0  derivation.

data IndBTContext0 : Formula -> Formula -> Set where

  -- Empty context: hole at the root, output equals input.
  hole : (P : Formula) -> IndBTContext0 P P

  -- ruleSym wrapped around the inner context.
  sym : {P : Formula} {t u : Term} ->
        IndBTContext0 P (atomic (eqn t u)) ->
        IndBTContext0 P (atomic (eqn u t))

  -- ruleTrans with the hole on the LEFT premise (inner context produces
  -- (eqn t u); right premise (eqn u v) is fixed).
  transL : {P : Formula} {t u v : Term} ->
           IndBTContext0 P (atomic (eqn t u)) ->
           DerivT0 (atomic (eqn u v)) ->
           IndBTContext0 P (atomic (eqn t v))

  -- ruleTrans with the hole on the RIGHT premise.
  transR : {P : Formula} {t u v : Term} ->
           DerivT0 (atomic (eqn t u)) ->
           IndBTContext0 P (atomic (eqn u v)) ->
           IndBTContext0 P (atomic (eqn t v))

  -- cong1 around the inner context.
  cong1 : {P : Formula} (f : Fun1) {t u : Term} ->
          IndBTContext0 P (atomic (eqn t u)) ->
          IndBTContext0 P (atomic (eqn (ap1 f t) (ap1 f u)))

  -- congL around the inner context.
  congL : {P : Formula} (g : Fun2) {t u : Term} (x : Term) ->
          IndBTContext0 P (atomic (eqn t u)) ->
          IndBTContext0 P (atomic (eqn (ap2 g t x) (ap2 g u x)))

  -- congR around the inner context.
  congR : {P : Formula} (g : Fun2) (x : Term) {t u : Term} ->
          IndBTContext0 P (atomic (eqn t u)) ->
          IndBTContext0 P (atomic (eqn (ap2 g x t) (ap2 g x u)))

  -- mp with the hole on the LEFT (the implication side); argument
  -- premise is fixed.
  mpL : {P A B : Formula} ->
        IndBTContext0 P (A imp B) ->
        DerivT0 A ->
        IndBTContext0 P B

  -- mp with the hole on the RIGHT (the antecedent side); implication
  -- premise is fixed.
  mpR : {P A B : Formula} ->
        DerivT0 (A imp B) ->
        IndBTContext0 P A ->
        IndBTContext0 P B

  -- ruleInst wrapped around the inner context.
  --
  -- The output index R is a free Formula; an equality witness
  --   Eq (substF x t Q) R
  -- ties it to the actual substituted formula.  This is the (P1)
  -- design: by externalising the function-equation as a propositional
  -- equality, pattern-matching on  inst ... refl  against contexts
  -- with concrete output indices (e.g.  bot ) becomes possible
  -- (Agda's unifier no longer has to invert  substF x t Q ).
  inst : {P Q R : Formula} (x : Nat) (t : Term) ->
         IndBTContext0 P Q ->
         Eq (substF x t Q) R ->
         IndBTContext0 P R

------------------------------------------------------------------------
-- plug0 : apply the context's structural rules to a hole derivation.
--
-- Walks the context from the outside (outermost constructor) inward,
-- recursing on the inner context first and then applying the current
-- frame.

plug0 :
  {P Q : Formula} ->
  IndBTContext0 P Q ->
  DerivT0 P ->
  DerivT0 Q
plug0 (hole _)             d = d
plug0 (sym ctx)            d = O.ruleSym       (plug0 ctx d)
plug0 (transL ctx d2)      d = O.ruleTrans     (plug0 ctx d) d2
plug0 (transR d1 ctx)      d = O.ruleTrans  d1 (plug0 ctx d)
plug0 (cong1 f ctx)        d = O.cong1 f       (plug0 ctx d)
plug0 (congL g x ctx)      d = O.congL g x     (plug0 ctx d)
plug0 (congR g x ctx)      d = O.congR g x     (plug0 ctx d)
plug0 (mpL ctx d_arg)      d = O.mp            (plug0 ctx d) d_arg
plug0 (mpR d_imp ctx)      d = O.mp        d_imp (plug0 ctx d)
plug0 (inst x t ctx eqOut) d =
  eqSubst (\ F -> DerivT0 F) eqOut (O.ruleInst x t (plug0 ctx d))

------------------------------------------------------------------------
-- Smoke test: a one-frame  inst 0 t  context.
--
-- Given  d : DerivT0 (atomic e) , the context  inst 0 t (hole _)
-- yields  DerivT0 (atomic (substEq 0 t e)) .

singleInstCtx :
  (e : Equation) (t : Term) ->
  IndBTContext0 (atomic e) (atomic (substEq zero t e))
singleInstCtx e t = inst zero t (hole (atomic e)) refl

singleInstPlug :
  (e : Equation) (t : Term) ->
  DerivT0 (atomic e) ->
  DerivT0 (atomic (substEq zero t e))
singleInstPlug e t d = plug0 (singleInstCtx e t) d
