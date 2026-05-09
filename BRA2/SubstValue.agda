{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SubstValue -- substitution helpers on value-shape terms.
--
-- For the eventual  StepCombinerFromStep  derivation (the lemma
-- that converts a raw indBT-step premise into a value-conditioned
-- StepCombiner), we need:
--
--   (1) values are closed:  IsValue t -> maxVarT t = 0 .
--   (2) subst on a value is identity:  IsValue t -> subst v a t = t .
--   (3) subst v a (var v) = a  (one-liner via natEq_refl).
--   (4) subst v a (var w) = var w  when  natEq w v = false .
--
-- (3) and (4) are utilities used to align types after  ruleInst
-- applications inside the proof.
--
-- Together these allow the eventual StepCombiner derivation to push
-- through  subst  on the substituent term  ap2 Pair a b  (a, b values),
-- which behaves as identity at the corresponding variable positions.

module BRA2.SubstValue where

open import BRA2.Base
open import BRA2.Term
open import BRA2.MaxVar

------------------------------------------------------------------------
-- (1) Values are closed:  maxVarT t = 0  for IsValue t.

maxVarT_value : (t : Term) -> IsValue t -> Eq (maxVarT t) zero
maxVarT_value .O                 valO              = refl
maxVarT_value .(ap2 Pair a b)    (valNd a b va vb) =
  -- maxVarT (ap2 Pair a b) = natMax (maxVarT a) (maxVarT b).
  -- By IH:  maxVarT a = 0  and  maxVarT b = 0 .  natMax 0 0 = 0.
  let ihA = maxVarT_value a va
      ihB = maxVarT_value b vb
  in eqTrans (eqCong (\ x -> natMax x (maxVarT b)) ihA)
              (eqCong (natMax zero)                ihB)

------------------------------------------------------------------------
-- (2) Subst on a value is identity.

subst_value :
  (v : Nat) (a : Term) (t : Term) ->
  IsValue t ->
  Eq (subst v a t) t
subst_value v a t vt =
  subst_aboveMax v a t
    (eqSubst (Geq v) (eqSym (maxVarT_value t vt)) (geqZero v))

------------------------------------------------------------------------
-- (3) subst v a (var v) = a.

subst_var_self : (v : Nat) (a : Term) -> Eq (subst v a (var v)) a
subst_var_self v a =
  -- subst v a (var v) = boolCase (natEq v v) a (var v).
  -- natEq_refl : natEq v v = true.
  eqCong (\ b -> boolCase b a (var v)) (natEq_refl v)

------------------------------------------------------------------------
-- (4) subst v a (var w) = var w  when  natEq w v = false .

subst_var_diff :
  (v w : Nat) (a : Term) ->
  Eq (natEq w v) false ->
  Eq (subst v a (var w)) (var w)
subst_var_diff v w a neq =
  -- subst v a (var w) = boolCase (natEq w v) a (var w).
  -- natEq w v = false  =>  result = var w.
  eqCong (\ b -> boolCase b a (var w)) neq

------------------------------------------------------------------------
-- Composite: subst v a applied to the indBT step's substituent
-- ap2 Pair (var v) (var w) with w != v gives ap2 Pair a (var w).

subst_pair_var_var :
  (v w : Nat) (a : Term) ->
  Eq (natEq w v) false ->
  Eq (subst v a (ap2 Pair (var v) (var w))) (ap2 Pair a (var w))
subst_pair_var_var v w a neq =
  -- subst v a (ap2 Pair (var v) (var w))
  --   = ap2 (substF2 v a Pair) (subst v a (var v)) (subst v a (var w))
  --   = ap2 Pair a (var w)                    [by Fun2_closed, subst_var_self, subst_var_diff]
  let lhs1 : Eq (subst v a (var v)) a
      lhs1 = subst_var_self v a
      lhs2 : Eq (subst v a (var w)) (var w)
      lhs2 = subst_var_diff v w a neq
  in eqCong2 (ap2 Pair) lhs1 lhs2

-- Companion: subst v a applied to ap2 Pair a' (var w) where a' is a value
-- (so subst v a a' = a') gives ap2 Pair a' (var w).

subst_pair_value_var :
  (v w : Nat) (a a' : Term) ->
  IsValue a' ->
  Eq (natEq w v) false ->
  Eq (subst v a (ap2 Pair a' (var w))) (ap2 Pair a' (var w))
subst_pair_value_var v w a a' va' neq =
  let lhs1 = subst_value v a a' va'
      lhs2 = subst_var_diff v w a neq
  in eqCong2 (ap2 Pair) lhs1 lhs2
