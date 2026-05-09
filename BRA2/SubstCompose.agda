{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.SubstCompose -- substitution composition lemmas under
-- freshness.
--
-- Foundational for the indBT-elimination at closed instances:
-- to instantiate the indBT step premise via  ruleInst v1 a , we need
-- to know that
--
--    substEq v1 a (substEq zero (var v1) e)  =  substEq zero a e
--
-- when  v1  is fresh in  e  (i.e.,  v1 >= maxVarT  of every term in
-- e ).  Provided as  substEq_compose_fresh ; the underlying term-
-- level lemma  substT_compose_fresh  is the engine.
--
-- The "fresh" condition is expressed as  Geq v (maxVarT t)  :
-- maxVarT  is one more than the highest free-variable index, so
-- v >= maxVarT t  forces  v  not to occur as any  var n  in  t .
--
-- See BRA2.MaxVar for the underlying  Geq  /  maxVarT  /
-- subst_aboveMax  infrastructure used here.

module BRA2.SubstCompose where

open import BRA2.Base
open import BRA2.Term
open import BRA2.MaxVar
open import BRA2.SubstClosure using (Fun1_closed ; Fun2_closed)
open import BRA2.NatMaxLemmas using (natMaxLE_L ; natMaxLE_R ; NatLE)

------------------------------------------------------------------------
-- Geq splits through natMax: if v >= natMax a b, then v >= a and v >= b.

geq_natMax_split :
  {v a b : Nat} ->
  Geq v (natMax a b) ->
  Sigma (Geq v a) (\ _ -> Geq v b)
geq_natMax_split {v} {a} {b} ge =
  mkSigma (geqTrans ge (natMax_geqL a b))
          (geqTrans ge (natMax_geqR a b))

------------------------------------------------------------------------
-- Term-level composition lemma:
--
--    subst v a (subst 0 (var v) t) = subst 0 a t
--
-- when v is fresh in t (Geq v (maxVarT t)).
--
-- Proof: structural induction on t.
--   * O          : both sides are O.
--   * var zero   : LHS reduces to subst v a (var v) = a; RHS = a.
--                  Use natEq_refl v.
--   * var (suc m): LHS reduces to subst v a (var (suc m)).  Need
--                  natEq (suc m) v = false; from ge : Geq v (suc (suc m))
--                  via natEq_false_aboveSuc.
--   * ap1 f t'   : functor closure (Fun1_closed twice) reduces both
--                  sides to ap1 f, recurse on t'.
--   * ap2 g t1 t2: same as ap1 with Fun2_closed and natMax-split for ge.

substT_compose_fresh :
  (v : Nat) (a t : Term) ->
  Geq v (maxVarT t) ->
  Eq (subst v a (subst zero (var v) t)) (subst zero a t)

substT_compose_fresh _ _ O           _  = refl

-- var zero: both substs hit and replace.
substT_compose_fresh v a (var zero) _ =
  -- subst zero (var v) (var zero) = var v.
  -- subst v a (var v) = boolCase (natEq v v) a (var v).
  -- Need: this = a.  Use natEq_refl v.
  eqCong (\ b -> boolCase b a (var v)) (natEq_refl v)

-- var (suc m): subst zero (var v) leaves it (var (suc m)); then subst
-- v a (var (suc m)) needs natEq (suc m) v = false from freshness.
substT_compose_fresh v a (var (suc m)) ge =
  eqCong (\ b -> boolCase b a (var (suc m)))
          (natEq_false_aboveSuc (suc m) v ge)

-- ap1 f t' : reduce functors via Fun1_closed; recurse on t'.
substT_compose_fresh v a (ap1 f t) ge =
  let -- Both sides' functors reduce to f.
      eqF : Eq (substF1 v a (substF1 zero (var v) f)) (substF1 zero a f)
      eqF = eqTrans (eqCong (substF1 v a) (Fun1_closed zero (var v) f))
                     (eqTrans (Fun1_closed v a f)
                              (eqSym (Fun1_closed zero a f)))
      ih = substT_compose_fresh v a t ge
  in eqTrans (eqCong (\ F -> ap1 F (subst v a (subst zero (var v) t))) eqF)
              (eqCong (\ T -> ap1 (substF1 zero a f) T) ih)

-- ap2 g t1 t2: same pattern with Fun2_closed and natMax-split.
substT_compose_fresh v a (ap2 g t1 t2) ge =
  let gePair = geq_natMax_split {v} {maxVarT t1} {maxVarT t2} ge
      ge1    = fst gePair
      ge2    = snd gePair
      eqG : Eq (substF2 v a (substF2 zero (var v) g)) (substF2 zero a g)
      eqG = eqTrans (eqCong (substF2 v a) (Fun2_closed zero (var v) g))
                     (eqTrans (Fun2_closed v a g)
                              (eqSym (Fun2_closed zero a g)))
      ih1 = substT_compose_fresh v a t1 ge1
      ih2 = substT_compose_fresh v a t2 ge2
  in eqTrans
       (eqCong (\ G -> ap2 G (subst v a (subst zero (var v) t1))
                              (subst v a (subst zero (var v) t2))) eqG)
       (eqTrans
         (eqCong (\ T1 -> ap2 (substF2 zero a g) T1
                                (subst v a (subst zero (var v) t2))) ih1)
         (eqCong (\ T2 -> ap2 (substF2 zero a g) (subst zero a t1) T2) ih2))

------------------------------------------------------------------------
-- Equation-level: maxVarEq and substEq_compose_fresh.

maxVarEq : Equation -> Nat
maxVarEq (eqn l r) = natMax (maxVarT l) (maxVarT r)

substEq_compose_fresh :
  (v : Nat) (a : Term) (e : Equation) ->
  Geq v (maxVarEq e) ->
  Eq (substEq v a (substEq zero (var v) e)) (substEq zero a e)
substEq_compose_fresh v a (eqn l r) ge =
  let gePair = geq_natMax_split {v} {maxVarT l} {maxVarT r} ge
      geL    = fst gePair
      geR    = snd gePair
      ihL    = substT_compose_fresh v a l geL
      ihR    = substT_compose_fresh v a r geR
  in eqCong2 eqn ihL ihR
