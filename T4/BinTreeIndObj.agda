{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BinTreeIndObj -- OBJECT structural reconstruction for coded binary
-- trees, the first brick of the internal (Deriv + ruleIndNat) structural
-- induction principle (attempt3 §14; the foundation BRA |- Con(T0) needs for
-- the internal-iteration triF).
--
-- TOP-DOWN / CONDITIONAL build (the ClashObj/HeadStab pattern): the single
-- genuinely-hard keystone -- SURJECTIVE CANTOR PAIRING
--     surjPair :  Pair (Fst x) (Snd x) = x      (for arbitrary x)
-- -- is taken as an explicit module hypothesis (it is absent in the repo but,
-- per BRA3.Church L1717, provable via nu / triInv / m_2 with a long proof).
-- Everything here is GREEN modulo that one parameter, so the downstream
-- induction driver + triF preservation can be built and tested now, with the
-- keystone isolated as the only remaining debt.
--
-- What surjective pairing BUYS = constructor RECONSTRUCTION from a tag fact:
-- a code whose head tag is pinned to a constructor IS that constructor applied
-- to its projections.  This is what lets the per-constructor fold closure
-- equations (stated in binLeaf / binNode form, e.g. wf_node, triF closure
-- eqs) FIRE on an otherwise-opaque code during the induction step -- without
-- it, an opaque `d` cannot be put into  binNode .. ..  form.
--
--     reconLeaf : Fst d = natCode 1  ->  d = binLeaf (Snd d)
--     reconNode : Fst d = natCode 2  ->  d = binNode (lab d) (lft d) (rgt d)
--
-- where lab/lft/rgt are the iterated Cantor projections of the node payload.
-- No holes, no postulates (surjPair is an explicit hypothesis, not a
-- postulate); --safe --without-K --exact-split.

module T4.BinTreeIndObj where

open import T4.Base
open import T4.BinTree using ( binLeaf ; binNode )

------------------------------------------------------------------------
-- Iterated projections of a node code  d = Pair (tag) (Pair lab (Pair l r)).

lab : Term -> Term                       -- node label  = Fst (Snd d)
lab d = ap1 Fst (ap1 Snd d)

lft : Term -> Term                       -- left child  = Fst (Snd (Snd d))
lft d = ap1 Fst (ap1 Snd (ap1 Snd d))

rgt : Term -> Term                       -- right child = Snd (Snd (Snd d))
rgt d = ap1 Snd (ap1 Snd (ap1 Snd d))

------------------------------------------------------------------------
-- The conditional development, parametric in surjective pairing.

module Ind
  (surjPair : (x : Term) ->
              Deriv (eqF (ap2 Pair (ap1 Fst x) (ap1 Snd x)) x))
  where

  -- LEAF reconstruction: a tag-1 code is a leaf over its second projection.
  reconLeaf : (d : Term) ->
    Deriv (eqF (ap1 Fst d) (natCode 1)) ->
    Deriv (eqF d (binLeaf (ap1 Snd d)))
  reconLeaf d ht =
    ruleTrans (ruleSym (surjPair d))
              (congL Pair (ap1 Snd d) ht)

  -- NODE reconstruction: a tag-2 code is a node over its iterated projections.
  --   d = Pair (Fst d) (Snd d)                           [surjPair d]
  --     = Pair (natCode 2) (Snd d)                        [ht]
  --     = Pair (natCode 2) (Pair (lab d) (Snd (Snd d)))   [surjPair (Snd d)]
  --     = Pair (natCode 2) (Pair (lab d) (Pair (lft d) (rgt d)))
  --                                                        [surjPair (Snd (Snd d))]
  reconNode : (d : Term) ->
    Deriv (eqF (ap1 Fst d) (natCode 2)) ->
    Deriv (eqF d (binNode (lab d) (lft d) (rgt d)))
  reconNode d ht =
    ruleTrans (ruleSym (surjPair d))
      (ruleTrans (congL Pair (ap1 Snd d) ht)
        (ruleTrans
          (congR Pair (natCode 2) (ruleSym (surjPair (ap1 Snd d))))
          (congR Pair (natCode 2)
            (congR Pair (lab d)
              (ruleSym (surjPair (ap1 Snd (ap1 Snd d))))))))
