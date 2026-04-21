{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RoseEFun -- the e-function as a Fun1 combinator in the Term grammar.
--
-- Rose (1967) defines  e(y)  such that if y is the number of equation A=B
-- then e(y) is the number of A!=B.  In our tree encoding,
--
--   code (eqn A B) = nd (code A) (code B)                   [i.e., a Pair]
--   code (eqn (ap2 TreeEq A B) falseT) =
--       nd (code (ap2 TreeEq A B)) (code falseT)
--     = nd (nd tagAp2 (nd (codeF2 TreeEq) (nd (code A) (code B))))
--          (code falseT)
--
-- So  e  at the reified-code level takes
--
--   ap2 Pair a b
--
-- (representing nd aC bC) to
--
--   ap2 Pair (ap2 Pair (reify tagAp2)
--                      (ap2 Pair (reify (codeF2 TreeEq))
--                                (ap2 Pair a b)))
--            (reify codeFalse) .
--
-- This is expressible as a pure Fun1 combinator  eT  using
-- Comp2 Pair / KT / I , and its behavior is a derivable equation
-- (Deriv-level), not just a meta-level Eq.
--
-- For the Rose-chain proof of classical Goedel II, we need BOTH:
--   (a) eT as a Fun1, so it can live inside the object-level term
--       language (unlike  Guard/RoseEncE.agda 's meta-level  eTree );
--   (b) its correctness as a Deriv, so chains can be assembled
--       without escaping to the meta-level.
--
-- No postulates, no holes.

module Guard.RoseEFun where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)
open import Guard.RoseEncE using (codeFalse ; eTree)
open import Guard.ImpT using (falseT)

------------------------------------------------------------------------
-- The  eT  combinator.
--
-- Applied to any x,
--   ap1 eT x = ap2 Pair (ap2 Pair K1 (ap2 Pair K2 x)) K3
--
-- with K1 = reify tagAp2, K2 = reify (codeF2 TreeEq), K3 = reify codeFalse.
--
-- When x = ap2 Pair a b (representing the code of eqn A B), the output is
-- the Term-level reify of eTree (nd aC bC).

k1 : Term
k1 = reify tagAp2

k2 : Term
k2 = reify (codeF2 TreeEq)

k3 : Term
k3 = reify codeFalse

-- Inner combinator:  x -> ap2 Pair k2 x  (i.e., Pair-with-k2-on-left).
innerPair : Fun1
innerPair = Comp2 Pair (KT k2) I

-- Middle combinator:  x -> ap2 Pair k1 (innerPair x) = ap2 Pair k1 (ap2 Pair k2 x).
middlePair : Fun1
middlePair = Comp2 Pair (KT k1) innerPair

-- Top: eT x = ap2 Pair (middlePair x) k3.
eT : Fun1
eT = Comp2 Pair middlePair (KT k3)

------------------------------------------------------------------------
-- Meta-level correctness: at the reify level, eT matches eTree.

-- Expanded form of  eT  applied to x.

eTExpanded : Term -> Term
eTExpanded x =
  ap2 Pair (ap2 Pair k1 (ap2 Pair k2 x)) k3

-- When x = ap2 Pair (reify aC) (reify bC), eTExpanded x = reify (eTree
-- (nd aC bC)).  This is a meta-level Eq, immediate by def of reify.

eTExpandedMatchesEtree : (aC bC : Tree) ->
  Eq (eTExpanded (ap2 Pair (reify aC) (reify bC)))
     (reify (eTree (nd aC bC)))
eTExpandedMatchesEtree aC bC = refl

------------------------------------------------------------------------
-- Deriv-level correctness of eT.
--
-- For any x, eT x reduces (via axComp2 / axKT / axI) to eTExpanded x.

eTReduces : (x : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 eT x) (eTExpanded x))
eTReduces x {hyp} =
  ruleTrans step1
  (ruleTrans step2
  (ruleTrans step3 step4))
  where
  -- step1: ap1 eT x = ap2 Pair (ap1 middlePair x) (ap1 (KT k3) x)
  step1 : Deriv hyp (eqn (ap1 eT x)
                         (ap2 Pair (ap1 middlePair x) (ap1 (KT k3) x)))
  step1 = axComp2 Pair middlePair (KT k3) x

  -- step2: rewrite (KT k3 x) to k3.
  step2 : Deriv hyp (eqn (ap2 Pair (ap1 middlePair x) (ap1 (KT k3) x))
                         (ap2 Pair (ap1 middlePair x) k3))
  step2 = congR Pair (ap1 middlePair x) (axKT k3 x)

  -- step3: rewrite middlePair x to ap2 Pair k1 (ap1 innerPair x).
  --   ap1 middlePair x = ap1 (Comp2 Pair (KT k1) innerPair) x
  --                    = ap2 Pair (ap1 (KT k1) x) (ap1 innerPair x)
  --                    = ap2 Pair k1 (ap1 innerPair x).
  middlePairReduces : Deriv hyp (eqn (ap1 middlePair x)
                                     (ap2 Pair k1 (ap1 innerPair x)))
  middlePairReduces = ruleTrans
    (axComp2 Pair (KT k1) innerPair x)
    (congL Pair (ap1 innerPair x) (axKT k1 x))

  step3 : Deriv hyp (eqn (ap2 Pair (ap1 middlePair x) k3)
                         (ap2 Pair (ap2 Pair k1 (ap1 innerPair x)) k3))
  step3 = congL Pair k3 middlePairReduces

  -- step4: rewrite innerPair x to ap2 Pair k2 x.
  --   ap1 innerPair x = ap1 (Comp2 Pair (KT k2) I) x
  --                   = ap2 Pair (ap1 (KT k2) x) (ap1 I x)
  --                   = ap2 Pair k2 x.
  innerPairReduces : Deriv hyp (eqn (ap1 innerPair x) (ap2 Pair k2 x))
  innerPairReduces = ruleTrans
    (axComp2 Pair (KT k2) I x)
    (ruleTrans (congL Pair (ap1 I x) (axKT k2 x))
               (congR Pair k2 (axI x)))

  -- step4: apply innerPairReduces inside the nested Pair.
  step4 : Deriv hyp (eqn (ap2 Pair (ap2 Pair k1 (ap1 innerPair x)) k3)
                         (ap2 Pair (ap2 Pair k1 (ap2 Pair k2 x)) k3))
  step4 = congL Pair k3 (congR Pair k1 innerPairReduces)

------------------------------------------------------------------------
-- Specialisation to x = ap2 Pair a b  (Pair-shaped input).
--
-- When the input x is already in Pair form (as happens when the caller
-- wants to apply eT to a reified codeEqn), the output is directly the
-- Term-level representation of reify (eTree (nd aC bC)) with aC = code
-- matching a, bC = code matching b.

eTAtPair : (a b : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 eT (ap2 Pair a b))
                 (ap2 Pair (ap2 Pair k1 (ap2 Pair k2 (ap2 Pair a b))) k3))
eTAtPair a b = eTReduces (ap2 Pair a b)

------------------------------------------------------------------------
-- Correctness against the meta-level  codeEqn  /  eTree  spec:
-- eT applied to reify (codeEqn (eqn A B)) produces reify (codeEqn (eqn
-- (ap2 TreeEq A B) falseT)).

-- codeEqn (eqn A B) = nd (code A) (code B), so reify (codeEqn (eqn A
-- B)) = ap2 Pair (reify (code A)) (reify (code B)).

reifyCodeEqn : (A B : Term) ->
  Eq (reify (codeEqn (eqn A B)))
     (ap2 Pair (reify (code A)) (reify (code B)))
reifyCodeEqn A B = refl

-- The target:  reify (codeEqn (eqn (ap2 TreeEq A B) falseT)).
--
-- We expand:
--   codeEqn (eqn (ap2 TreeEq A B) falseT)
--     = nd (code (ap2 TreeEq A B)) (code falseT)
--     = nd (nd tagAp2 (nd (codeF2 TreeEq) (nd (code A) (code B))))
--          codeFalse
--
-- So reify of this = ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair
-- (reify (codeF2 TreeEq)) (ap2 Pair (reify (code A)) (reify (code
-- B))))) (reify codeFalse).

reifyCodeEqnNeg : (A B : Term) ->
  Eq (reify (codeEqn (eqn (ap2 TreeEq A B) falseT)))
     (ap2 Pair (ap2 Pair k1 (ap2 Pair k2
              (ap2 Pair (reify (code A)) (reify (code B))))) k3)
reifyCodeEqnNeg A B = refl

-- The Deriv-level consequence: feeding reify (codeEqn (eqn A B)) into
-- eT yields reify (codeEqn (eqn (ap2 TreeEq A B) falseT)).

eTCorrect : (A B : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 eT (reify (codeEqn (eqn A B))))
                 (reify (codeEqn (eqn (ap2 TreeEq A B) falseT))))
eTCorrect A B = eTAtPair (reify (code A)) (reify (code B))

------------------------------------------------------------------------
-- Summary
--
-- eT : Fun1  -- the e-function definable from Comp2/KT/I combinators.
--
-- eTCorrect :  ap1 eT (reify (codeEqn (eqn A B)))
--            = reify (codeEqn (eqn (ap2 TreeEq A B) falseT))
--
-- This is the object-level / Deriv-level analogue of
-- Guard/RoseEncE.agda's meta-level eTree.  It is the missing
-- ingredient for Rose's chain in the Rose/Ryan-style formulation of
-- classical Goedel II over Triv (see Guard/ROSE-CHAIN-DESIGN.md for the
-- full plan).
