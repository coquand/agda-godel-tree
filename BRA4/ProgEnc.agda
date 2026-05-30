{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ProgEnc -- Phase E4, step R1a (CHAITIN-G1-FAITHFUL-BLUEPRINT.md S5bis):
-- the program-string ENCODER  enc  and the faithful SIZE bridge
--
--   lenR_enc :  lenR (enc t)  =  natCode (nodes t) .
--
-- A program code  t  (an mcode tree over the alphabet  {O, s, pi} ) is
-- serialised in PREORDER into a right-spine of tag-cells; lenR counts the
-- cells, so it measures the program's DESCRIPTION LENGTH faithfully (the
-- Chaitin size).  This is the  Bin.binMetaFromBits / lenR_binMeta  pattern,
-- with a node TAG (leaf / unary / binary) in place of a bit.
--
--   cell tag rest = pi (natCode tag) rest          (tag in {1,2,3}, so the
--                                                    first child is  s _ )
--   encApp O          rest = cell 1 rest
--   encApp (var k)    rest = cell 1 rest            (no var in mcode; leaf)
--   encApp (ap1 _ t)  rest = cell 2 (encApp t rest)
--   encApp (ap2 _ a b) rest = cell 3 (encApp a (encApp b rest))
--   enc t = encApp t O
--
-- nodes counts one per cell.  lenR_enc holds for ALL Terms (lenR / nodes do
-- not inspect the Fun1/Fun2 head, only the Term constructor).  The inverse
-- parse and the round-trip (which DO need the head, hence only the
-- {O,s,pi} fragment) are step R1b, BRA4.ProgParse.

module BRA4.ProgEnc where

open import BRA4.Base
open import BRA4.LenR using ( lenR ; lenR_at_O ; lenR_at_node )

open import BRA3.Church       using ( pi )
open import BRA3.Code.Tag     using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right )

------------------------------------------------------------------------
-- A small meta lemma: associativity of  addN  (recursion on the first arg,
-- matching  addN zero n = n ,  addN (suc m) n = suc (addN m n) ).

addN_assoc : (a b c : Nat) -> Eq (addN a (addN b c)) (addN (addN a b) c)
addN_assoc zero    b c = refl
addN_assoc (suc a) b c = eqCong suc (addN_assoc a b c)

------------------------------------------------------------------------
-- Node tags.  All >= 1, so  natCode tag = s (...)  and  lenR_at_node  fires.

tagLeaf : Nat
tagLeaf = suc zero

tagUnary : Nat
tagUnary = suc (suc zero)

tagBinary : Nat
tagBinary = suc (suc (suc zero))

------------------------------------------------------------------------
-- The encoder (meta).  encApp t rest = (preorder cells of t) ++ rest.

encApp : Term -> Term -> Term
encApp O          rest = ap2 pi (natCode tagLeaf)   rest
encApp (var k)    rest = ap2 pi (natCode tagLeaf)   rest
encApp (ap1 f t)  rest = ap2 pi (natCode tagUnary)  (encApp t rest)
encApp (ap2 g a b) rest = ap2 pi (natCode tagBinary) (encApp a (encApp b rest))

enc : Term -> Term
enc t = encApp t O

------------------------------------------------------------------------
-- The node count (meta).  One per cell.

nodes : Term -> Nat
nodes O           = suc zero
nodes (var k)     = suc zero
nodes (ap1 f t)   = suc (nodes t)
nodes (ap2 g a b) = suc (addN (nodes a) (nodes b))

------------------------------------------------------------------------
-- The size bridge, threaded form:  given  lenR rest = natCode m ,
--   lenR (encApp t rest) = natCode (addN (nodes t) m) .
-- (Threading  m  avoids any  iterS / multiplication: each layer is one  s .)

lenR_encApp :
  (t rest : Term) (m : Nat) ->
  Deriv (eqF (ap1 lenR rest) (natCode m)) ->
  Deriv (eqF (ap1 lenR (encApp t rest)) (natCode (addN (nodes t) m)))
lenR_encApp O rest m h =
  ruleTrans (lenR_at_node O rest) (cong1 s h)
lenR_encApp (var k) rest m h =
  ruleTrans (lenR_at_node O rest) (cong1 s h)
lenR_encApp (ap1 f t) rest m h =
  ruleTrans (lenR_at_node (natCode (suc zero)) (encApp t rest))
            (cong1 s (lenR_encApp t rest m h))
lenR_encApp (ap2 g a b) rest m h =
  eqSubst (\ k -> Deriv (eqF (ap1 lenR (encApp (ap2 g a b) rest)) (natCode k)))
          (eqCong suc (addN_assoc (nodes a) (nodes b) m))
          (ruleTrans (lenR_at_node (natCode (suc (suc zero))) (encApp a (encApp b rest)))
                     (cong1 s (lenR_encApp a (encApp b rest) (addN (nodes b) m)
                                          (lenR_encApp b rest m h))))

------------------------------------------------------------------------
-- HEADLINE:  lenR (enc t) = natCode (nodes t) .  lenR is faithful on the
-- description string (it counts the nodes of the program).

lenR_enc :
  (t : Term) -> Deriv (eqF (ap1 lenR (enc t)) (natCode (nodes t)))
lenR_enc t =
  eqSubst (\ k -> Deriv (eqF (ap1 lenR (enc t)) (natCode k)))
          (addN_zero_right (nodes t))
          (lenR_encApp t O zero lenR_at_O)
