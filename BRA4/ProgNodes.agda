{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ProgNodes -- Phase E4, step R4a (CHAITIN-G1-FAITHFUL-BLUEPRINT.md S5bis):
-- the nodes-ADDITIVITY / depth-tracking, as a GENERIC context-plugging lemma.
--
--   nodes_plug :  nodes (plug C t)  =  addN (nodesCtx C) (nodes t) .
--
-- A one-hole context  C  is the path from a term's root down to a single
-- distinguished subterm.  This lemma says the node count splits additively:
-- the (fixed, t-independent) context contributes  nodesCtx C , the plugged
-- subterm contributes  nodes t .  For the Berry program this is
--   nodes (Skel[L])  =  nodesCtx (Skel context)  +  nodes (L-embedding)
--                    =  c0  +  emb ,
-- with  c0 = nodesCtx (g_L context)  L-INDEPENDENT.  The proof is by induction
-- on the CONTEXT (its length = the combinator DEPTH to L), never on the
-- program size -- this is exactly the "bounded by depth, not size" claim.
--
-- The concrete g_L context is identified by tracing the (fixed) mcode layers;
-- mcodeLayer_C below demonstrates one such layer-peel is a clean single step.

module BRA4.ProgNodes where

open import BRA4.Base
open import BRA4.ProgEnc using ( nodes ; addN_assoc )

open import BRA3.Church       using ( pi )
open import BRA3.Code.Tag     using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right ; addN_suc_right )

------------------------------------------------------------------------
-- Meta arithmetic:  commutativity (built from the two shipped lemmas) and
-- the left-hole rearrangement  (X + t) + b = (X + b) + t .

addN_comm : (a b : Nat) -> Eq (addN a b) (addN b a)
addN_comm zero    b = eqSym (addN_zero_right b)
addN_comm (suc a) b = eqTrans (eqCong suc (addN_comm a b))
                              (eqSym (addN_suc_right b a))

rearr : (x t b : Nat) -> Eq (addN (addN x t) b) (addN (addN x b) t)
rearr x t b =
  eqTrans (eqSym (addN_assoc x t b))
          (eqTrans (eqCong (addN x) (addN_comm t b))
                   (addN_assoc x b t))

------------------------------------------------------------------------
-- One-hole contexts.

data Ctx : Set where
  hole   : Ctx
  inAp1  : Fun1 -> Ctx -> Ctx          -- ap1 f [.]
  inAp2L : Fun2 -> Ctx -> Term -> Ctx  -- ap2 g [.] b
  inAp2R : Fun2 -> Term -> Ctx -> Ctx  -- ap2 g a [.]

plug : Ctx -> Term -> Term
plug hole          t = t
plug (inAp1 f c)   t = ap1 f (plug c t)
plug (inAp2L g c b) t = ap2 g (plug c t) b
plug (inAp2R g a c) t = ap2 g a (plug c t)

nodesCtx : Ctx -> Nat
nodesCtx hole          = zero
nodesCtx (inAp1 f c)   = suc (nodesCtx c)
nodesCtx (inAp2L g c b) = suc (addN (nodesCtx c) (nodes b))
nodesCtx (inAp2R g a c) = suc (addN (nodes a) (nodesCtx c))

------------------------------------------------------------------------
-- The plugging lemma.  Induction on  C  (length = combinator depth to the
-- hole); each constructor is ONE additivity step.

nodes_plug : (c : Ctx) (t : Term) -> Eq (nodes (plug c t)) (addN (nodesCtx c) (nodes t))
nodes_plug hole          t = refl
nodes_plug (inAp1 f c)   t = eqCong suc (nodes_plug c t)
nodes_plug (inAp2L g c b) t =
  -- nodes (ap2 g (plug c t) b) = suc (addN (nodes (plug c t)) (nodes b))
  -- IH: nodes (plug c t) = addN (nodesCtx c) (nodes t)
  eqCong suc
    (eqTrans (eqCong (\ z -> addN z (nodes b)) (nodes_plug c t))
             (rearr (nodesCtx c) (nodes t) (nodes b)))
nodes_plug (inAp2R g a c) t =
  -- nodes (ap2 g a (plug c t)) = suc (addN (nodes a) (nodes (plug c t)))
  eqCong suc
    (eqTrans (eqCong (addN (nodes a)) (nodes_plug c t))
             (addN_assoc (nodes a) (nodesCtx c) (nodes t)))

------------------------------------------------------------------------
-- DEMONSTRATION that one real mcode layer is a clean single context-step.
-- mcode1 (C g h1 h2) = pi (natCode tag_C) (pi (mcode2 g) (pi (mcode1 h1) (mcode1 h2))).
-- The first child where a deeper subterm (e.g. inside g) lives is reached by
-- the context  inAp2R pi (natCode tag_C) (inAp2L pi hole (...)) ... ; the
-- point is each mcode layer contributes a FIXED number of  suc / addN  steps,
-- so the full path to  L  is a depth-many composition of  Ctx  constructors,
-- and  nodes_plug  collapses it in one application.  Concretely, plugging the
-- g-subterm  X  at  ap2 pi (natCode tag_C) (ap2 pi [X] rest):

mcodeLayer_demo :
  (tagC X rest : Term) ->
  Eq (nodes (ap2 pi tagC (ap2 pi X rest)))
     (addN (nodesCtx (inAp2R pi tagC (inAp2L pi hole rest))) (nodes X))
mcodeLayer_demo tagC X rest =
  nodes_plug (inAp2R pi tagC (inAp2L pi hole rest)) X
