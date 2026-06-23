{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerCode -- THE OBJECT CODING of parallel-reduction DERIVATIONS as labelled
-- binary trees, on T4.BinTree (the induction-oriented library), DISCARDING the
-- ParCert / isCert fold.  This is the first brick of the genuinely INTERNAL
-- layer (Theorem C of T4/CON-T0-ARCHITECTURE.md): from here on every conclusion
-- is an object  Deriv (...) , not a meta Agda  Set .
--
-- A derivation node carries its constructor TAG (0=pZe .. 4=pRS) in the label
-- and its sub-derivations as children, coded with  binLeaf / binNode :
--
--     derZe          = binLeaf 0                       (tag 0, 0 children)
--     derSu d        = binNode 1 d        (binLeaf 0)  (tag 1, 1 child + filler)
--     derAd d1 d2    = binNode 2 d1 d2                 (tag 2, 2 children)
--     derRO d        = binNode 3 d        (binLeaf 0)  (tag 3, 1 child + filler)
--     derRS d1 d2    = binNode 4 d1 d2                 (tag 4, 2 children)
--
-- The 1-child constructors use a leaf filler in the unused right slot; object
-- well-formedness ignores it (a leaf is wf).
--
-- DELIVERED, all as object  Deriv :
--   * tag projector equations          derTag_*       (from binTag, axFst only)
--   * child projector equations        derChildL/R_*  (from binL / binR)
--   * the meta shadow  DerM + codeDer  bridging to the structure (gives the
--     leaf/node DISPATCH an opaque code cannot supply -- cf. T4.BinTree.binInd)
--   * OBJECT WELL-FORMEDNESS  derWf : every coded derivation is a wf binary
--     tree, proved by ONE structural induction on the shadow (the "preservation
--     = one structural induction" payoff), reusing  T4.BinTree.isWf .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerCode where

open import T4.Base

open import T4.BinTree
  using ( binLeaf ; binNode ; binArg
        ; binArg_leaf ; binLab
        ; binL ; binR
        ; isWf ; isWf_leaf ; isWf_node )
open import T4.ParEnds using ( pi_O_O )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 0.  Constructor tags.

dgZe : Term
dgZe = natCode 0

dgSu : Term
dgSu = natCode 1

dgAd : Term
dgAd = natCode 2

dgRO : Term
dgRO = natCode 3

dgRS : Term
dgRS = natCode 4

-- the leaf filler used in the unused slot of a 1-child node.
filler : Term
filler = binLeaf dgZe

------------------------------------------------------------------------
-- SECTION 1.  The derivation-node builders.

derZe : Term
derZe = binLeaf dgZe

derSu : Term -> Term
derSu d = binNode dgSu d filler

derAd : Term -> Term -> Term
derAd d1 d2 = binNode dgAd d1 d2

derRO : Term -> Term
derRO d = binNode dgRO d filler

derRS : Term -> Term -> Term
derRS d1 d2 = binNode dgRS d1 d2

------------------------------------------------------------------------
-- SECTION 2.  Child accessors (the left / right sub-derivation of a node).

derL : Term -> Term            -- left child  = Fst (Snd (binArg d))
derL d = ap1 Fst (ap1 Snd (binArg d))

derR : Term -> Term            -- right child = Snd (Snd (binArg d))
derR d = ap1 Snd (ap1 Snd (binArg d))

------------------------------------------------------------------------
-- SECTION 3.  Derivation-TAG projector equations.  The derivation tag lives in
-- the tree LABEL: for the leaf  pZe  it is  binArg derZe ; for the node
-- constructors it is the node label  derLab d = Fst (binArg d)  (= binLab).
-- (BinTree's own  binTag  only distinguishes leaf=1 / node=2.)

derLab : Term -> Term            -- node label = Fst (binArg d)
derLab d = ap1 Fst (binArg d)

derTag_Ze : Deriv (eqF (binArg derZe) dgZe)
derTag_Ze = binArg_leaf dgZe

derTag_Su : (d : Term) -> Deriv (eqF (derLab (derSu d)) dgSu)
derTag_Su d = binLab dgSu d filler

derTag_Ad : (d1 d2 : Term) -> Deriv (eqF (derLab (derAd d1 d2)) dgAd)
derTag_Ad d1 d2 = binLab dgAd d1 d2

derTag_RO : (d : Term) -> Deriv (eqF (derLab (derRO d)) dgRO)
derTag_RO d = binLab dgRO d filler

derTag_RS : (d1 d2 : Term) -> Deriv (eqF (derLab (derRS d1 d2)) dgRS)
derTag_RS d1 d2 = binLab dgRS d1 d2

------------------------------------------------------------------------
-- SECTION 4.  Child projector equations (from binL / binR).

derChildL_Su : (d : Term) -> Deriv (eqF (derL (derSu d)) d)
derChildL_Su d = binL dgSu d filler

derChildL_Ad : (d1 d2 : Term) -> Deriv (eqF (derL (derAd d1 d2)) d1)
derChildL_Ad d1 d2 = binL dgAd d1 d2

derChildR_Ad : (d1 d2 : Term) -> Deriv (eqF (derR (derAd d1 d2)) d2)
derChildR_Ad d1 d2 = binR dgAd d1 d2

derChildL_RO : (d : Term) -> Deriv (eqF (derL (derRO d)) d)
derChildL_RO d = binL dgRO d filler

derChildL_RS : (d1 d2 : Term) -> Deriv (eqF (derL (derRS d1 d2)) d1)
derChildL_RS d1 d2 = binL dgRS d1 d2

derChildR_RS : (d1 d2 : Term) -> Deriv (eqF (derR (derRS d1 d2)) d2)
derChildR_RS d1 d2 = binR dgRS d1 d2

------------------------------------------------------------------------
-- SECTION 5.  The meta shadow  DerM + codeDer  (the leaf/node dispatch).
-- Mirrors T4.ObjCR.Der; supplies the structural induction an opaque code
-- cannot (no surjective pairing).

data DerM : Set where
  mZe : DerM
  mSu : DerM -> DerM
  mAd : DerM -> DerM -> DerM
  mRO : DerM -> DerM
  mRS : DerM -> DerM -> DerM

codeDer : DerM -> Term
codeDer mZe         = derZe
codeDer (mSu d)     = derSu (codeDer d)
codeDer (mAd d1 d2) = derAd (codeDer d1) (codeDer d2)
codeDer (mRO d)     = derRO (codeDer d)
codeDer (mRS d1 d2) = derRS (codeDer d1) (codeDer d2)

------------------------------------------------------------------------
-- SECTION 6.  OBJECT WELL-FORMEDNESS:  every coded derivation is a wf binary
-- tree (object  Deriv ), by ONE structural induction on the shadow.  The
-- 2-children nodes recover both child wf-proofs; the 1-child nodes pair the
-- child proof with the filler-leaf proof.  All collapse to O via  pi_O_O .

-- shared: from  isWf l = O  and  isWf r = O  conclude  isWf (binNode n l r) = O.
nodeWf : (n l r : Term) ->
         Deriv (eqF (ap1 isWf l) O) -> Deriv (eqF (ap1 isWf r) O) ->
         Deriv (eqF (ap1 isWf (binNode n l r)) O)
nodeWf n l r wl wr =
  ruleTrans (isWf_node n l r)
    (ruleTrans (congL pi (ap1 isWf r) wl)
      (ruleTrans (congR pi O wr) pi_O_O))

derWf : (d : DerM) -> Deriv (eqF (ap1 isWf (codeDer d)) O)
derWf mZe         = isWf_leaf dgZe
derWf (mSu d)     = nodeWf dgSu (codeDer d) filler (derWf d) (isWf_leaf dgZe)
derWf (mAd d1 d2) = nodeWf dgAd (codeDer d1) (codeDer d2) (derWf d1) (derWf d2)
derWf (mRO d)     = nodeWf dgRO (codeDer d) filler (derWf d) (isWf_leaf dgZe)
derWf (mRS d1 d2) = nodeWf dgRS (codeDer d1) (codeDer d2) (derWf d1) (derWf d2)
