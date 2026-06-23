{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrDerCode -- OBJECT CODING of parallel-reduction DERIVATIONS for the FULL
-- closed-term p.r. calculus (6 rules o/u/v/C/Rb/Rs over T4.PrCodeObj), the
-- generalisation of T4.DerCode from the toy {Ze,Su,Ad,RO,RS}.
--
-- A derivation node carries its TAG and (for the redex/congruence nodes that
-- mention generic fun-codes) an INERT FUN-CODE BUNDLE in the tree LABEL, plus
-- its <= 2 sub-derivations in the two child slots.  Coded on T4.BinTree:
--
--   derLeaf  reflO          = binLeaf dgReflO                 (refl at tmO)
--   ap1c f d                = binNode (Pair dgAp1c f)  d   filler   (ap1 cong)
--   ap2c g d1 d2            = binNode (Pair dgAp2c g)  d1  d2       (ap2 cong)
--   derO  d                 = binNode (Pair dgRo  O)   d   filler   (o-redex)
--   derU  d                 = binNode (Pair dgRu  O)   d   filler   (u-redex)
--   derV  d1 d2             = binNode (Pair dgRv  O)   d1  d2       (v-redex)
--   derC  g h1 h2 d         = binNode (Pair dgRC  (Pair g (Pair h1 h2)))  d filler
--   derRb g h1 h2 d         = binNode (Pair dgRb  (Pair g (Pair h1 h2)))  d filler
--   derRs g h1 h2 d1 d2     = binNode (Pair dgRs  (Pair g (Pair h1 h2)))  d1 d2
--
-- The label is  Pair tag bundle ; the fold dispatches on  derTag = Fst label ,
-- the endpoint functors read the carried fun-codes from  derBun = Snd label
-- (RAW, no recursion -- fun-codes are inert) and the child fold-values from
-- lIdx / rIdx (the < node course-of-values recovery, unchanged from the toy).
--
-- DELIVERED: tag/bundle/child projector equations + meta shadow DerM + codeDer
-- + OBJECT well-formedness derWf (one structural induction, reusing isWf).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrDerCode where

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

dgReflO : Term
dgReflO = natCode 0

dgAp1c : Term
dgAp1c = natCode 1

dgAp2c : Term
dgAp2c = natCode 2

dgRo : Term
dgRo = natCode 3

dgRu : Term
dgRu = natCode 4

dgRv : Term
dgRv = natCode 5

dgRC : Term
dgRC = natCode 6

dgRb : Term
dgRb = natCode 7

dgRs : Term
dgRs = natCode 8

filler : Term
filler = binLeaf dgReflO

-- the inert fun-code bundle for the C / R nodes.
bun3 : Term -> Term -> Term -> Term
bun3 g h1 h2 = ap2 Pair g (ap2 Pair h1 h2)

------------------------------------------------------------------------
-- SECTION 1.  Derivation-node builders.

derLeaf : Term                                 -- reflexivity at tmO
derLeaf = binLeaf dgReflO

ap1c : Term -> Term -> Term                    -- ap1 congruence, carries fun f
ap1c f d = binNode (ap2 Pair dgAp1c f) d filler

ap2c : Term -> Term -> Term -> Term            -- ap2 congruence, carries fun g
ap2c g d1 d2 = binNode (ap2 Pair dgAp2c g) d1 d2

derO : Term -> Term                            -- o-redex (fun fixed = cZero)
derO d = binNode (ap2 Pair dgRo O) d filler

derU : Term -> Term                            -- u-redex (fun fixed = cId)
derU d = binNode (ap2 Pair dgRu O) d filler

derV : Term -> Term -> Term                    -- v-redex (fun fixed = cProj)
derV d1 d2 = binNode (ap2 Pair dgRv O) d1 d2

derC : Term -> Term -> Term -> Term -> Term    -- C-redex, carries g h1 h2
derC g h1 h2 d = binNode (ap2 Pair dgRC (bun3 g h1 h2)) d filler

derRb : Term -> Term -> Term -> Term -> Term   -- R-base redex, carries g h1 h2
derRb g h1 h2 d = binNode (ap2 Pair dgRb (bun3 g h1 h2)) d filler

derRs : Term -> Term -> Term -> Term -> Term -> Term  -- R-step redex
derRs g h1 h2 d1 d2 = binNode (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2

------------------------------------------------------------------------
-- SECTION 2.  Child accessors (the left / right sub-derivation of a node).

derL : Term -> Term            -- left child  = Fst (Snd (binArg d))
derL d = ap1 Fst (ap1 Snd (binArg d))

derR : Term -> Term            -- right child = Snd (Snd (binArg d))
derR d = ap1 Snd (ap1 Snd (binArg d))

------------------------------------------------------------------------
-- SECTION 3.  Label / tag / bundle accessors.

derLab : Term -> Term          -- the node label  = Fst (binArg d)  (= Pair tag bundle)
derLab d = ap1 Fst (binArg d)

derTag : Term -> Term          -- the constructor tag = Fst (derLab d)
derTag d = ap1 Fst (derLab d)

derBun : Term -> Term          -- the inert fun-code bundle = Snd (derLab d)
derBun d = ap1 Snd (derLab d)

------------------------------------------------------------------------
-- SECTION 4.  Tag projector equations.
-- Leaf: the tag is  binArg derLeaf  directly.  Nodes: tag = Fst (label),
-- with label recovered by binLab.

derTag_reflO : Deriv (eqF (binArg derLeaf) dgReflO)
derTag_reflO = binArg_leaf dgReflO

-- shared: label of a node X is  Pair dgX bun  (by binLab), so its tag = dgX.
nodeTag : (dgX bun l r : Term) -> Deriv (eqF (derTag (binNode (ap2 Pair dgX bun) l r)) dgX)
nodeTag dgX bun l r =
  ruleTrans (cong1 Fst (binLab (ap2 Pair dgX bun) l r)) (axFst dgX bun)

nodeBun : (dgX bun l r : Term) -> Deriv (eqF (derBun (binNode (ap2 Pair dgX bun) l r)) bun)
nodeBun dgX bun l r =
  ruleTrans (cong1 Snd (binLab (ap2 Pair dgX bun) l r)) (axSnd dgX bun)

derTag_Ap1c : (f d : Term) -> Deriv (eqF (derTag (ap1c f d)) dgAp1c)
derTag_Ap1c f d = nodeTag dgAp1c f d filler

derTag_Ap2c : (g d1 d2 : Term) -> Deriv (eqF (derTag (ap2c g d1 d2)) dgAp2c)
derTag_Ap2c g d1 d2 = nodeTag dgAp2c g d1 d2

derTag_O : (d : Term) -> Deriv (eqF (derTag (derO d)) dgRo)
derTag_O d = nodeTag dgRo O d filler

derTag_U : (d : Term) -> Deriv (eqF (derTag (derU d)) dgRu)
derTag_U d = nodeTag dgRu O d filler

derTag_V : (d1 d2 : Term) -> Deriv (eqF (derTag (derV d1 d2)) dgRv)
derTag_V d1 d2 = nodeTag dgRv O d1 d2

derTag_C : (g h1 h2 d : Term) -> Deriv (eqF (derTag (derC g h1 h2 d)) dgRC)
derTag_C g h1 h2 d = nodeTag dgRC (bun3 g h1 h2) d filler

derTag_Rb : (g h1 h2 d : Term) -> Deriv (eqF (derTag (derRb g h1 h2 d)) dgRb)
derTag_Rb g h1 h2 d = nodeTag dgRb (bun3 g h1 h2) d filler

derTag_Rs : (g h1 h2 d1 d2 : Term) -> Deriv (eqF (derTag (derRs g h1 h2 d1 d2)) dgRs)
derTag_Rs g h1 h2 d1 d2 = nodeTag dgRs (bun3 g h1 h2) d1 d2

------------------------------------------------------------------------
-- SECTION 5.  Bundle projector equations (the carried fun-codes), RAW.

derBun_Ap1c : (f d : Term) -> Deriv (eqF (derBun (ap1c f d)) f)
derBun_Ap1c f d = nodeBun dgAp1c f d filler

derBun_Ap2c : (g d1 d2 : Term) -> Deriv (eqF (derBun (ap2c g d1 d2)) g)
derBun_Ap2c g d1 d2 = nodeBun dgAp2c g d1 d2

derBun_C : (g h1 h2 d : Term) -> Deriv (eqF (derBun (derC g h1 h2 d)) (bun3 g h1 h2))
derBun_C g h1 h2 d = nodeBun dgRC (bun3 g h1 h2) d filler

derBun_Rb : (g h1 h2 d : Term) -> Deriv (eqF (derBun (derRb g h1 h2 d)) (bun3 g h1 h2))
derBun_Rb g h1 h2 d = nodeBun dgRb (bun3 g h1 h2) d filler

derBun_Rs : (g h1 h2 d1 d2 : Term) ->
            Deriv (eqF (derBun (derRs g h1 h2 d1 d2)) (bun3 g h1 h2))
derBun_Rs g h1 h2 d1 d2 = nodeBun dgRs (bun3 g h1 h2) d1 d2

-- bundle components  bun3 g h1 h2 = Pair g (Pair h1 h2) :  g = Fst , h1 = Fst Snd , h2 = Snd Snd.
bunG : (g h1 h2 : Term) -> Deriv (eqF (ap1 Fst (bun3 g h1 h2)) g)
bunG g h1 h2 = axFst g (ap2 Pair h1 h2)

bunInner : (g h1 h2 : Term) -> Deriv (eqF (ap1 Snd (bun3 g h1 h2)) (ap2 Pair h1 h2))
bunInner g h1 h2 = axSnd g (ap2 Pair h1 h2)

bunH1 : (g h1 h2 : Term) -> Deriv (eqF (ap1 Fst (ap1 Snd (bun3 g h1 h2))) h1)
bunH1 g h1 h2 = ruleTrans (cong1 Fst (bunInner g h1 h2)) (axFst h1 h2)

bunH2 : (g h1 h2 : Term) -> Deriv (eqF (ap1 Snd (ap1 Snd (bun3 g h1 h2))) h2)
bunH2 g h1 h2 = ruleTrans (cong1 Snd (bunInner g h1 h2)) (axSnd h1 h2)

------------------------------------------------------------------------
-- SECTION 6.  Child projector equations (from binL / binR).

derChildL_Ap1c : (f d : Term) -> Deriv (eqF (derL (ap1c f d)) d)
derChildL_Ap1c f d = binL (ap2 Pair dgAp1c f) d filler

derChildL_Ap2c : (g d1 d2 : Term) -> Deriv (eqF (derL (ap2c g d1 d2)) d1)
derChildL_Ap2c g d1 d2 = binL (ap2 Pair dgAp2c g) d1 d2

derChildR_Ap2c : (g d1 d2 : Term) -> Deriv (eqF (derR (ap2c g d1 d2)) d2)
derChildR_Ap2c g d1 d2 = binR (ap2 Pair dgAp2c g) d1 d2

derChildL_O : (d : Term) -> Deriv (eqF (derL (derO d)) d)
derChildL_O d = binL (ap2 Pair dgRo O) d filler

derChildL_U : (d : Term) -> Deriv (eqF (derL (derU d)) d)
derChildL_U d = binL (ap2 Pair dgRu O) d filler

derChildL_V : (d1 d2 : Term) -> Deriv (eqF (derL (derV d1 d2)) d1)
derChildL_V d1 d2 = binL (ap2 Pair dgRv O) d1 d2

derChildR_V : (d1 d2 : Term) -> Deriv (eqF (derR (derV d1 d2)) d2)
derChildR_V d1 d2 = binR (ap2 Pair dgRv O) d1 d2

derChildL_C : (g h1 h2 d : Term) -> Deriv (eqF (derL (derC g h1 h2 d)) d)
derChildL_C g h1 h2 d = binL (ap2 Pair dgRC (bun3 g h1 h2)) d filler

derChildL_Rb : (g h1 h2 d : Term) -> Deriv (eqF (derL (derRb g h1 h2 d)) d)
derChildL_Rb g h1 h2 d = binL (ap2 Pair dgRb (bun3 g h1 h2)) d filler

derChildL_Rs : (g h1 h2 d1 d2 : Term) -> Deriv (eqF (derL (derRs g h1 h2 d1 d2)) d1)
derChildL_Rs g h1 h2 d1 d2 = binL (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2

derChildR_Rs : (g h1 h2 d1 d2 : Term) -> Deriv (eqF (derR (derRs g h1 h2 d1 d2)) d2)
derChildR_Rs g h1 h2 d1 d2 = binR (ap2 Pair dgRs (bun3 g h1 h2)) d1 d2

------------------------------------------------------------------------
-- SECTION 7.  The meta shadow  DerM + codeDer  (leaf/node dispatch).

data DerM : Set where
  mRefl : DerM
  mAp1c : Term -> DerM -> DerM
  mAp2c : Term -> DerM -> DerM -> DerM
  mO    : DerM -> DerM
  mU    : DerM -> DerM
  mV    : DerM -> DerM -> DerM
  mC    : Term -> Term -> Term -> DerM -> DerM
  mRb   : Term -> Term -> Term -> DerM -> DerM
  mRs   : Term -> Term -> Term -> DerM -> DerM -> DerM

codeDer : DerM -> Term
codeDer mRefl            = derLeaf
codeDer (mAp1c f d)      = ap1c f (codeDer d)
codeDer (mAp2c g d1 d2)  = ap2c g (codeDer d1) (codeDer d2)
codeDer (mO d)           = derO (codeDer d)
codeDer (mU d)           = derU (codeDer d)
codeDer (mV d1 d2)       = derV (codeDer d1) (codeDer d2)
codeDer (mC g h1 h2 d)   = derC g h1 h2 (codeDer d)
codeDer (mRb g h1 h2 d)  = derRb g h1 h2 (codeDer d)
codeDer (mRs g h1 h2 d1 d2) = derRs g h1 h2 (codeDer d1) (codeDer d2)

------------------------------------------------------------------------
-- SECTION 8.  OBJECT WELL-FORMEDNESS:  every coded derivation is a wf binary
-- tree (object Deriv), by ONE structural induction on the shadow.

nodeWf : (n l r : Term) ->
         Deriv (eqF (ap1 isWf l) O) -> Deriv (eqF (ap1 isWf r) O) ->
         Deriv (eqF (ap1 isWf (binNode n l r)) O)
nodeWf n l r wl wr =
  ruleTrans (isWf_node n l r)
    (ruleTrans (congL pi (ap1 isWf r) wl)
      (ruleTrans (congR pi O wr) pi_O_O))

fillerWf : Deriv (eqF (ap1 isWf filler) O)
fillerWf = isWf_leaf dgReflO

derWf : (d : DerM) -> Deriv (eqF (ap1 isWf (codeDer d)) O)
derWf mRefl           = isWf_leaf dgReflO
derWf (mAp1c f d)     = nodeWf (ap2 Pair dgAp1c f) (codeDer d) filler (derWf d) fillerWf
derWf (mAp2c g d1 d2) = nodeWf (ap2 Pair dgAp2c g) (codeDer d1) (codeDer d2) (derWf d1) (derWf d2)
derWf (mO d)          = nodeWf (ap2 Pair dgRo O) (codeDer d) filler (derWf d) fillerWf
derWf (mU d)          = nodeWf (ap2 Pair dgRu O) (codeDer d) filler (derWf d) fillerWf
derWf (mV d1 d2)      = nodeWf (ap2 Pair dgRv O) (codeDer d1) (codeDer d2) (derWf d1) (derWf d2)
derWf (mC g h1 h2 d)  = nodeWf (ap2 Pair dgRC (bun3 g h1 h2)) (codeDer d) filler (derWf d) fillerWf
derWf (mRb g h1 h2 d) = nodeWf (ap2 Pair dgRb (bun3 g h1 h2)) (codeDer d) filler (derWf d) fillerWf
derWf (mRs g h1 h2 d1 d2) =
  nodeWf (ap2 Pair dgRs (bun3 g h1 h2)) (codeDer d1) (codeDer d2) (derWf d1) (derWf d2)
