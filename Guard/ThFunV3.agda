{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunV3 — scaffolding for the hypothesis-aware proof evaluator.
--
-- This file is Phase A of the Gödel-II redesign (see GODEL-II-REDESIGN.md).
-- It is deliberately minimal:
--
--   * introduces the new proof-tag  n26  ("use of hypothesis"),
--   * gives the encoding  encHyp : Tree -> Tree  for that tag,
--   * gives a two-argument metalevel evaluator  thFunV3 : Tree -> Tree -> Tree
--     whose first argument is the ambient hypothesis code (<H>).
--
-- For every existing tag n0..n25 it currently DELEGATES to the old unary
-- thFun.  This is intentional: Phase A just wants a tag that exists and
-- a skeleton that typechecks.  Phase B ports the 25 cases to thread
-- <H> through recursive calls.
--
-- No existing file is touched.

module Guard.ThFunV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (thFun)

------------------------------------------------------------------------
-- The new tag.  n26 extends the range of tags used by thm14E
-- (currently 0..25).  Its encoding carries the hypothesis code
-- <H> as its single field of data.

n0  : Nat ; n0  = zero
n1  : Nat ; n1  = suc n0
n2  : Nat ; n2  = suc n1
n3  : Nat ; n3  = suc n2
n4  : Nat ; n4  = suc n3
n5  : Nat ; n5  = suc n4
n6  : Nat ; n6  = suc n5
n7  : Nat ; n7  = suc n6
n8  : Nat ; n8  = suc n7
n9  : Nat ; n9  = suc n8
n10 : Nat ; n10 = suc n9
n11 : Nat ; n11 = suc n10
n12 : Nat ; n12 = suc n11
n13 : Nat ; n13 = suc n12
n14 : Nat ; n14 = suc n13
n15 : Nat ; n15 = suc n14
n16 : Nat ; n16 = suc n15
n17 : Nat ; n17 = suc n16
n18 : Nat ; n18 = suc n17
n19 : Nat ; n19 = suc n18
n20 : Nat ; n20 = suc n19
n21 : Nat ; n21 = suc n20
n22 : Nat ; n22 = suc n21
n23 : Nat ; n23 = suc n22
n24 : Nat ; n24 = suc n23
n25 : Nat ; n25 = suc n24
n26 : Nat ; n26 = suc n25

------------------------------------------------------------------------
-- encHyp : encoding of a  ruleHyp  use-site.
--
-- Input hC is the metalevel code of the ambient hypothesis equation H,
-- i.e. hC = codeEqn H.  The resulting tree  nd (natCode n26) hC  is what
-- the new thm14E emits at every  ruleHyp  node — replacing the old
-- "splice in a mkProofEAny tree for H" trick.

encHyp : Tree -> Tree
encHyp hC = nd (natCode n26) hC

------------------------------------------------------------------------
-- thFunV3 : Tree -> Tree -> Tree
--
--   thFunV3 hyp p = <codeEqn concl>   if p encodes a valid derivation
--                                     of concl from H (with codeEqn H = hyp),
--                 = lf                otherwise (sentinel).
--
-- Phase A: only the n26 case is "real"; every other shape either
-- delegates to the old unary thFun (which ignores hyp) or returns lf.
-- Phase B will replace the delegation with a full case-by-case port.

thFunV3 : Tree -> Tree -> Tree
thFunV3 hyp lf = lf
thFunV3 hyp (nd tag body) =
  boolCase (treeEq tag (natCode n26))
    -- n26 case: body is the encoded hypothesis.  Match it against
    -- the ambient hyp.  On match, return hyp (= codeEqn H); on
    -- mismatch, return the sentinel lf.
    (boolCase (treeEq body hyp) hyp lf)
    -- Other tags: delegate to old thFun for now (Phase B will port).
    (thFun (nd tag body))

------------------------------------------------------------------------
-- Sentinel.  We pick lf.  It is disjoint from every codeEqn eq
-- (which always has shape  nd (code l) (code r) ), so  TreeEq(lf, codeBotT)
-- reduces to  falseT  via  axTreeEqLN  in the object-level system.
-- That is precisely what the new Con_H sentence needs to be meaningful
-- at sentinel witnesses.

sentinel : Tree
sentinel = lf
