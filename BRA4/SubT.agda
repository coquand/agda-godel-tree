{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SubT -- substitution on Pair-coded Terms / Formulas.
--
-- ======================================================================
-- DESIGN (user-confirmed, 2026-05-17):
-- ======================================================================
--
-- Three BRA  Fun2  functions:
--
--   sbt : Fun2   -- substitution on coded TERMS.
--   sbf : Fun2   -- substitution on coded FORMULAS.
--   sub : Fun2   -- top-level: fix var-index 0, num-ify substituent;
--                  derived as  sub z cP = sbf (Pair (natCode 0) (num z)) cP .
--
-- Each operates on Pair-encoded BRA4 codes ( BRA4.Code ).  The
-- substituent in sbt / sbf's first arg is an ARBITRARY  Term S
-- (NOT restricted to  codeTerm t ) -- the generalisation needed for
-- Thm 14.  See BRA4.SbContract for the contract.
--
-- The user-specified equations (BRA4.SbContract per-shape closures):
--
--   sbt (Pair (natCode k) S) O = O                              [sbt_at_O]
--
--   sbt (Pair (natCode k) S) (Pair (natCode tag_var) (natCode n))
--     = if natEq k n then S
--                    else (Pair (natCode tag_var) (natCode n))   [sbt_at_var]
--
--   sbt (Pair (natCode k) S) (Pair (natCode tag_ap1) (Pair (codeF1 f) cu))
--     = Pair (natCode tag_ap1)
--         (Pair (codeF1 f) (sbt (Pair (natCode k) S) cu))        [sbt_at_ap1]
--
--   sbt (Pair (natCode k) S) (Pair (natCode tag_ap2)
--                                  (Pair (codeF2 g) (Pair cu cv)))
--     = Pair (natCode tag_ap2)
--         (Pair (codeF2 g)
--           (Pair (sbt (Pair (natCode k) S) cu)
--                  (sbt (Pair (natCode k) S) cv)))               [sbt_at_ap2]
--
--   sbf likewise on (atomic, neg, imp) -- recursing via sbt on
--   coded-term subpositions and via sbf on coded-formula subpositions.
--
-- ======================================================================
-- CONSTRUCTION (deferred for next session -- substantial port).
-- ======================================================================
--
-- The BRA construction of  sbt  /  sbf  via course-of-value recursion
-- is non-trivial -- it adapts  BRA3.SubT.V2Full.subT_v2  (which uses
-- BRA3's pi_safe-shifted Tree encoding via  recTreeP ) to BRA4's
-- raw-Pair encoding (with tag>=1 discipline).
--
-- Reference port targets:
--
--   BRA3.RecTreeP.recTreeP         ~600 LoC -- generic tree recursor.
--   BRA3.SubT.V2.gLeaf_subT        -- leaf-preservation Fun1.
--   BRA3.SubT.V2Full.hNode_subT_full  -- the match-test + dispatch Fun2.
--   BRA3.SubT.V2Full.subT_v2       -- the full Fun2.
--   BRA3.SubT.V2VarMatch / V2VarNomatch / V2NonVar -- closure lemmas.
--
-- These together ship  subT_v2  with closures at  encodeTree
-- inputs.  For BRA4 the adaptation is:
--
--   * Replace  encodeTree (Leaf n)  with  O  (for  codeTerm O )
--     OR with  Pair (natCode tag_var) (natCode n)  (for codeTerm var n)
--     OR with  natCode (codeFunNat f)  (for the Fun1/Fun2 leaf positions
--     inside codeTerm).
--   * Replace  encodeTree (Node a b)  with  Pair (natCode tag) body
--     for the appropriate top tag (tag_ap1 / tag_ap2 / tag_eq / ...).
--   * Replace BRA3's pi_safe-based recursion firing (via  predTwice
--     dispatch) with the user's tag>=1 + isZero(Fst) dispatch.
--
-- ESTIMATE.  ~3000-5000 LoC of new BRA4 SubT/* files mirroring the
-- BRA3 SubT/* structure.  Multi-session work.
--
-- THIS SESSION ships the SPECIFICATION (BRA4.SbContract per-shape
-- closures) + the derived sbEq lemma (BRA4.SbDerived) showing how
-- those closures imply the codeFormula F / codeTerm t -shape sbEq
-- via meta-induction.  The actual BRA construction  sbt , sbf  and
-- their closure-equation proofs are the next-session work.

module BRA4.SubT where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.SbContract public
open import BRA4.SbDerived  public
