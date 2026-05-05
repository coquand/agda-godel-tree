{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12RecCheckTree
--
-- Theorem 12 (asymmetric) for D_Rec_OS_F = Rec O (Post Snd Pair) at
-- ALL CANONICAL Tree inputs, by Agda-level induction on  v : Tree .
--
-- Mirrors Guard's pattern: meta-induction on the input value (which
-- in Guard's framework is always a numeral; here, a canonical tree).
-- The Agda recursion supplies cross-IHs at the recursive subtrees.
--
-- Universal closure over arbitrary  x : Term  (including variables)
-- requires additional machinery (ruleIndBT + SKI internalisation) and
-- is NOT delivered here.  This file delivers the canonical-input case.
--
-- No postulates, no holes.

module BRA.Thm12RecCheckTree where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm14CodeFTeqAsym
open import BRA.Thm.ThmT using
  ( thmT ; tagCode_axRecLf ; tagCode_ruleTrans )
open import BRA.Thm12RecCheck

------------------------------------------------------------------------
-- thm12_RecOS_O_IH1 : the leaf case packaged as an IH1 record.

thm12_RecOS_O_IH1 : IH1 O
thm12_RecOS_O_IH1 = record
  { Df    = ap2 Pair tagCode_axRecLf (ap2 Pair O (reify (codeF2 sBin)))
  ; fstL  = _
  ; fstR  = _
  ; shape = axFst tagCode_axRecLf (ap2 Pair O (reify (codeF2 sBin)))
  ; image = snd thm12_RecOS_O
  }

------------------------------------------------------------------------
-- thm12_RecOS_pair_IH1 : the Pair case packaged as an IH1 record at
-- input  ap2 Pair v1T v2T , given IH1 inputs at  v1T  and  v2T .

thm12_RecOS_pair_IH1 :
  (v1T v2T : Term) (ih_v1 : IH1 v1T) (ih_v2 : IH1 v2T) ->
  IH1 (ap2 Pair v1T v2T)
thm12_RecOS_pair_IH1 v1T v2T ih_v1 ih_v2 =
  let open module M = RecOSPairCaseFull v1T v2T ih_v1 ih_v2
  in record
       { Df    = M.Df_chain12345
       ; fstL  = _
       ; fstR  = _
       ; shape = axFst tagCode_ruleTrans (ap2 Pair M.Df_chain1234 M.Df_E5)
       ; image = snd M.thm12_RecOS_pair
       }

------------------------------------------------------------------------
-- tree_rec : Theorem 12 at all canonical tree inputs, by Agda-level
-- recursion on  v : Tree .  Cross-IHs at the recursive subtrees are
-- supplied automatically by the recursive calls  tree_rec a, tree_rec b .

tree_rec : (v : Tree) -> IH1 (reify v)
tree_rec lf       = thm12_RecOS_O_IH1
tree_rec (nd a b) =
  thm12_RecOS_pair_IH1 (reify a) (reify b) (tree_rec a) (tree_rec b)

------------------------------------------------------------------------
-- Final theorem at canonical inputs.

thm12_RecOS_canonical : (v : Tree) ->
  Sigma Term (\ Df ->
    Deriv (atomic (eqn (ap1 thmT Df) (codeFTeq1Asym D_Rec_OS_F (reify v)))))
thm12_RecOS_canonical v =
  let r = tree_rec v
  in mkSigma (IH1.Df r) (IH1.image r)
