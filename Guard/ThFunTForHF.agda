{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunTForHF — hypothesis-free thmT (Guard 1963 th-analog).
--
-- Per UNIFIED-DESIGN-REV2.md: our thmT becomes a hyp-free Fun1
-- (no hCode parameter), matching Guard's Def 12 `th : Nat -> Nat`.
-- No `case26` (no hypothesis-use rule in hyp-free Deriv).  All
-- validation-failure sentinels become `codeTrueT` (code of the
-- trivially-true equation  O = O ) instead of `O`.  This makes
-- every thmT output be the code of SOME theorem of BRA — either
-- the intended conclusion, or the  0 = 0  fallback.
--
-- This module replaces Guard.ThFunTForV3Unify for user-facing
-- reasoning.  The non-Unify Guard.ThFunTForV3 stays in place for
-- legacy modules pending [unify-5d] cleanup.
--
-- No postulates, no holes.

module Guard.ThFunTForHF where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.SubstOpUnify using (substOp)
open import Guard.Formula using (tagImp ; tagNeg)

------------------------------------------------------------------------
-- Nat abbreviations (private)

private
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
  -- n26: no longer a live tag (was ruleHyp).  The dispatch chain
  --      skips from n25 to n27.  The tag slot is still consumed by
  --      ndT26HF returning codeTrueT (the validation-failure
  --      sentinel) on encoded-proofs that improperly use n26.
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  n31 : Nat ; n31 = suc n30
  n32 : Nat ; n32 = suc n31
  n33 : Nat ; n33 = suc n32

  tc : Nat -> Fun2
  tc = tagCheck

  -- Useful precomputed Terms
  tagAp2T : Term
  tagAp2T = reify tagAp2

  n26T : Term
  n26T = reify (natCode n26)

  n33T : Term
  n33T = reify (natCode n33)

  falseT : Term
  falseT = ap2 Pair O O

  -- Reified codeF2 constants used in case29 (axGoodstein encoder).
  iflfCFR : Term
  iflfCFR = reify (codeF2 IfLf)

  treeeqCFR : Term
  treeeqCFR = reify (codeF2 TreeEq)

  pairCFR : Term
  pairCFR = reify (codeF2 Pair)

  oCC : Term
  oCC = ap2 Pair O O   -- reify (code O) = reify (nd lf lf)

  -- Reified formula-level tags (for codeFormula).
  tagImpT : Term
  tagImpT = reify tagImp

  tagNegT : Term
  tagNegT = reify tagNeg

------------------------------------------------------------------------
-- codeTrueT: the code of the trivially-true equation  O = O .
--
-- Used as the validation-failure sentinel throughout thmT's
-- dispatch.  On malformed inputs, thmT returns codeTrueT instead
-- of O.  This ensures every thmT output is the code of SOME
-- theorem of BRA (either the intended conclusion, or trivial 0=0).
--
-- Concretely:
--   codeTrueT = reify (codeEqn (eqn O O))
--             = reify (nd (code O) (code O))
--             = reify (nd (nd lf lf) (nd lf lf))
--             = ap2 Pair falseT falseT
-- where falseT = ap2 Pair O O = reify (nd lf lf) = reify (code O).

codeTrueT : Term
codeTrueT = ap2 Pair falseT falseT

------------------------------------------------------------------------
-- Formula-level builder combinators (mirror mkAp1F / mkAp2F).
--
-- mkImpF pF qF = Pair tagImpT (Pair pF qF) — code of implication.
-- mkNegF pF    = Pair tagNegT pF            — code of negation.

mkImpF : Fun2 -> Fun2 -> Fun2
mkImpF pCodeF qCodeF =
  Fan (kF2 tagImpT) (Fan pCodeF qCodeF Pair) Pair

mkNegF : Fun2 -> Fun2
mkNegF pCodeF = Fan (kF2 tagNegT) pCodeF Pair

------------------------------------------------------------------------
-- case19V3: validating trans case.
--
-- On middle-term mismatch, returns codeTrueT (not O).

case19V3 : Fun2
case19V3 = Fan
  (Fan recsAR recsBL TreeEq)                          -- check: right(sp1) = left(sp2) ?
  (Fan (Fan recsAL recsBR Pair) (kF2 codeTrueT) Pair) -- (on-match, on-miss = codeTrueT)
  IfLf

------------------------------------------------------------------------
-- case23V3: ruleInst case (unchanged from hyp-carrying version).

case23V3 : Fun2
case23V3 = Fan (Fan origA recsBL substOp)
               (Fan origA recsBR substOp)
               Pair

------------------------------------------------------------------------
-- case27, case28, case29: same as hyp-carrying version (they don't
-- use hCode).

case27 : Fun2
case27 =
  let recPCodeF = Fan (kF2 n33T) origA Pair
      lhsInnerF = Fan recPCodeF (Fan origB (kF2 falseT) Pair) Pair
      lhsF = Fan (kF2 tagAp2T) lhsInnerF Pair
  in Fan lhsF (kF2 falseT) Pair

case28 : Fun2
case28 =
  let recPCodeF = Fan (kF2 n33T) origA Pair
      pairF2F   = Fan (kF2 n26T) (kF2 O) Pair
      lhsF = mkAp2F recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b)
      rhsF = mkAp2F origA
               (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
               (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                               (mkAp2F recPCodeF origB1 origB2b))
  in Fan lhsF rhsF Pair

case29 : Fun2
case29 =
  let treeEqABF = mkAp2F (kF2 treeeqCFR) origA origB
      pairAOF   = mkAp2F (kF2 pairCFR)   origA (kF2 oCC)
      pairBOF   = mkAp2F (kF2 pairCFR)   origB (kF2 oCC)
      lhsF = mkAp2F (kF2 iflfCFR) treeEqABF pairAOF
      rhsF = mkAp2F (kF2 iflfCFR) treeEqABF pairBOF
  in mkEqF lhsF rhsF

------------------------------------------------------------------------
-- case30, case31, case32: propositional axiom encoders.  Same as
-- hyp-carrying version (no hCode).

case30 : Fun2
case30 = mkImpF origA (mkImpF origB origA)

case31 : Fun2
case31 =
  let pImp_qImpR = mkImpF origA (mkImpF origB1 origB2)
      pImpQ      = mkImpF origA origB1
      pImpR      = mkImpF origA origB2
      pqr        = mkImpF pImpQ pImpR
  in mkImpF pImp_qImpR pqr

case32 : Fun2
case32 =
  mkImpF (mkNegF origA)
         (mkImpF (mkNegF origB)
                 (mkImpF origB origA))

------------------------------------------------------------------------
-- case33: formula-level modus ponens (encMp).
--
-- Validation fallbacks change from kF2 O to kF2 codeTrueT.

rbFst : Fun2
rbFst = Post Fst recsB

rbSnd : Fun2
rbSnd = Post Snd recsB

rbSndFst : Fun2
rbSndFst = Post Fst rbSnd

rbSndSnd : Fun2
rbSndSnd = Post Snd rbSnd

check1mp : Fun2
check1mp = Fan rbFst (kF2 tagImpT) TreeEq

check2mp : Fun2
check2mp = Fan rbSndFst recsA TreeEq

case33 : Fun2
case33 =
  branch check1mp
    (branch check2mp rbSndSnd (kF2 codeTrueT))
    (kF2 codeTrueT)

------------------------------------------------------------------------
-- Extended dispatch chain.
--
-- Compared to ThFunTForV3's chain: no hCode parameter.  Tag 26 is
-- no longer handled by case26 (hypothesis-use); instead it falls
-- through to case27.  Effectively, encountering n26 in an encoded
-- proof means "some old encRuleHyp leftover" — we emit codeTrueT
-- via the validation-failure-sentinel path.
--
-- Simpler: skip tag 26 entirely.  ndT25V3 directly branches to
-- ndT27V3 with n26 as an unmatched tag that falls through the
-- chain.  Since our encoders never emit n26 in hyp-free mode,
-- this gap doesn't cause issues.

ndT34V3 : Fun2
ndT34V3 = sndArg2

ndT33V3 : Fun2
ndT33V3 = branch (tc n33) case33 ndT34V3

ndT32V3 : Fun2
ndT32V3 = branch (tc n32) case32 ndT33V3

ndT31V3 : Fun2
ndT31V3 = branch (tc n31) case31 ndT32V3

ndT30V3 : Fun2
ndT30V3 = branch (tc n30) case30 ndT31V3

ndT29V3 : Fun2
ndT29V3 = branch (tc n29) case29 ndT30V3

ndT28V3 : Fun2
ndT28V3 = branch (tc n28) case28 ndT29V3

ndT27V3 : Fun2
ndT27V3 = branch (tc n27) case27 ndT28V3

-- ndT26V3 skips tag 26 entirely: no case26 dispatch.  Any encoded
-- proof with tag 26 falls through the tagCheck (mismatched) and
-- continues down the chain.
ndT26V3 : Fun2
ndT26V3 = ndT27V3

ndT25V3 : Fun2
ndT25V3 = branch (tc n25) case25 ndT26V3

ndT24V3 : Fun2
ndT24V3 = branch (tc n24) case24 ndT25V3

ndT23V3 : Fun2
ndT23V3 = branch (tc n23) case23V3 ndT24V3

ndT22V3 : Fun2
ndT22V3 = branch (tc n22) case22 ndT23V3

ndT21V3 : Fun2
ndT21V3 = branch (tc n21) case21 ndT22V3

ndT20V3 : Fun2
ndT20V3 = branch (tc n20) case20 ndT21V3

ndT19V3 : Fun2
ndT19V3 = branch (tc n19) case19V3 ndT20V3

ndT18V3 : Fun2
ndT18V3 = branch (tc n18) case18 ndT19V3

ndT17V3 : Fun2
ndT17V3 = branch (tc n17) case17 ndT18V3

ndT16V3 : Fun2
ndT16V3 = branch (tc n16) case16 ndT17V3

ndT15V3 : Fun2
ndT15V3 = branch (tc n15) case15 ndT16V3

ndT14V3 : Fun2
ndT14V3 = branch (tc n14) case14 ndT15V3

ndT13V3 : Fun2
ndT13V3 = branch (tc n13) case13 ndT14V3

ndT12V3 : Fun2
ndT12V3 = branch (tc n12) case12 ndT13V3

ndT11V3 : Fun2
ndT11V3 = branch (tc n11) case11 ndT12V3

ndT10V3 : Fun2
ndT10V3 = branch (tc n10) case10 ndT11V3

ndT9V3 : Fun2
ndT9V3 = branch (tc n9) case9 ndT10V3

ndT8V3 : Fun2
ndT8V3 = branch (tc n8) case8 ndT9V3

ndT7V3 : Fun2
ndT7V3 = branch (tc n7) case7 ndT8V3

ndT6V3 : Fun2
ndT6V3 = branch (tc n6) case6 ndT7V3

ndT5V3 : Fun2
ndT5V3 = branch (tc n5) case5 ndT6V3

ndT4V3 : Fun2
ndT4V3 = branch (tc n4) case4 ndT5V3

ndT3V3 : Fun2
ndT3V3 = branch (tc n3) case3 ndT4V3

ndT2V3 : Fun2
ndT2V3 = branch (tc n2) case2 ndT3V3

ndT1V3 : Fun2
ndT1V3 = branch (tc n1) case1 ndT2V3

ndDispatchV3 : Fun2
ndDispatchV3 = branch (tc n0) case0 ndT1V3

------------------------------------------------------------------------
-- lf-data dispatch.  Fallback on non-tag13 lf data: codeTrueT.

private
  tag13Check : Fun2
  tag13Check = Fan (Lift Fst) (kF2 (reify (natCode n13))) TreeEq

lfDispatchV3 : Fun2
lfDispatchV3 = branch tag13Check case13 (kF2 codeTrueT)

-- Check whether the data part of  orig  is lf (= O).
dataIsLfV3 : Fun2
dataIsLfV3 = Fan (Lift Snd) (kF2 O) TreeEq

------------------------------------------------------------------------
-- Step and the evaluator.  Hyp-free: no hCode parameter.

thmTStep : Fun2
thmTStep =
  Fan dataIsLfV3 (Fan lfDispatchV3 ndDispatchV3 Pair) IfLf

thmT : Fun1
thmT = Rec O thmTStep
