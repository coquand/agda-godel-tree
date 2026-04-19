{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ThFunTForV3 — object-level hypothesis-aware proof evaluator.
--
-- Phase B of the Gödel-II redesign (see GODEL-II-REDESIGN.md).
--
-- The evaluator  thmT : Term -> Fun1  is parameterised by the ambient
-- hypothesis code  hCode = reify (codeEqn H).  Applying  ap1 (thmT hCode)
-- to an encoded derivation  enc(d)  returns
--   * reify(codeEqn(concl d))   if d : H ⊢ concl(d) is genuine,
--   * O (the sentinel)          otherwise (e.g. if d is a fake of the
--                                kind  mkProofEAny t f  produced in the
--                                old encoding).
--
-- The 25 existing cases  case0 .. case25  from the old
-- Guard.ThFunTForCases0–3 are REUSED unchanged: none of them touches
-- the ambient hypothesis.  The new  case26  is the one that enforces
-- the hypothesis discipline.
--
-- No existing file is touched.

module Guard.ThFunTForV3 where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.SubstOp using (substOp)

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
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  -- n33 = functor tag for RecP (see Term.agda codeF2 (RecP s)).
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

  poo : Term
  poo = ap2 Pair O O

------------------------------------------------------------------------
-- case26: hypothesis-use case.
--
-- Encoding for a  ruleHyp  step at hypothesis H:
--   encHyp hC = nd (natCode n26) hC      where  hC = codeEqn H
--
-- At the node, the step function is called with
--   orig = Pair (reify (natCode n26)) (reify hC)
--   recs = Pair _ _             (irrelevant: the node has no sub-proofs)
--
-- The body of the node — reify hC — is extracted by  Lift Snd  (i.e.
-- the second component of  orig ).  We compare this body against the
-- ambient  hCode  term.  On match, return  hCode  (the conclusion of
-- ruleHyp ⌜H⌝ is ⌜H⌝).  On mismatch, return  O  as sentinel.
--
-- O is a legitimate sentinel because every non-sentinel output of
-- thmT has shape  reify (codeEqn eq) = ap2 Pair _ _ , disjoint from O.

case26 : Term -> Fun2
case26 hCode =
  Fan (Fan (Lift Snd) (kF2 hCode) TreeEq)          -- check: body = hCode ?
      (Fan (kF2 hCode) (kF2 O) Pair)               -- (on-match, on-miss)
      IfLf                                          -- O -> match, Pair -> miss

------------------------------------------------------------------------
-- case19V3: validating trans case.
--
-- Unlike V2's case19 = mkEqF recsAL recsBR (which just emits
-- Pair (left sp1) (right sp2) with no middle-term check), case19V3
-- first verifies that the "middle term" — right-of-sp1 = left-of-sp2
-- — agrees.  On mismatch, it returns the sentinel O, so fake trees
-- like  trans(refl t, refl f)  with t ≠ f  no longer produce a valid
-- codeEqn.  This is the load-bearing extra check beyond the n26 tag.

case19V3 : Fun2
case19V3 = Fan
  (Fan recsAR recsBL TreeEq)                        -- check: right(sp1) = left(sp2) ?
  (Fan (Fan recsAL recsBR Pair) (kF2 O) Pair)        -- (on-match, on-miss)
  IfLf

------------------------------------------------------------------------
-- case23V3: validating ruleInst case.
--
-- Unlike V2's case23 = Post substTFor recsBL / recsBR (which leaves
-- var11 and var12 free to be bound by ruleInst at the Deriv level),
-- case23V3 applies  substOp  dynamically at the Fun2 level, using
--   origA = Pair tC xC              (the encoded subst parameters)
--   recsBL, recsBR = L, R           (sides of the sub-equation)
-- to produce  Pair (substOp (Pair tC xC) L) (substOp (Pair tC xC) R) ,
-- i.e. the reified codes of  subst x t l, subst x t r  when L = reify
-- (code l), R = reify (code r).  No free variables remain — the
-- var-capture loophole of V2's case23 is gone.

case23V3 : Fun2
case23V3 = Fan (Fan origA recsBL substOp)
               (Fan origA recsBR substOp)
               Pair

------------------------------------------------------------------------
-- case27 and case28: encoding cases for the new V3 axioms
-- axRecPLf s p  and  axRecPNd s p a b.
--
-- These Deriv constructors aren't used by natural derivations (they
-- are artifacts of the RecP primitive), but thm14EV3 must handle them
-- for totality.  We give each its own tag + fixed-shape body encoding.
--
-- encAxRecPLf:  nd (natCode n27) (nd (codeF2 s) (code p))
--   body layout: Pair sCr pCr
--   case27 builds the codeEqn of  eqn (ap2 (RecP s) p O) O .
--
-- encAxRecPNd:  nd (natCode n28) (nd (codeF2 s) (nd (code p) (nd (code a) (code b))))
--   body layout: Pair sCr (Pair pCr (Pair aCr bCr))
--   case28 builds the codeEqn of
--     eqn (ap2 (RecP s) p (Pair a b))
--         (ap2 s (Pair p (Pair a b)) (Pair (ap2 (RecP s) p a) (ap2 (RecP s) p b))) .

case27 : Fun2
case27 =
  let recPCodeF = Fan (kF2 n33T) origA Pair          -- reify(codeF2 (RecP s))
      -- LHS code = reify(code (ap2 (RecP s) p O))
      -- Note: code(O:Term) = nd lf lf, so reify = poo.
      --   = Pair tagAp2T (Pair (Pair n33T sCr) (Pair pCr poo))
      lhsInnerF = Fan recPCodeF (Fan origB (kF2 poo) Pair) Pair
      lhsF = Fan (kF2 tagAp2T) lhsInnerF Pair
  in Fan lhsF (kF2 poo) Pair

case28 : Fun2
case28 =
  let recPCodeF = Fan (kF2 n33T) origA Pair           -- reify(codeF2 (RecP s))
      pairF2F   = Fan (kF2 n26T) (kF2 O) Pair         -- reify(codeF2 Pair)
      -- LHS = ap2 (RecP s) p (Pair a b)
      lhsF = mkAp2F recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b)
      -- RHS = ap2 s (Pair p (Pair a b))
      --             (Pair (ap2 (RecP s) p a) (ap2 (RecP s) p b))
      rhsF = mkAp2F origA
               (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
               (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                               (mkAp2F recPCodeF origB1 origB2b))
  in Fan lhsF rhsF Pair

------------------------------------------------------------------------
-- Dispatch chain, threaded with the ambient hypothesis code.
--
-- In the V2 chain (Guard.ThFunTFor) the bottom is  ndT26 = sndArg2 .
-- Here we insert a real tag-26 check in front of the fallthrough,
-- renaming the old fallthrough to  ndT27V3 .

ndT29V3 : Fun2
ndT29V3 = sndArg2

ndT28V3 : Fun2
ndT28V3 = branch (tc n28) case28 ndT29V3

ndT27V3 : Fun2
ndT27V3 = branch (tc n27) case27 ndT28V3

ndT26V3 : Term -> Fun2
ndT26V3 hCode = branch (tc n26) (case26 hCode) ndT27V3

ndT25V3 : Term -> Fun2
ndT25V3 hCode = branch (tc n25) case25 (ndT26V3 hCode)

ndT24V3 : Term -> Fun2
ndT24V3 hCode = branch (tc n24) case24 (ndT25V3 hCode)

ndT23V3 : Term -> Fun2
ndT23V3 hCode = branch (tc n23) case23V3 (ndT24V3 hCode)

ndT22V3 : Term -> Fun2
ndT22V3 hCode = branch (tc n22) case22 (ndT23V3 hCode)

ndT21V3 : Term -> Fun2
ndT21V3 hCode = branch (tc n21) case21 (ndT22V3 hCode)

ndT20V3 : Term -> Fun2
ndT20V3 hCode = branch (tc n20) case20 (ndT21V3 hCode)

ndT19V3 : Term -> Fun2
ndT19V3 hCode = branch (tc n19) case19V3 (ndT20V3 hCode)

ndT18V3 : Term -> Fun2
ndT18V3 hCode = branch (tc n18) case18 (ndT19V3 hCode)

ndT17V3 : Term -> Fun2
ndT17V3 hCode = branch (tc n17) case17 (ndT18V3 hCode)

ndT16V3 : Term -> Fun2
ndT16V3 hCode = branch (tc n16) case16 (ndT17V3 hCode)

ndT15V3 : Term -> Fun2
ndT15V3 hCode = branch (tc n15) case15 (ndT16V3 hCode)

ndT14V3 : Term -> Fun2
ndT14V3 hCode = branch (tc n14) case14 (ndT15V3 hCode)

ndT13V3 : Term -> Fun2
ndT13V3 hCode = branch (tc n13) case13 (ndT14V3 hCode)

ndT12V3 : Term -> Fun2
ndT12V3 hCode = branch (tc n12) case12 (ndT13V3 hCode)

ndT11V3 : Term -> Fun2
ndT11V3 hCode = branch (tc n11) case11 (ndT12V3 hCode)

ndT10V3 : Term -> Fun2
ndT10V3 hCode = branch (tc n10) case10 (ndT11V3 hCode)

ndT9V3 : Term -> Fun2
ndT9V3 hCode = branch (tc n9) case9 (ndT10V3 hCode)

ndT8V3 : Term -> Fun2
ndT8V3 hCode = branch (tc n8) case8 (ndT9V3 hCode)

ndT7V3 : Term -> Fun2
ndT7V3 hCode = branch (tc n7) case7 (ndT8V3 hCode)

ndT6V3 : Term -> Fun2
ndT6V3 hCode = branch (tc n6) case6 (ndT7V3 hCode)

ndT5V3 : Term -> Fun2
ndT5V3 hCode = branch (tc n5) case5 (ndT6V3 hCode)

ndT4V3 : Term -> Fun2
ndT4V3 hCode = branch (tc n4) case4 (ndT5V3 hCode)

ndT3V3 : Term -> Fun2
ndT3V3 hCode = branch (tc n3) case3 (ndT4V3 hCode)

ndT2V3 : Term -> Fun2
ndT2V3 hCode = branch (tc n2) case2 (ndT3V3 hCode)

ndT1V3 : Term -> Fun2
ndT1V3 hCode = branch (tc n1) case1 (ndT2V3 hCode)

ndDispatchV3 : Term -> Fun2
ndDispatchV3 hCode = branch (tc n0) case0 (ndT1V3 hCode)

------------------------------------------------------------------------
-- lf-data dispatch (unchanged from V2: only case13 = axTreeEqLL fires
-- on a lf-body proof, and it does not use the hypothesis).

private
  tag13Check : Fun2
  tag13Check = Fan (Lift Fst) (kF2 (reify (natCode n13))) TreeEq

lfDispatchV3 : Fun2
lfDispatchV3 = branch tag13Check case13 (kF2 O)

-- Check whether the data part of  orig  is lf (= O).
dataIsLfV3 : Fun2
dataIsLfV3 = Fan (Lift Snd) (kF2 O) TreeEq

------------------------------------------------------------------------
-- Step and the evaluator.

thmTStep : Term -> Fun2
thmTStep hCode =
  Fan dataIsLfV3 (Fan lfDispatchV3 (ndDispatchV3 hCode) Pair) IfLf

thmT : Term -> Fun1
thmT hCode = Rec O (thmTStep hCode)
