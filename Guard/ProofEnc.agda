{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProofEnc — proof-encoding combinators for the classical Gödel II.
--
-- Each combinator takes one or more "encoded sub-proof" Terms and
-- builds a larger encoded Term.  Each comes with a polymorphic
-- correctness lemma showing  thmT hCode  of the combined encoding
-- equals the expected codeEqn of the combined equation.
--
-- These mirror  thm14EV3Sym ,  thm14EV3Trans ,  thm14EV3CongL/R ,
-- and  thm14EV3Inst  from  Guard.Thm14EV3 , but work with Term-level
-- inputs and Deriv-based correctness (i.e. the sub-proof's result is
-- given as a polymorphic Deriv equation, not wrapped in a ProofE3
-- record with concrete Tree components).
--
-- Start: encRuleSym.  Encoding pattern: wrap subEnc with the n18 tag.
--
-- No postulates, no holes.

module Guard.ProofEnc where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTForCorrectDefs using (ndBranchHit ; ndBranchMiss)
open import Guard.ThFunTForV3
open import Guard.ThFunTForV3Defs
open import Guard.ThFunTForV3Pass
open import Guard.ExtractorRed

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

------------------------------------------------------------------------
-- Navigation: from start of ndDispatchV3 to case18 at tag n18.
--
-- Same chain as the private  ndDisp18V3  in  Guard.Thm14EV3 ; we need a
-- publicly accessible copy.

ndDisp18V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n18)) d) r)
                 (ap2 case18 (ap2 Pair (reify (natCode n18)) d) r))
ndDisp18V3Pub hCode d r =
  ruleTrans (ndBranchMiss n18 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n18 n17 case17 (ndT18V3 hCode) d r refl)
             (ndBranchHit n18 case18 (ndT19V3 hCode) d r))))))))))))))))))

------------------------------------------------------------------------
-- encRuleSym: wrap an encoded sub-proof with the sym tag (n18).
--
-- Encoding: Pair (reify (natCode n18)) (Pair (reify tagVar) subEnc).
-- subEnc must be a Pair  Pair paR pbR  (standard proof-encoding shape).
--
-- Correctness: given subCorr : thmT hCode (Pair paR pbR) = Pair tC uC
-- (i.e. the sub-encoding yields codeEqn (eqn t u)), we produce
--   thmT hCode (encRuleSym (Pair paR pbR)) = Pair uC tC
-- (i.e. codeEqn (eqn u t) — the symmetric equation).

encRuleSym : Term -> Term
encRuleSym enc = ap2 Pair (reify (natCode n18)) (ap2 Pair (reify tagVar) enc)

encRuleSymCorr :
  (hCode paR pbR tC uC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair paR pbR)) (ap2 Pair tC uC)) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encRuleSym (ap2 Pair paR pbR)))
                 (ap2 Pair uC tC))
encRuleSymCorr hCode paR pbR tC uC {hyp} subCorr =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR tagVarR spR recs')
  (ruleTrans (ndDisp18V3Pub hCode dat recs')
  (mkEqFRed recsBR recsBL enc recs' uC tC
    (recsBRRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) tagVarR) tC uC)
    (recsBLRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) tagVarR) tC uC)))))
  where
  tagR    : Term ; tagR    = reify (natCode n18)
  tagVarR : Term ; tagVarR = reify tagVar
  spR     : Term ; spR     = ap2 Pair paR pbR
  dat     : Term ; dat     = ap2 Pair tagVarR spR
  enc     : Term ; enc     = ap2 Pair tagR dat
  recs'   : Term
  recs'   = ap2 Pair (ap1 (thmT hCode) tagR)
                     (ap2 Pair (ap1 (thmT hCode) tagVarR) (ap2 Pair tC uC))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) tagVarR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode tagVarR spR paR pbR
                (\x' rc' -> ndDispatchV3PairMiss hCode (ap2 Pair O O) O O x' rc'))
              (congR Pair (ap1 (thmT hCode) tagVarR) subCorr)

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

------------------------------------------------------------------------
-- encRuleSymPass: tag-opaque "pass" property for sym-wrapped encodings.
--
-- Needed when encRuleSym's output appears as a sub-encoding inside
-- another combinator (e.g. encRuleTrans).

encRuleSymPass :
  (hCode paR pbR x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encRuleSym (ap2 Pair paR pbR)) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encRuleSym (ap2 Pair paR pbR)) x) rcs))
encRuleSymPass hCode paR pbR x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n17))
    (ap2 Pair (reify tagVar) (ap2 Pair paR pbR)) x rcs
