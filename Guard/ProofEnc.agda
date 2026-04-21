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
open import Guard.SubstOp using (substOp)

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

------------------------------------------------------------------------
-- Navigation: from start of ndDispatchV3 to case19V3 at tag n19.

ndDisp19V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n19)) d) r)
                 (ap2 case19V3 (ap2 Pair (reify (natCode n19)) d) r))
ndDisp19V3Pub hCode d r =
  ruleTrans (ndBranchMiss n19 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n19 n18 case18 (ndT19V3 hCode) d r refl)
             (ndBranchHit n19 case19V3 (ndT20V3 hCode) d r)))))))))))))))))))

------------------------------------------------------------------------
-- encRuleTrans: combine two sub-encodings with the trans tag (n19).
--
-- Encoding: Pair (natCode n19) (Pair enc1 enc2).
-- Sub-encodings must already be Pair  Pair paNR pbNR  (standard shape).
--
-- Correctness requires:
--   * subCorr1 : thmT hCode (Pair pa1R pb1R) = Pair tC uC
--   * subCorr2 : thmT hCode (Pair pa2R pb2R) = Pair uC vC  (middle agrees)
--   * pass1    : sub-encoding 1 is tag-opaque to ndDispatchV3.
-- Yields:
--   thmT hCode (encRuleTrans (Pair pa1R pb1R) (Pair pa2R pb2R)) = Pair tC vC.

encRuleTrans : Term -> Term -> Term
encRuleTrans enc1 enc2 =
  ap2 Pair (reify (natCode n19)) (ap2 Pair enc1 enc2)

encRuleTransCorr :
  (hCode pa1R pb1R pa2R pb2R tC uC vC : Term) {hyp : Equation} ->
  ((x rcs : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair pa1R pb1R) x) rcs)
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair pa1R pb1R) x) rcs))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair pa1R pb1R)) (ap2 Pair tC uC)) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair pa2R pb2R)) (ap2 Pair uC vC)) ->
  Deriv hyp (eqn (ap1 (thmT hCode)
                   (encRuleTrans (ap2 Pair pa1R pb1R) (ap2 Pair pa2R pb2R)))
                 (ap2 Pair tC vC))
encRuleTransCorr hCode pa1R pb1R pa2R pb2R tC uC vC {hyp} pass1 subCorr1 subCorr2 =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR sp1R sp2R recs')
  (ruleTrans (ndDisp19V3Pub hCode dat recs')
             (case19V3Match tagR dat (ap1 (thmT hCode) tagR) tC uC vC))))
  where
  tagR  : Term ; tagR  = reify (natCode n19)
  sp1R  : Term ; sp1R  = ap2 Pair pa1R pb1R
  sp2R  : Term ; sp2R  = ap2 Pair pa2R pb2R
  dat   : Term ; dat   = ap2 Pair sp1R sp2R
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode sp1R sp2R pa2R pb2R
                (\x' rc' -> pass1 x' rc'))
    (ruleTrans (congL Pair (ap1 (thmT hCode) sp2R) subCorr1)
               (congR Pair (ap2 Pair tC uC) subCorr2))

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

------------------------------------------------------------------------
-- encRuleTransPass: tag-opaque pass property.

encRuleTransPass :
  (hCode pa1R pb1R pa2R pb2R x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair
                     (encRuleTrans (ap2 Pair pa1R pb1R) (ap2 Pair pa2R pb2R)) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair
                     (encRuleTrans (ap2 Pair pa1R pb1R) (ap2 Pair pa2R pb2R)) x) rcs))
encRuleTransPass hCode pa1R pb1R pa2R pb2R x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n18))
    (ap2 Pair (ap2 Pair pa1R pb1R) (ap2 Pair pa2R pb2R)) x rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case21V3 at tag n21 (congL).

ndDisp21V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n21)) d) r)
                 (ap2 case21 (ap2 Pair (reify (natCode n21)) d) r))
ndDisp21V3Pub hCode d r =
  ruleTrans (ndBranchMiss n21 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n21 n20 case20 (ndT21V3 hCode) d r refl)
             (ndBranchHit n21 case21 (ndT22V3 hCode) d r)))))))))))))))))))))

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case22V3 at tag n22 (congR).

ndDisp22V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n22)) d) r)
                 (ap2 case22 (ap2 Pair (reify (natCode n22)) d) r))
ndDisp22V3Pub hCode d r =
  ruleTrans (ndBranchMiss n22 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n22 n21 case21 (ndT22V3 hCode) d r refl)
             (ndBranchHit n22 case22 (ndT23V3 hCode) d r))))))))))))))))))))))

------------------------------------------------------------------------
-- encCongL: wrap a sub-proof with the congL tag (n21), given a
-- binary functor g and the reified code xC of the fixed argument.
--
-- Encoding: Pair (natCode n21) (Pair (Pair (codeF2 g) xC) subEnc).
-- Caller supplies dispMiss for (Pair (codeF2 g) xC) tag-opacity.

encCongL : Fun2 -> Term -> Term -> Term
encCongL g xC enc =
  ap2 Pair (reify (natCode n21))
    (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) enc)

encCongLCorr :
  (hCode : Term) (g : Fun2) (xC paR pbR tC uC : Term) {hyp : Equation} ->
  ((x' rc' : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) x') rc'))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair paR pbR)) (ap2 Pair tC uC)) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encCongL g xC (ap2 Pair paR pbR)))
    (ap2 Pair (ap2 Pair (reify tagAp2)
                        (ap2 Pair (reify (codeF2 g)) (ap2 Pair tC xC)))
              (ap2 Pair (reify tagAp2)
                        (ap2 Pair (reify (codeF2 g)) (ap2 Pair uC xC)))))
encCongLCorr hCode g xC paR pbR tC uC {hyp} dispMiss subCorr =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR aR spR recs')
  (ruleTrans (ndDisp21V3Pub hCode dat recs')
  (mkEqFRed (mkAp2F origAL recsBL origAR) (mkAp2F origAL recsBR origAR)
    enc recs'
    (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair tC xC)))
    (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair uC xC)))
    (mkAp2FRed origAL recsBL origAR enc recs' gC tC xC
      (origALRed tagR gC xC spR recs')
      (recsBLRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) aR) tC uC)
      (origARRed tagR gC xC spR recs'))
    (mkAp2FRed origAL recsBR origAR enc recs' gC uC xC
      (origALRed tagR gC xC spR recs')
      (recsBRRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) aR) tC uC)
      (origARRed tagR gC xC spR recs'))))))
  where
  gC    : Term ; gC    = reify (codeF2 g)
  spR   : Term ; spR   = ap2 Pair paR pbR
  aR    : Term ; aR    = ap2 Pair gC xC
  tagR  : Term ; tagR  = reify (natCode n21)
  dat   : Term ; dat   = ap2 Pair aR spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode aR spR paR pbR
                (\x' rc' -> dispMiss x' rc'))
              (congR Pair (ap1 (thmT hCode) aR) subCorr)

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

encCongLPass :
  (hCode : Term) (g : Fun2) (xC paR pbR x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encCongL g xC (ap2 Pair paR pbR)) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encCongL g xC (ap2 Pair paR pbR)) x) rcs))
encCongLPass hCode g xC paR pbR x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n20))
    (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) (ap2 Pair paR pbR)) x rcs

------------------------------------------------------------------------
-- encCongR: wrap a sub-proof with the congR tag (n22).  Mirror of
-- encCongL with t/u on the right.

encCongR : Fun2 -> Term -> Term -> Term
encCongR g xC enc =
  ap2 Pair (reify (natCode n22))
    (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) enc)

encCongRCorr :
  (hCode : Term) (g : Fun2) (xC paR pbR tC uC : Term) {hyp : Equation} ->
  ((x' rc' : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) x') rc'))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair paR pbR)) (ap2 Pair tC uC)) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encCongR g xC (ap2 Pair paR pbR)))
    (ap2 Pair (ap2 Pair (reify tagAp2)
                        (ap2 Pair (reify (codeF2 g)) (ap2 Pair xC tC)))
              (ap2 Pair (reify tagAp2)
                        (ap2 Pair (reify (codeF2 g)) (ap2 Pair xC uC)))))
encCongRCorr hCode g xC paR pbR tC uC {hyp} dispMiss subCorr =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR aR spR recs')
  (ruleTrans (ndDisp22V3Pub hCode dat recs')
  (mkEqFRed (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR)
    enc recs'
    (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC tC)))
    (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC uC)))
    (mkAp2FRed origAL origAR recsBL enc recs' gC xC tC
      (origALRed tagR gC xC spR recs')
      (origARRed tagR gC xC spR recs')
      (recsBLRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) aR) tC uC))
    (mkAp2FRed origAL origAR recsBR enc recs' gC xC uC
      (origALRed tagR gC xC spR recs')
      (origARRed tagR gC xC spR recs')
      (recsBRRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) aR) tC uC))))))
  where
  gC    : Term ; gC    = reify (codeF2 g)
  spR   : Term ; spR   = ap2 Pair paR pbR
  aR    : Term ; aR    = ap2 Pair gC xC
  tagR  : Term ; tagR  = reify (natCode n22)
  dat   : Term ; dat   = ap2 Pair aR spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode aR spR paR pbR
                (\x' rc' -> dispMiss x' rc'))
              (congR Pair (ap1 (thmT hCode) aR) subCorr)

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

encCongRPass :
  (hCode : Term) (g : Fun2) (xC paR pbR x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encCongR g xC (ap2 Pair paR pbR)) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encCongR g xC (ap2 Pair paR pbR)) x) rcs))
encCongRPass hCode g xC paR pbR x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n21))
    (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) (ap2 Pair paR pbR)) x rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case23V3 at tag n23 (ruleInst).

ndDisp23V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n23)) d) r)
                 (ap2 case23V3 (ap2 Pair (reify (natCode n23)) d) r))
ndDisp23V3Pub hCode d r =
  ruleTrans (ndBranchMiss n23 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n21 case21 (ndT22V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n23 n22 case22 (ndT23V3 hCode) d r refl)
             (ndBranchHit n23 case23V3 (ndT24V3 hCode) d r)))))))))))))))))))))))

------------------------------------------------------------------------
-- encRuleInst: wrap a sub-proof with the ruleInst tag (n23).
--
-- Encoding: Pair (natCode n23) (Pair aR subEnc) , where aR is the
-- reified code-pair  Pair (reify (code t)) (reify (natCode x))  of the
-- substitution parameters.  Caller supplies aR and its dispMiss.
--
-- Correctness yields  thmT hCode (encRuleInst ...) = Pair (substOp aR
-- lC) (substOp aR r'C) .  Caller combines with substOpCorrect to reach
-- codeEqn (subst x t l, subst x t r') as needed.

encRuleInst : Term -> Term -> Term
encRuleInst aR enc =
  ap2 Pair (reify (natCode n23)) (ap2 Pair aR enc)

encRuleInstCorr :
  (hCode aR paR pbR lC r'C : Term) {hyp : Equation} ->
  ((x' rc' : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair aR x') rc')
                   (ap2 sndArg2 (ap2 Pair aR x') rc'))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair paR pbR)) (ap2 Pair lC r'C)) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encRuleInst aR (ap2 Pair paR pbR)))
                 (ap2 Pair (ap2 substOp aR lC) (ap2 substOp aR r'C)))
encRuleInstCorr hCode aR paR pbR lC r'C {hyp} dispMiss subCorr =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR aR spR recs')
  (ruleTrans (ndDisp23V3Pub hCode dat recs')
             (case23V3Match tagR aR spR
                (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) aR) lC r'C))))
  where
  spR   : Term ; spR   = ap2 Pair paR pbR
  tagR  : Term ; tagR  = reify (natCode n23)
  dat   : Term ; dat   = ap2 Pair aR spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair lC r'C))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair lC r'C)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode aR spR paR pbR
                (\x' rc' -> dispMiss x' rc'))
              (congR Pair (ap1 (thmT hCode) aR) subCorr)

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

encRuleInstPass :
  (hCode aR paR pbR x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encRuleInst aR (ap2 Pair paR pbR)) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encRuleInst aR (ap2 Pair paR pbR)) x) rcs))
encRuleInstPass hCode aR paR pbR x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n22))
    (ap2 Pair aR (ap2 Pair paR pbR)) x rcs

------------------------------------------------------------------------
-- Axiom encoders (closed; no sub-proofs).
--
-- Each axiom of the Deriv system has its own tag (n0..n28) and a
-- fixed body shape.  The encoder here mirrors thm14EV3Ax* from
-- Guard.Thm14EV3 but takes the reified codes of the Term parameters
-- directly, so the output's correctness speaks in terms of supplied
-- reified codes (not opaque Terms).

------------------------------------------------------------------------
-- encAxI: axI t.  Tag n0 (reify = O).
--
-- encAxI tC = Pair O (Pair tC O) , where tC = reify (code t).
-- Correctness: thmT hCode (encAxI tC) = codeEqn(eqn (ap1 I t) t) reified.

encAxI : Term -> Term
encAxI tC = ap2 Pair O (ap2 Pair tC O)

encAxICorr : (hCode tC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxI tC))
    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 I)) tC)) tC))
encAxICorr hCode tC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR tC O recs)
  (ruleTrans (ndBranchHit n0 case0 (ndT1V3 hCode) body recs)
  (mkEqFRed (mkAp1F (kF2 codeIF) origA) origA enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair codeIF tC)) tC
    (mkAp1FRed (kF2 codeIF) origA enc recs codeIF tC
      (kF2Red codeIF enc recs)
      (origARed tagR tC O recs))
    (origARed tagR tC O recs))))
  where
  tagR   : Term ; tagR   = O
  body   : Term ; body   = ap2 Pair tC O
  enc    : Term ; enc    = ap2 Pair tagR body
  codeIF : Term ; codeIF = reify (codeF1 I)
  recs   : Term
  recs   = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

-- encAxIPass: requires the actual Term t (not just reified code) to
-- pattern-match on t's structure for passthrough.

encAxIPass :
  (hCode : Term) (t : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxI (reify (code t))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxI (reify (code t))) x) rcs))
encAxIPass hCode t x rcs = axIPassthroughV3 hCode t x rcs

------------------------------------------------------------------------
-- encAxFst / encAxSnd: Tag n1, n2.  Body = Pair aC bC.

encAxFst : Term -> Term -> Term
encAxFst aC bC = ap2 Pair (reify (natCode n1)) (ap2 Pair aC bC)

encAxFstCorr : (hCode aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxFst aC bC))
    (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Fst))
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)))))
      aC))
encAxFstCorr hCode aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR aC bC recs)
  (ruleTrans (ndBranchMiss n1 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n1 case1 (ndT2V3 hCode) body recs)
  (mkEqFRed (mkAp1F (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB))
            origA enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair codeFstF
      (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
    aC
    (mkAp1FRed (kF2 codeFstF) (mkAp2F (kF2 pairCF) origA origB)
      enc recs codeFstF
      (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
      (kF2Red codeFstF enc recs)
      (mkAp2FRed (kF2 pairCF) origA origB enc recs pairCF aC bC
        (kF2Red pairCF enc recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs)))
    (origARed tagR aC bC recs)))))
  where
  tagR     : Term ; tagR     = reify (natCode n1)
  body     : Term ; body     = ap2 Pair aC bC
  enc      : Term ; enc      = ap2 Pair tagR body
  codeFstF : Term ; codeFstF = reify (codeF1 Fst)
  pairCF   : Term ; pairCF   = reify (codeF2 Pair)
  recs     : Term
  recs     = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxFstPass :
  (hCode : Term) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxFst (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxFst (reify (code a)) (reify (code b))) x) rcs))
encAxFstPass hCode a b x rcs =
  passthroughSucV3 hCode n0 (nd (code a) (code b)) x rcs

encAxSnd : Term -> Term -> Term
encAxSnd aC bC = ap2 Pair (reify (natCode n2)) (ap2 Pair aC bC)

encAxSndCorr : (hCode aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxSnd aC bC))
    (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 Snd))
        (ap2 Pair (reify tagAp2) (ap2 Pair (reify (codeF2 Pair)) (ap2 Pair aC bC)))))
      bC))
encAxSndCorr hCode aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR aC bC recs)
  (ruleTrans (ndBranchMiss n2 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n2 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n2 case2 (ndT3V3 hCode) body recs)
  (mkEqFRed (mkAp1F (kF2 codeSndF) (mkAp2F (kF2 pairCF) origA origB))
            origB enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair codeSndF
      (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))))
    bC
    (mkAp1FRed (kF2 codeSndF) (mkAp2F (kF2 pairCF) origA origB)
      enc recs codeSndF
      (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
      (kF2Red codeSndF enc recs)
      (mkAp2FRed (kF2 pairCF) origA origB enc recs pairCF aC bC
        (kF2Red pairCF enc recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs)))
    (origBRed tagR aC bC recs))))))
  where
  tagR     : Term ; tagR     = reify (natCode n2)
  body     : Term ; body     = ap2 Pair aC bC
  enc      : Term ; enc      = ap2 Pair tagR body
  codeSndF : Term ; codeSndF = reify (codeF1 Snd)
  pairCF   : Term ; pairCF   = reify (codeF2 Pair)
  recs     : Term
  recs     = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxSndPass :
  (hCode : Term) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxSnd (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxSnd (reify (code a)) (reify (code b))) x) rcs))
encAxSndPass hCode a b x rcs =
  passthroughSucV3 hCode n1 (nd (code a) (code b)) x rcs

------------------------------------------------------------------------
-- Extra nat abbreviations for later encoders.

private
  n24 : Nat ; n24 = suc n23
  n25 : Nat ; n25 = suc n24

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case25 at tag n25 (axKT).

ndDisp25V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n25)) d) r)
                 (ap2 case25 (ap2 Pair (reify (natCode n25)) d) r))
ndDisp25V3Pub hCode d r =
  ruleTrans (ndBranchMiss n25 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n21 case21 (ndT22V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n22 case22 (ndT23V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n23 case23V3 (ndT24V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n25 n24 case24 (ndT25V3 hCode) d r refl)
             (ndBranchHit n25 case25 (ndT26V3 hCode) d r)))))))))))))))))))))))))

------------------------------------------------------------------------
-- encAxKT: axKT t x.  Tag n25.
--
-- Encoding: Pair (natCode n25) (Pair tC xC) , tC = reify (code t), xC = reify (code x).
-- Correctness: thmT hCode (encAxKT tC xC)
--   = codeEqn (eqn (ap1 (KT t) x) t) reified
--   = Pair (Pair tagAp1 (Pair (Pair codeKTTag tC) xC)) tC

private
  codeKTTag : Term
  codeKTTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))

encAxKT : Term -> Term -> Term
encAxKT tC xC = ap2 Pair (reify (natCode n25)) (ap2 Pair tC xC)

encAxKTCorr : (hCode tC xC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxKT tC xC))
    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (ap2 Pair codeKTTag tC) xC)) tC))
encAxKTCorr hCode tC xC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR tC xC recs)
  (ruleTrans (ndDisp25V3Pub hCode body recs)
  (mkEqFRed (mkAp1F (Fan (kF2 codeKTTag) origA Pair) origB) origA enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair (ap2 Pair codeKTTag tC) xC))
    tC
    (mkAp1FRed (Fan (kF2 codeKTTag) origA Pair) origB enc recs
      (ap2 Pair codeKTTag tC) xC
      (ruleTrans (fanRed (kF2 codeKTTag) origA Pair enc recs)
      (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red codeKTTag enc recs))
                 (congR Pair codeKTTag (origARed tagR tC xC recs))))
      (origBRed tagR tC xC recs))
    (origARed tagR tC xC recs))))
  where
  tagR : Term ; tagR = reify (natCode n25)
  body : Term ; body = ap2 Pair tC xC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxKTPass :
  (hCode : Term) (t x : Term) (x' rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxKT (reify (code t)) (reify (code x))) x') rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxKT (reify (code t)) (reify (code x))) x') rcs))
encAxKTPass hCode t x x' rcs =
  passthroughSucV3 hCode n24 (nd (code t) (code x)) x' rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case17 at tag n17 (axRefl).

ndDisp17V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n17)) d) r)
                 (ap2 case17 (ap2 Pair (reify (natCode n17)) d) r))
ndDisp17V3Pub hCode d r =
  ruleTrans (ndBranchMiss n17 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n17 n16 case16 (ndT17V3 hCode) d r refl)
             (ndBranchHit n17 case17 (ndT18V3 hCode) d r)))))))))))))))))

------------------------------------------------------------------------
-- encAxRefl: axRefl t.  Tag n17.
--
-- Encoding: Pair (natCode n17) (Pair tC O), tC = reify (code t).
-- Body has shape  Pair tC O  so that origA extracts tC.
-- Correctness: thmT hCode (encAxRefl tC) = Pair tC tC
--   ( = codeEqn (eqn t t) reified ).

encAxRefl : Term -> Term
encAxRefl tC = ap2 Pair (reify (natCode n17)) (ap2 Pair tC O)

encAxReflCorr : (hCode tC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxRefl tC))
                 (ap2 Pair tC tC))
encAxReflCorr hCode tC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR tC O recs)
  (ruleTrans (ndDisp17V3Pub hCode body recs)
  (mkEqFRed origA origA enc recs tC tC
    (origARed tagR tC O recs)
    (origARed tagR tC O recs))))
  where
  tagR : Term ; tagR = reify (natCode n17)
  body : Term ; body = ap2 Pair tC O
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxReflPass :
  (hCode : Term) (t : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxRefl (reify (code t))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxRefl (reify (code t))) x) rcs))
encAxReflPass hCode t x rcs =
  passthroughSucV3 hCode n16 (nd (code t) lf) x rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case20 at tag n20 (cong1).

ndDisp20V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n20)) d) r)
                 (ap2 case20 (ap2 Pair (reify (natCode n20)) d) r))
ndDisp20V3Pub hCode d r =
  ruleTrans (ndBranchMiss n20 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n20 n19 case19V3 (ndT20V3 hCode) d r refl)
             (ndBranchHit n20 case20 (ndT21V3 hCode) d r))))))))))))))))))))

------------------------------------------------------------------------
-- encRuleCong1: wrap a sub-proof with the cong1 tag (n20), given a
-- unary functor f.
--
-- Encoding: Pair (natCode n20) (Pair (codeF1 f) subEnc).
-- Caller supplies dispMiss for (codeF1 f) tag-opacity (the body's inner
-- tag is just fC, not a Pair like in CongL/R).

encRuleCong1 : Fun1 -> Term -> Term
encRuleCong1 f enc =
  ap2 Pair (reify (natCode n20))
    (ap2 Pair (reify (codeF1 f)) enc)

encRuleCong1Corr :
  (hCode : Term) (f : Fun1) (paR pbR tC uC : Term) {hyp : Equation} ->
  ((x' rc' : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (reify (codeF1 f)) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (reify (codeF1 f)) x') rc'))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (ap2 Pair paR pbR)) (ap2 Pair tC uC)) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encRuleCong1 f (ap2 Pair paR pbR)))
    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) tC))
              (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) uC))))
encRuleCong1Corr hCode f paR pbR tC uC {hyp} dispMiss subCorr =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR fC spR recs')
  (ruleTrans (ndDisp20V3Pub hCode dat recs')
  (mkEqFRed (mkAp1F origA recsBL) (mkAp1F origA recsBR)
    enc recs'
    (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
    (ap2 Pair (reify tagAp1) (ap2 Pair fC uC))
    (mkAp1FRed origA recsBL enc recs' fC tC
      (origARed tagR fC spR recs')
      (recsBLRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) fC) tC uC))
    (mkAp1FRed origA recsBR enc recs' fC uC
      (origARed tagR fC spR recs')
      (recsBRRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) fC) tC uC))))))
  where
  fC    : Term ; fC    = reify (codeF1 f)
  spR   : Term ; spR   = ap2 Pair paR pbR
  tagR  : Term ; tagR  = reify (natCode n20)
  dat   : Term ; dat   = ap2 Pair fC spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) fC) (ap2 Pair tC uC))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) fC) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode fC spR paR pbR
                (\x' rc' -> dispMiss x' rc'))
              (congR Pair (ap1 (thmT hCode) fC) subCorr)

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

encRuleCong1Pass :
  (hCode : Term) (f : Fun1) (paR pbR x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encRuleCong1 f (ap2 Pair paR pbR)) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encRuleCong1 f (ap2 Pair paR pbR)) x) rcs))
encRuleCong1Pass hCode f paR pbR x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n19))
    (ap2 Pair (reify (codeF1 f)) (ap2 Pair paR pbR)) x rcs

------------------------------------------------------------------------
-- encAxTreeEqLL: axTreeEqLL.  Tag n13.  Body is O (lf case).
--
-- Encoding: Pair (natCode n13) O.  Closed (no parameters).
-- Correctness: thmT hCode (encAxTreeEqLL)
--   = codeEqn (eqn (ap2 TreeEq O O) O) reified
--   = Pair (Pair tagAp2 (Pair codeF2_TreeEq (Pair (Pair O O) (Pair O O)))) (Pair O O)
--
-- Uses guardLfV3 + lfDispatchV3 (not ndDispatchV3) because body=O.

private
  treeeqCFR : Term ; treeeqCFR = reify (codeF2 TreeEq)
  pairCFR   : Term ; pairCFR   = reify (codeF2 Pair)
  iflfCFR   : Term ; iflfCFR   = reify (codeF2 IfLf)
  oCC       : Term ; oCC       = ap2 Pair O O
  reifyTagAp2 : Term ; reifyTagAp2 = reify tagAp2
  oneC      : Term
  oneC      = ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair oCC oCC))

encAxTreeEqLL : Term
encAxTreeEqLL = ap2 Pair (reify (natCode n13)) O

encAxTreeEqLLCorr : (hCode : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) encAxTreeEqLL)
    (ap2 Pair (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair oCC oCC))) oCC))
encAxTreeEqLLCorr hCode {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR O)
  (ruleTrans (guardLfV3 hCode tagR recs)
  (ruleTrans (ndBranchHit n13 case13 (kF2 O) O recs)
  (mkEqFRed (mkAp2F (kF2 treeeqCFR) (kF2 oCC) (kF2 oCC)) (kF2 oCC) enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair oCC oCC)))
    oCC
    (mkAp2FRed (kF2 treeeqCFR) (kF2 oCC) (kF2 oCC) enc recs treeeqCFR oCC oCC
      (kF2Red treeeqCFR enc recs)
      (kF2Red oCC enc recs)
      (kF2Red oCC enc recs))
    (kF2Red oCC enc recs))))
  where
  tagR : Term ; tagR = reify (natCode n13)
  enc  : Term ; enc  = ap2 Pair tagR O
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) O)

encAxTreeEqLLPass :
  (hCode : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair encAxTreeEqLL x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair encAxTreeEqLL x) rcs))
encAxTreeEqLLPass hCode x rcs =
  passthroughSucV3 hCode n12 lf x rcs

------------------------------------------------------------------------
-- encAxTreeEqLN: axTreeEqLN a b.  Tag n14.  Body = Pair aC bC.
--
-- Correctness: thmT hCode (encAxTreeEqLN aC bC)
--   = codeEqn (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)) reified.

encAxTreeEqLN : Term -> Term -> Term
encAxTreeEqLN aC bC = ap2 Pair (reify (natCode n14)) (ap2 Pair aC bC)

encAxTreeEqLNCorr : (hCode aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxTreeEqLN aC bC))
    (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair oCC
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))))))
      oneC))
encAxTreeEqLNCorr hCode aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR aC bC recs)
  (ruleTrans (ndBranchMiss n14 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n12 case12 (ndT13V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n14 n13 case13 (ndT14V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n14 case14 (ndT15V3 hCode) body recs)
  (mkEqFRed (mkAp2F (kF2 treeeqCFR) (kF2 oCC) (mkAp2F (kF2 pairCFR) origA origB))
            (kF2 oneC) enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair oCC
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))))))
    oneC
    (mkAp2FRed (kF2 treeeqCFR) (kF2 oCC) (mkAp2F (kF2 pairCFR) origA origB)
      enc recs treeeqCFR oCC
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
      (kF2Red treeeqCFR enc recs)
      (kF2Red oCC enc recs)
      (mkAp2FRed (kF2 pairCFR) origA origB enc recs pairCFR aC bC
        (kF2Red pairCFR enc recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs)))
    (kF2Red oneC enc recs))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n14)
  body : Term ; body = ap2 Pair aC bC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxTreeEqLNPass :
  (hCode : Term) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxTreeEqLN (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxTreeEqLN (reify (code a)) (reify (code b))) x) rcs))
encAxTreeEqLNPass hCode a b x rcs =
  passthroughSucV3 hCode n13 (nd (code a) (code b)) x rcs

------------------------------------------------------------------------
-- encAxTreeEqNL: axTreeEqNL a b.  Tag n15.  Body = Pair aC bC.
--
-- Correctness: thmT hCode (encAxTreeEqNL aC bC)
--   = codeEqn (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)) reified.

encAxTreeEqNL : Term -> Term -> Term
encAxTreeEqNL aC bC = ap2 Pair (reify (natCode n15)) (ap2 Pair aC bC)

encAxTreeEqNLCorr : (hCode aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxTreeEqNL aC bC))
    (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
        oCC)))
      oneC))
encAxTreeEqNLCorr hCode aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR aC bC recs)
  (ruleTrans (ndBranchMiss n15 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n12 case12 (ndT13V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n13 case13 (ndT14V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n15 n14 case14 (ndT15V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n15 case15 (ndT16V3 hCode) body recs)
  (mkEqFRed (mkAp2F (kF2 treeeqCFR) (mkAp2F (kF2 pairCFR) origA origB) (kF2 oCC))
            (kF2 oneC) enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
      oCC)))
    oneC
    (mkAp2FRed (kF2 treeeqCFR) (mkAp2F (kF2 pairCFR) origA origB) (kF2 oCC)
      enc recs treeeqCFR
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
      oCC
      (kF2Red treeeqCFR enc recs)
      (mkAp2FRed (kF2 pairCFR) origA origB enc recs pairCFR aC bC
        (kF2Red pairCFR enc recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs))
      (kF2Red oCC enc recs))
    (kF2Red oneC enc recs)))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n15)
  body : Term ; body = ap2 Pair aC bC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxTreeEqNLPass :
  (hCode : Term) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxTreeEqNL (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxTreeEqNL (reify (code a)) (reify (code b))) x) rcs))
encAxTreeEqNLPass hCode a b x rcs =
  passthroughSucV3 hCode n14 (nd (code a) (code b)) x rcs

------------------------------------------------------------------------
-- encAxTreeEqNN: axTreeEqNN a1 a2 b1 b2.  Tag n16.
-- Body = Pair a1C (Pair a2C (Pair b1C b2C)).
--
-- Correctness: thmT hCode (encAxTreeEqNN a1C a2C b1C b2C)
--   = codeEqn (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
--                  (ap2 IfLf (ap2 TreeEq a1 b1)
--                            (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O)))) reified.

encAxTreeEqNN : Term -> Term -> Term -> Term -> Term
encAxTreeEqNN a1C a2C b1C b2C =
  ap2 Pair (reify (natCode n16))
    (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C)))

encAxTreeEqNNCorr : (hCode a1C a2C b1C b2C : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxTreeEqNN a1C a2C b1C b2C))
    (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair a1C a2C)))
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair b1C b2C))))))
      (ap2 Pair reifyTagAp2 (ap2 Pair iflfCFR (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a1C b1C)))
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair
          (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a2C b2C))) oneC))))))))
encAxTreeEqNNCorr hCode a1C a2C b1C b2C {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
  (ruleTrans (ndBranchMiss n16 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n12 case12 (ndT13V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n13 case13 (ndT14V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n14 case14 (ndT15V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n16 n15 case15 (ndT16V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n16 case16 (ndT17V3 hCode) body recs)
  (mkEqFRed
    (mkAp2F (kF2 treeeqCFR) (mkAp2F (kF2 pairCFR) origA origB1)
                            (mkAp2F (kF2 pairCFR) origB2a origB2b))
    (mkAp2F (kF2 iflfCFR) (mkAp2F (kF2 treeeqCFR) origA origB2a)
                          (mkAp2F (kF2 pairCFR) (mkAp2F (kF2 treeeqCFR) origB1 origB2b)
                                                (kF2 oneC)))
    enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair a1C a2C)))
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair b1C b2C))))))
    (ap2 Pair reifyTagAp2 (ap2 Pair iflfCFR (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a1C b1C)))
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a2C b2C))) oneC))))))
    (mkAp2FRed (kF2 treeeqCFR) (mkAp2F (kF2 pairCFR) origA origB1)
                                (mkAp2F (kF2 pairCFR) origB2a origB2b) enc recs
      treeeqCFR
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair a1C a2C)))
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair b1C b2C)))
      (kF2Red treeeqCFR enc recs)
      (mkAp2FRed (kF2 pairCFR) origA origB1 enc recs pairCFR a1C a2C
        (kF2Red pairCFR enc recs)
        (origARed tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
        (origB1Red tagR a1C a2C (ap2 Pair b1C b2C) recs))
      (mkAp2FRed (kF2 pairCFR) origB2a origB2b enc recs pairCFR b1C b2C
        (kF2Red pairCFR enc recs)
        (origB2aRed tagR a1C a2C b1C b2C recs)
        (origB2bRed tagR a1C a2C b1C b2C recs)))
    (mkAp2FRed (kF2 iflfCFR) (mkAp2F (kF2 treeeqCFR) origA origB2a)
                              (mkAp2F (kF2 pairCFR) (mkAp2F (kF2 treeeqCFR) origB1 origB2b)
                                                    (kF2 oneC))
      enc recs iflfCFR
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a1C b1C)))
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a2C b2C))) oneC)))
      (kF2Red iflfCFR enc recs)
      (mkAp2FRed (kF2 treeeqCFR) origA origB2a enc recs treeeqCFR a1C b1C
        (kF2Red treeeqCFR enc recs)
        (origARed tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
        (origB2aRed tagR a1C a2C b1C b2C recs))
      (mkAp2FRed (kF2 pairCFR) (mkAp2F (kF2 treeeqCFR) origB1 origB2b) (kF2 oneC)
        enc recs pairCFR
        (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCFR (ap2 Pair a2C b2C)))
        oneC
        (kF2Red pairCFR enc recs)
        (mkAp2FRed (kF2 treeeqCFR) origB1 origB2b enc recs treeeqCFR a2C b2C
          (kF2Red treeeqCFR enc recs)
          (origB1Red tagR a1C a2C (ap2 Pair b1C b2C) recs)
          (origB2bRed tagR a1C a2C b1C b2C recs))
        (kF2Red oneC enc recs))))))))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n16)
  body : Term ; body = ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C))
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxTreeEqNNPass :
  (hCode : Term) (a1 a2 b1 b2 : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxTreeEqNN (reify (code a1)) (reify (code a2))
                                            (reify (code b1)) (reify (code b2))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxTreeEqNN (reify (code a1)) (reify (code a2))
                                            (reify (code b1)) (reify (code b2))) x) rcs))
encAxTreeEqNNPass hCode a1 a2 b1 b2 x rcs =
  passthroughSucV3 hCode n15
    (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))) x rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case26 (hCode-parameterised) at tag n26.

private
  n26 : Nat ; n26 = suc n25

ndDisp26V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n26)) d) r)
                 (ap2 (case26 hCode) (ap2 Pair (reify (natCode n26)) d) r))
ndDisp26V3Pub hCode d r =
  ruleTrans (ndBranchMiss n26 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n21 case21 (ndT22V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n22 case22 (ndT23V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n23 case23V3 (ndT24V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n24 case24 (ndT25V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n26 n25 case25 (ndT26V3 hCode) d r refl)
             (ndBranchHit n26 (case26 hCode) ndT27V3 d r))))))))))))))))))))))))))

------------------------------------------------------------------------
-- encRuleHyp: hypothesis encoding.  Tag n26.
--
-- Encoding: Pair (natCode n26) (Pair lC rC) where (lC, rC) are the codes
-- of the hypothesis equation's left/right sides.
-- Unique structure: the body literally IS hCode = reify (codeEqn (eqn l r))
-- = Pair lC rC.  The case26 (hCode) reduction then yields hCode itself.
--
-- Correctness: thmT (Pair lC rC) (encRuleHyp lC rC) = Pair lC rC.

encRuleHyp : Term -> Term -> Term
encRuleHyp lC rC = ap2 Pair (reify (natCode n26)) (ap2 Pair lC rC)

encRuleHypCorr : (lC rC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT (ap2 Pair lC rC)) (encRuleHyp lC rC))
                 (ap2 Pair lC rC))
encRuleHypCorr lC rC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR hCode)
  (ruleTrans (guardNdV3 hCode tagR lC rC recs)
  (ruleTrans (ndDisp26V3Pub hCode hCode recs)
             (case26Match hCode tagR recs)))
  where
  hCode : Term ; hCode = ap2 Pair lC rC
  tagR  : Term ; tagR  = reify (natCode n26)
  enc   : Term ; enc   = ap2 Pair tagR hCode
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) hCode)

encRuleHypPass :
  (hCode : Term) (lC rC : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encRuleHyp lC rC) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encRuleHyp lC rC) x) rcs))
encRuleHypPass hCode lC rC x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n25)) (ap2 Pair lC rC) x rcs

------------------------------------------------------------------------
-- encAxConst: axConst a b.  Tag n3.  Body = Pair aC bC.
--
-- Correctness: thmT hCode (encAxConst aC bC)
--   = codeEqn (eqn (ap2 Const a b) a) reified
--   = Pair (Pair tagAp2 (Pair constCF (Pair aC bC))) aC.

private
  constCF : Term ; constCF = reify (codeF2 Const)

encAxConst : Term -> Term -> Term
encAxConst aC bC = ap2 Pair (reify (natCode n3)) (ap2 Pair aC bC)

encAxConstCorr : (hCode aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxConst aC bC))
    (ap2 Pair (ap2 Pair reifyTagAp2 (ap2 Pair constCF (ap2 Pair aC bC)))
              aC))
encAxConstCorr hCode aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR aC bC recs)
  (ruleTrans (ndBranchMiss n3 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n3 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n3 n2 case2 (ndT3V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n3 case3 (ndT4V3 hCode) body recs)
  (mkEqFRed (mkAp2F (kF2 constCF) origA origB) origA enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair constCF (ap2 Pair aC bC)))
    aC
    (mkAp2FRed (kF2 constCF) origA origB enc recs constCF aC bC
      (kF2Red constCF enc recs)
      (origARed tagR aC bC recs)
      (origBRed tagR aC bC recs))
    (origARed tagR aC bC recs)))))))
  where
  tagR : Term ; tagR = reify (natCode n3)
  body : Term ; body = ap2 Pair aC bC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxConstPass :
  (hCode : Term) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxConst (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxConst (reify (code a)) (reify (code b))) x) rcs))
encAxConstPass hCode a b x rcs =
  passthroughSucV3 hCode n2 (nd (code a) (code b)) x rcs

------------------------------------------------------------------------
-- encAxComp: axComp f g t.  Tag n4.  Body = Pair fC (Pair gC tC).
--
-- Correctness: thmT hCode (encAxComp fC gC tC)
--   = codeEqn (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))) reified.

private
  compCTag : Term ; compCTag = reify (natCode (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))

encAxComp : Term -> Term -> Term -> Term
encAxComp fC gC tC = ap2 Pair (reify (natCode n4)) (ap2 Pair fC (ap2 Pair gC tC))

encAxCompCorr : (hCode fC gC tC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxComp fC gC tC))
    (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair compCTag (ap2 Pair fC gC)) tC))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC
        (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))))))
encAxCompCorr hCode fC gC tC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR fC (ap2 Pair gC tC) recs)
  (ruleTrans (ndBranchMiss n4 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n4 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n4 n2 case2 (ndT3V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n4 n3 case3 (ndT4V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n4 case4 (ndT5V3 hCode) body recs)
  (mkEqFRed (mkAp1F (Fan (kF2 compCTag) (Fan origA origB1 Pair) Pair) origB2)
            (mkAp1F origA (mkAp1F origB1 origB2)) enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair
      (ap2 Pair compCTag (ap2 Pair fC gC))
      tC))
    (ap2 Pair (reify tagAp1) (ap2 Pair fC
      (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))))
    (mkAp1FRed (Fan (kF2 compCTag) (Fan origA origB1 Pair) Pair) origB2
      enc recs
      (ap2 Pair compCTag (ap2 Pair fC gC))
      tC
      (ruleTrans (fanRed (kF2 compCTag) (Fan origA origB1 Pair) Pair enc recs)
      (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) enc recs)
                   (kF2Red compCTag enc recs))
      (congR Pair compCTag
        (ruleTrans (fanRed origA origB1 Pair enc recs)
        (ruleTrans (congL Pair (ap2 origB1 enc recs)
                     (origARed tagR fC (ap2 Pair gC tC) recs))
                   (congR Pair fC
                     (origB1Red tagR fC gC tC recs)))))))
      (origB2Red tagR fC gC tC recs))
    (mkAp1FRed origA (mkAp1F origB1 origB2) enc recs fC
      (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))
      (origARed tagR fC (ap2 Pair gC tC) recs)
      (mkAp1FRed origB1 origB2 enc recs gC tC
        (origB1Red tagR fC gC tC recs)
        (origB2Red tagR fC gC tC recs))))))))))
  where
  tagR : Term ; tagR = reify (natCode n4)
  body : Term ; body = ap2 Pair fC (ap2 Pair gC tC)
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxCompPass :
  (hCode : Term) (f g : Fun1) (t : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxComp (reify (codeF1 f)) (reify (codeF1 g))
                                        (reify (code t))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxComp (reify (codeF1 f)) (reify (codeF1 g))
                                        (reify (code t))) x) rcs))
encAxCompPass hCode f g t x rcs =
  passthroughSucV3 hCode n3 (nd (codeF1 f) (nd (codeF1 g) (code t))) x rcs

------------------------------------------------------------------------
-- encAxComp2: axComp2 h f g t.  Tag n5.
-- Body = Pair hhC (Pair fC (Pair gC tC)).
--
-- Correctness: thmT hCode (encAxComp2 hhC fC gC tC)
--   = codeEqn (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))) reified.

private
  comp2CTag : Term ; comp2CTag = reify (natCode (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))

encAxComp2 : Term -> Term -> Term -> Term -> Term
encAxComp2 hhC fC gC tC = ap2 Pair (reify (natCode n5))
  (ap2 Pair hhC (ap2 Pair fC (ap2 Pair gC tC)))

encAxComp2Corr : (hCode hhC fC gC tC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxComp2 hhC fC gC tC))
    (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair comp2CTag (ap2 Pair hhC (ap2 Pair fC gC)))
        tC))
      (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair
        (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
        (ap2 Pair (reify tagAp1) (ap2 Pair gC tC)))))))
encAxComp2Corr hCode hhC fC gC tC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR hhC (ap2 Pair fC (ap2 Pair gC tC)) recs)
  (ruleTrans (ndBranchMiss n5 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n5 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n5 n2 case2 (ndT3V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n5 n3 case3 (ndT4V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n5 n4 case4 (ndT5V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n5 case5 (ndT6V3 hCode) body recs)
  (mkEqFRed
    (mkAp1F (Fan (kF2 comp2CTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origB2b)
    (mkAp2F origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b))
    enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair
      (ap2 Pair comp2CTag (ap2 Pair hhC (ap2 Pair fC gC)))
      tC))
    (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
      (ap2 Pair (reify tagAp1) (ap2 Pair gC tC)))))
    (mkAp1FRed
      (Fan (kF2 comp2CTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) origB2b
      enc recs
      (ap2 Pair comp2CTag (ap2 Pair hhC (ap2 Pair fC gC)))
      tC
      (ruleTrans (fanRed (kF2 comp2CTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair enc recs)
      (ruleTrans (congL Pair (ap2 (Fan origA (Fan origB1 origB2a Pair) Pair) enc recs)
                   (kF2Red comp2CTag enc recs))
      (congR Pair comp2CTag
        (ruleTrans (fanRed origA (Fan origB1 origB2a Pair) Pair enc recs)
        (ruleTrans (congL Pair (ap2 (Fan origB1 origB2a Pair) enc recs)
                     (origARed tagR hhC (ap2 Pair fC (ap2 Pair gC tC)) recs))
        (congR Pair hhC
          (ruleTrans (fanRed origB1 origB2a Pair enc recs)
          (ruleTrans (congL Pair (ap2 origB2a enc recs)
                       (origB1Red tagR hhC fC (ap2 Pair gC tC) recs))
                     (congR Pair fC
                       (origB2aRed tagR hhC fC gC tC recs))))))))))
      (origB2bRed tagR hhC fC gC tC recs))
    (mkAp2FRed origA (mkAp1F origB1 origB2b) (mkAp1F origB2a origB2b) enc recs
      hhC
      (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
      (ap2 Pair (reify tagAp1) (ap2 Pair gC tC))
      (origARed tagR hhC (ap2 Pair fC (ap2 Pair gC tC)) recs)
      (mkAp1FRed origB1 origB2b enc recs fC tC
        (origB1Red tagR hhC fC (ap2 Pair gC tC) recs)
        (origB2bRed tagR hhC fC gC tC recs))
      (mkAp1FRed origB2a origB2b enc recs gC tC
        (origB2aRed tagR hhC fC gC tC recs)
        (origB2bRed tagR hhC fC gC tC recs)))))))))))
  where
  tagR : Term ; tagR = reify (natCode n5)
  body : Term ; body = ap2 Pair hhC (ap2 Pair fC (ap2 Pair gC tC))
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxComp2Pass :
  (hCode : Term) (h : Fun2) (f g : Fun1) (t : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxComp2 (reify (codeF2 h)) (reify (codeF1 f))
                                         (reify (codeF1 g)) (reify (code t))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxComp2 (reify (codeF2 h)) (reify (codeF1 f))
                                         (reify (codeF1 g)) (reify (code t))) x) rcs))
encAxComp2Pass hCode h f g t x rcs =
  passthroughSucV3 hCode n4
    (nd (codeF2 h) (nd (codeF1 f) (nd (codeF1 g) (code t)))) x rcs

------------------------------------------------------------------------
-- encAxLift: axLift f a b.  Tag n6.
-- Body = Pair fC (Pair aC bC).
-- Correctness: thmT hCode (encAxLift fC aC bC)
--   = codeEqn (eqn (ap2 (Lift f) a b) (ap1 f a)) reified.

private
  liftCTag : Term ; liftCTag = reify (natCode (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))

encAxLift : Term -> Term -> Term -> Term
encAxLift fC aC bC = ap2 Pair (reify (natCode n6)) (ap2 Pair fC (ap2 Pair aC bC))

encAxLiftCorr : (hCode fC aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxLift fC aC bC))
    (ap2 Pair
      (ap2 Pair (reify tagAp2) (ap2 Pair
        (ap2 Pair liftCTag fC)
        (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC aC))))
encAxLiftCorr hCode fC aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR fC (ap2 Pair aC bC) recs)
  (ruleTrans (ndBranchMiss n6 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n6 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n6 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n6 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n6 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n6 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchHit n6 case6 (ndT7V3 hCode) body recs)
  (mkEqFRed (mkAp2F (Fan (kF2 liftCTag) origA Pair) origB1 origB2)
            (mkAp1F origA origB1) enc recs
    (ap2 Pair (reify tagAp2) (ap2 Pair
      (ap2 Pair liftCTag fC)
      (ap2 Pair aC bC)))
    (ap2 Pair (reify tagAp1) (ap2 Pair fC aC))
    (mkAp2FRed (Fan (kF2 liftCTag) origA Pair) origB1 origB2 enc recs
      (ap2 Pair liftCTag fC) aC bC
      (ruleTrans (fanRed (kF2 liftCTag) origA Pair enc recs)
      (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red liftCTag enc recs))
                 (congR Pair liftCTag (origARed tagR fC (ap2 Pair aC bC) recs))))
      (origB1Red tagR fC aC bC recs)
      (origB2Red tagR fC aC bC recs))
    (mkAp1FRed origA origB1 enc recs fC aC
      (origARed tagR fC (ap2 Pair aC bC) recs)
      (origB1Red tagR fC aC bC recs)))))))))))
  where
  tagR : Term ; tagR = reify (natCode n6)
  body : Term ; body = ap2 Pair fC (ap2 Pair aC bC)
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxLiftPass :
  (hCode : Term) (f : Fun1) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxLift (reify (codeF1 f)) (reify (code a))
                                        (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxLift (reify (codeF1 f)) (reify (code a))
                                        (reify (code b))) x) rcs))
encAxLiftPass hCode f a b x rcs =
  passthroughSucV3 hCode n5 (nd (codeF1 f) (nd (code a) (code b))) x rcs

------------------------------------------------------------------------
-- encAxPost: axPost f h a b.  Tag n7.
-- Body = Pair fC (Pair hhC (Pair aC bC)).
-- Correctness: thmT hCode (encAxPost fC hhC aC bC)
--   = codeEqn (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))) reified.

private
  postCTag : Term ; postCTag = reify (natCode (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))

encAxPost : Term -> Term -> Term -> Term -> Term
encAxPost fC hhC aC bC = ap2 Pair (reify (natCode n7))
  (ap2 Pair fC (ap2 Pair hhC (ap2 Pair aC bC)))

encAxPostCorr : (hCode fC hhC aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxPost fC hhC aC bC))
    (ap2 Pair
      (ap2 Pair (reify tagAp2) (ap2 Pair
        (ap2 Pair postCTag (ap2 Pair fC hhC))
        (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC
        (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair aC bC)))))))
encAxPostCorr hCode fC hhC aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR fC (ap2 Pair hhC (ap2 Pair aC bC)) recs)
  (ruleTrans (ndBranchMiss n7 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n7 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n7 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n7 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n7 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n7 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n7 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchHit n7 case7 (ndT8V3 hCode) body recs)
  (mkEqFRed
    (mkAp2F (Fan (kF2 postCTag) (Fan origA origB1 Pair) Pair) origB2a origB2b)
    (mkAp1F origA (mkAp2F origB1 origB2a origB2b))
    enc recs
    (ap2 Pair (reify tagAp2) (ap2 Pair
      (ap2 Pair postCTag (ap2 Pair fC hhC))
      (ap2 Pair aC bC)))
    (ap2 Pair (reify tagAp1) (ap2 Pair fC
      (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair aC bC)))))
    (mkAp2FRed (Fan (kF2 postCTag) (Fan origA origB1 Pair) Pair) origB2a origB2b
      enc recs
      (ap2 Pair postCTag (ap2 Pair fC hhC))
      aC bC
      (ruleTrans (fanRed (kF2 postCTag) (Fan origA origB1 Pair) Pair enc recs)
      (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) enc recs)
                   (kF2Red postCTag enc recs))
      (congR Pair postCTag
        (ruleTrans (fanRed origA origB1 Pair enc recs)
        (ruleTrans (congL Pair (ap2 origB1 enc recs)
                     (origARed tagR fC (ap2 Pair hhC (ap2 Pair aC bC)) recs))
                   (congR Pair fC
                     (origB1Red tagR fC hhC (ap2 Pair aC bC) recs)))))))
      (origB2aRed tagR fC hhC aC bC recs)
      (origB2bRed tagR fC hhC aC bC recs))
    (mkAp1FRed origA (mkAp2F origB1 origB2a origB2b) enc recs fC
      (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair aC bC)))
      (origARed tagR fC (ap2 Pair hhC (ap2 Pair aC bC)) recs)
      (mkAp2FRed origB1 origB2a origB2b enc recs hhC aC bC
        (origB1Red tagR fC hhC (ap2 Pair aC bC) recs)
        (origB2aRed tagR fC hhC aC bC recs)
        (origB2bRed tagR fC hhC aC bC recs)))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n7)
  body : Term ; body = ap2 Pair fC (ap2 Pair hhC (ap2 Pair aC bC))
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxPostPass :
  (hCode : Term) (f : Fun1) (h : Fun2) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxPost (reify (codeF1 f)) (reify (codeF2 h))
                                        (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxPost (reify (codeF1 f)) (reify (codeF2 h))
                                        (reify (code a)) (reify (code b))) x) rcs))
encAxPostPass hCode f h a b x rcs =
  passthroughSucV3 hCode n6 (nd (codeF1 f) (nd (codeF2 h) (nd (code a) (code b)))) x rcs

------------------------------------------------------------------------
-- encAxFan: axFan h1 h2 h a b.  Tag n8.
-- Body = Pair h1C (Pair h2C (Pair hhC (Pair aC bC))).
-- Correctness: codeEqn (eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b))).

private
  fanCTag : Term ; fanCTag = reify (natCode (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))
  ob2b1F : Fun2 ; ob2b1F = Post Fst origB2b
  ob2b2F : Fun2 ; ob2b2F = Post Snd origB2b

encAxFan : Term -> Term -> Term -> Term -> Term -> Term
encAxFan h1C h2C hhC aC bC = ap2 Pair (reify (natCode n8))
  (ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hhC (ap2 Pair aC bC))))

encAxFanCorr : (hCode h1C h2C hhC aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxFan h1C h2C hhC aC bC))
    (ap2 Pair
      (ap2 Pair (reify tagAp2) (ap2 Pair
        (ap2 Pair fanCTag (ap2 Pair h1C (ap2 Pair h2C hhC)))
        (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC))))))))
encAxFanCorr hCode h1C h2C hhC aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR h1C (ap2 Pair h2C (ap2 Pair hhC (ap2 Pair aC bC))) recs)
  (ruleTrans (ndBranchMiss n8 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n2 case2 (ndT3V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n3 case3 (ndT4V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n4 case4 (ndT5V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n5 case5 (ndT6V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n6 case6 (ndT7V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n8 n7 case7 (ndT8V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n8 case8 (ndT9V3 hCode) body recs)
  (mkEqFRed
    (mkAp2F (Fan (kF2 fanCTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) ob2b1F ob2b2F)
    (mkAp2F origB2a (mkAp2F origA ob2b1F ob2b2F) (mkAp2F origB1 ob2b1F ob2b2F))
    enc recs
    (ap2 Pair (reify tagAp2) (ap2 Pair (ap2 Pair fanCTag (ap2 Pair h1C (ap2 Pair h2C hhC))) (ap2 Pair aC bC)))
    (ap2 Pair (reify tagAp2) (ap2 Pair hhC (ap2 Pair
      (ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC))))))
    (mkAp2FRed (Fan (kF2 fanCTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair) ob2b1F ob2b2F
      enc recs (ap2 Pair fanCTag (ap2 Pair h1C (ap2 Pair h2C hhC))) aC bC
      (ruleTrans (fanRed (kF2 fanCTag) (Fan origA (Fan origB1 origB2a Pair) Pair) Pair enc recs)
      (ruleTrans (congL Pair (ap2 (Fan origA (Fan origB1 origB2a Pair) Pair) enc recs) (kF2Red fanCTag enc recs))
      (congR Pair fanCTag
        (ruleTrans (fanRed origA (Fan origB1 origB2a Pair) Pair enc recs)
        (ruleTrans (congL Pair (ap2 (Fan origB1 origB2a Pair) enc recs)
                     (origARed tagR h1C (ap2 Pair h2C (ap2 Pair hhC (ap2 Pair aC bC))) recs))
        (congR Pair h1C
          (ruleTrans (fanRed origB1 origB2a Pair enc recs)
          (ruleTrans (congL Pair (ap2 origB2a enc recs)
                       (origB1Red tagR h1C h2C (ap2 Pair hhC (ap2 Pair aC bC)) recs))
                     (congR Pair h2C (origB2aRed tagR h1C h2C hhC (ap2 Pair aC bC) recs))))))))))
      (origB2b1Red tagR h1C h2C hhC aC bC recs)
      (origB2b2Red tagR h1C h2C hhC aC bC recs))
    (mkAp2FRed origB2a (mkAp2F origA ob2b1F ob2b2F) (mkAp2F origB1 ob2b1F ob2b2F)
      enc recs hhC
      (ap2 Pair (reify tagAp2) (ap2 Pair h1C (ap2 Pair aC bC)))
      (ap2 Pair (reify tagAp2) (ap2 Pair h2C (ap2 Pair aC bC)))
      (origB2aRed tagR h1C h2C hhC (ap2 Pair aC bC) recs)
      (mkAp2FRed origA ob2b1F ob2b2F enc recs h1C aC bC
        (origARed tagR h1C (ap2 Pair h2C (ap2 Pair hhC (ap2 Pair aC bC))) recs)
        (origB2b1Red tagR h1C h2C hhC aC bC recs)
        (origB2b2Red tagR h1C h2C hhC aC bC recs))
      (mkAp2FRed origB1 ob2b1F ob2b2F enc recs h2C aC bC
        (origB1Red tagR h1C h2C (ap2 Pair hhC (ap2 Pair aC bC)) recs)
        (origB2b1Red tagR h1C h2C hhC aC bC recs)
        (origB2b2Red tagR h1C h2C hhC aC bC recs))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n8)
  body : Term ; body = ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hhC (ap2 Pair aC bC)))
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxFanPass :
  (hCode : Term) (h1 h2 h : Fun2) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxFan (reify (codeF2 h1)) (reify (codeF2 h2))
                                       (reify (codeF2 h)) (reify (code a))
                                       (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxFan (reify (codeF2 h1)) (reify (codeF2 h2))
                                       (reify (codeF2 h)) (reify (code a))
                                       (reify (code b))) x) rcs))
encAxFanPass hCode h1 h2 h a b x rcs =
  passthroughSucV3 hCode n7
    (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h) (nd (code a) (code b))))) x rcs

------------------------------------------------------------------------
-- encAxRecLf: axRecLf z s.  Tag n9.  Body = Pair zC sC.
-- Correctness: thmT hCode (encAxRecLf zC sC)
--   = codeEqn (eqn (ap1 (Rec z s) O) z) reified.

private
  recTagC : Term ; recTagC = reify (natCode (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))

encAxRecLf : Term -> Term -> Term
encAxRecLf zC sC = ap2 Pair (reify (natCode n9)) (ap2 Pair zC sC)

encAxRecLfCorr : (hCode zC sC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxRecLf zC sC))
    (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair recTagC (ap2 Pair zC sC))
        oCC))
      zC))
encAxRecLfCorr hCode zC sC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR zC sC recs)
  (ruleTrans (ndBranchMiss n9 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n2 case2 (ndT3V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n3 case3 (ndT4V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n4 case4 (ndT5V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n5 case5 (ndT6V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n6 case6 (ndT7V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n7 case7 (ndT8V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n9 n8 case8 (ndT9V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n9 case9 (ndT10V3 hCode) body recs)
  (mkEqFRed (mkAp1F (Fan (kF2 recTagC) (Fan origA origB Pair) Pair) (kF2 oCC))
            origA enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair
      (ap2 Pair recTagC (ap2 Pair zC sC))
      oCC))
    zC
    (mkAp1FRed (Fan (kF2 recTagC) (Fan origA origB Pair) Pair) (kF2 oCC)
      enc recs
      (ap2 Pair recTagC (ap2 Pair zC sC))
      oCC
      (ruleTrans (fanRed (kF2 recTagC) (Fan origA origB Pair) Pair enc recs)
      (ruleTrans (congL Pair (ap2 (Fan origA origB Pair) enc recs)
                   (kF2Red recTagC enc recs))
      (congR Pair recTagC
        (ruleTrans (fanRed origA origB Pair enc recs)
        (ruleTrans (congL Pair (ap2 origB enc recs)
                     (origARed tagR zC sC recs))
                   (congR Pair zC
                     (origBRed tagR zC sC recs)))))))
      (kF2Red oCC enc recs))
    (origARed tagR zC sC recs)))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n9)
  body : Term ; body = ap2 Pair zC sC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxRecLfPass :
  (hCode : Term) (z : Term) (s : Fun2) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxRecLf (reify (code z)) (reify (codeF2 s))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxRecLf (reify (code z)) (reify (codeF2 s))) x) rcs))
encAxRecLfPass hCode z s x rcs =
  passthroughSucV3 hCode n8 (nd (code z) (codeF2 s)) x rcs

------------------------------------------------------------------------
-- encAxRecNd: axRecNd z s a b.  Tag n10.
-- Body = Pair zC (Pair sC (Pair aC bC)).

encAxRecNd : Term -> Term -> Term -> Term -> Term
encAxRecNd zC sC aC bC = ap2 Pair (reify (natCode n10))
  (ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC)))

encAxRecNdCorr : (hCode zC sC aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxRecNd zC sC aC bC))
    (ap2 Pair
      (ap2 Pair (reify tagAp1) (ap2 Pair
        (ap2 Pair recTagC (ap2 Pair zC sC))
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))))
      (ap2 Pair reifyTagAp2 (ap2 Pair sC (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair
          (ap2 Pair (reify tagAp1) (ap2 Pair
            (ap2 Pair recTagC (ap2 Pair zC sC)) aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair
            (ap2 Pair recTagC (ap2 Pair zC sC)) bC))))))))))
encAxRecNdCorr hCode zC sC aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR zC (ap2 Pair sC (ap2 Pair aC bC)) recs)
  (ruleTrans (ndBranchMiss n10 n0 case0 (ndT1V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n1 case1 (ndT2V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n2 case2 (ndT3V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n3 case3 (ndT4V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n4 case4 (ndT5V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n5 case5 (ndT6V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n6 case6 (ndT7V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n7 case7 (ndT8V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n8 case8 (ndT9V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n10 n9 case9 (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n10 case10 (ndT11V3 hCode) body recs)
  (mkEqFRed (mkAp1F recF pairAB)
            (mkAp2F origB1 pairAB (mkAp2F (kF2 pairCFR) (mkAp1F recF origB2a) (mkAp1F recF origB2b)))
    enc recs
    (ap2 Pair (reify tagAp1) (ap2 Pair recFVal pairABVal))
    (ap2 Pair reifyTagAp2 (ap2 Pair sC (ap2 Pair pairABVal
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair
        (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
        (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC))))))))
    (mkAp1FRed recF pairAB enc recs recFVal pairABVal recFPf pairABPf)
    (mkAp2FRed origB1 pairAB
      (mkAp2F (kF2 pairCFR) (mkAp1F recF origB2a) (mkAp1F recF origB2b))
      enc recs sC pairABVal
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair
        (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
        (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC)))))
      (origB1Red tagR zC sC (ap2 Pair aC bC) recs)
      pairABPf
      (mkAp2FRed (kF2 pairCFR) (mkAp1F recF origB2a) (mkAp1F recF origB2b) enc recs
        pairCFR
        (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
        (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC))
        (kF2Red pairCFR enc recs)
        (mkAp1FRed recF origB2a enc recs recFVal aC recFPf
          (origB2aRed tagR zC sC aC bC recs))
        (mkAp1FRed recF origB2b enc recs recFVal bC recFPf
          (origB2bRed tagR zC sC aC bC recs)))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n10)
  body : Term ; body = ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC))
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  recF : Fun2 ; recF = Fan (kF2 recTagC) (Fan origA origB1 Pair) Pair
  pairAB : Fun2 ; pairAB = mkAp2F (kF2 pairCFR) origB2a origB2b

  recFVal : Term ; recFVal = ap2 Pair recTagC (ap2 Pair zC sC)
  pairABVal : Term
  pairABVal = ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))

  recFPf : Deriv hyp (eqn (ap2 recF enc recs) recFVal)
  recFPf =
    ruleTrans (fanRed (kF2 recTagC) (Fan origA origB1 Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) enc recs) (kF2Red recTagC enc recs))
    (congR Pair recTagC
      (ruleTrans (fanRed origA origB1 Pair enc recs)
      (ruleTrans (congL Pair (ap2 origB1 enc recs)
                   (origARed tagR zC (ap2 Pair sC (ap2 Pair aC bC)) recs))
                 (congR Pair zC (origB1Red tagR zC sC (ap2 Pair aC bC) recs))))))

  pairABPf : Deriv hyp (eqn (ap2 pairAB enc recs) pairABVal)
  pairABPf =
    mkAp2FRed (kF2 pairCFR) origB2a origB2b enc recs pairCFR aC bC
      (kF2Red pairCFR enc recs)
      (origB2aRed tagR zC sC aC bC recs)
      (origB2bRed tagR zC sC aC bC recs)

encAxRecNdPass :
  (hCode : Term) (z : Term) (s : Fun2) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxRecNd (reify (code z)) (reify (codeF2 s))
                                         (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxRecNd (reify (code z)) (reify (codeF2 s))
                                         (reify (code a)) (reify (code b))) x) rcs))
encAxRecNdPass hCode z s a b x rcs =
  passthroughSucV3 hCode n9 (nd (code z) (nd (codeF2 s) (nd (code a) (code b)))) x rcs

------------------------------------------------------------------------
-- encAxIfLfL: axIfLfL a b.  Tag n11.  Body = Pair aC bC.

encAxIfLfL : Term -> Term -> Term
encAxIfLfL aC bC = ap2 Pair (reify (natCode n11)) (ap2 Pair aC bC)

encAxIfLfLCorr : (hCode aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxIfLfL aC bC))
    (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair iflfCFR (ap2 Pair oCC
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))))))
      aC))
encAxIfLfLCorr hCode aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR aC bC recs)
  (ruleTrans (ndBranchMiss n11 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n11 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n11 case11 (ndT12V3 hCode) body recs)
  (mkEqFRed (mkAp2F (kF2 iflfCFR) (kF2 oCC) (mkAp2F (kF2 pairCFR) origA origB))
            origA enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair iflfCFR (ap2 Pair oCC
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))))))
    aC
    (mkAp2FRed (kF2 iflfCFR) (kF2 oCC) (mkAp2F (kF2 pairCFR) origA origB)
      enc recs iflfCFR oCC
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
      (kF2Red iflfCFR enc recs)
      (kF2Red oCC enc recs)
      (mkAp2FRed (kF2 pairCFR) origA origB enc recs pairCFR aC bC
        (kF2Red pairCFR enc recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs)))
    (origARed tagR aC bC recs)))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n11)
  body : Term ; body = ap2 Pair aC bC
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxIfLfLPass :
  (hCode : Term) (a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxIfLfL (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxIfLfL (reify (code a)) (reify (code b))) x) rcs))
encAxIfLfLPass hCode a b x rcs =
  passthroughSucV3 hCode n10 (nd (code a) (code b)) x rcs

------------------------------------------------------------------------
-- encAxIfLfN: axIfLfN x y a b.  Tag n12.
-- Body = Pair xC (Pair yC (Pair aC bC)).

encAxIfLfN : Term -> Term -> Term -> Term -> Term
encAxIfLfN xC yC aC bC = ap2 Pair (reify (natCode n12))
  (ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC)))

encAxIfLfNCorr : (hCode xC yC aC bC : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxIfLfN xC yC aC bC))
    (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair iflfCFR (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair xC yC)))
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))))))
      bC))
encAxIfLfNCorr hCode xC yC aC bC {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR xC (ap2 Pair yC (ap2 Pair aC bC)) recs)
  (ruleTrans (ndBranchMiss n12 n0  case0  (ndT1V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n1  case1  (ndT2V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n2  case2  (ndT3V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n3  case3  (ndT4V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n4  case4  (ndT5V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n5  case5  (ndT6V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n6  case6  (ndT7V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n7  case7  (ndT8V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n8  case8  (ndT9V3  hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n9  case9  (ndT10V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n10 case10 (ndT11V3 hCode) body recs refl)
  (ruleTrans (ndBranchMiss n12 n11 case11 (ndT12V3 hCode) body recs refl)
  (ruleTrans (ndBranchHit n12 case12 (ndT13V3 hCode) body recs)
  (mkEqFRed
    (mkAp2F (kF2 iflfCFR) (mkAp2F (kF2 pairCFR) origA origB1)
                          (mkAp2F (kF2 pairCFR) origB2a origB2b))
    origB2b enc recs
    (ap2 Pair reifyTagAp2 (ap2 Pair iflfCFR (ap2 Pair
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair xC yC)))
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC))))))
    bC
    (mkAp2FRed (kF2 iflfCFR) (mkAp2F (kF2 pairCFR) origA origB1)
                             (mkAp2F (kF2 pairCFR) origB2a origB2b) enc recs
      iflfCFR
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair xC yC)))
      (ap2 Pair reifyTagAp2 (ap2 Pair pairCFR (ap2 Pair aC bC)))
      (kF2Red iflfCFR enc recs)
      (mkAp2FRed (kF2 pairCFR) origA origB1 enc recs pairCFR xC yC
        (kF2Red pairCFR enc recs)
        (origARed tagR xC (ap2 Pair yC (ap2 Pair aC bC)) recs)
        (origB1Red tagR xC yC (ap2 Pair aC bC) recs))
      (mkAp2FRed (kF2 pairCFR) origB2a origB2b enc recs pairCFR aC bC
        (kF2Red pairCFR enc recs)
        (origB2aRed tagR xC yC aC bC recs)
        (origB2bRed tagR xC yC aC bC recs)))
    (origB2bRed tagR xC yC aC bC recs))))))))))))))))
  where
  tagR : Term ; tagR = reify (natCode n12)
  body : Term ; body = ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC))
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

encAxIfLfNPass :
  (hCode : Term) (x y a b : Term) (x' rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxIfLfN (reify (code x)) (reify (code y))
                                         (reify (code a)) (reify (code b))) x') rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxIfLfN (reify (code x)) (reify (code y))
                                         (reify (code a)) (reify (code b))) x') rcs))
encAxIfLfNPass hCode x y a b x' rcs =
  passthroughSucV3 hCode n11
    (nd (code x) (nd (code y) (nd (code a) (code b)))) x' rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case27, case28 (for RecP axioms).

private
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n33 : Nat ; n33 = suc (suc (suc (suc (suc n28))))

  tagAp2T : Term ; tagAp2T = reify tagAp2
  n26T    : Term ; n26T    = reify (natCode n26)
  n33T    : Term ; n33T    = reify (natCode n33)

ndDisp27V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n27)) d) r)
                 (ap2 case27 (ap2 Pair (reify (natCode n27)) d) r))
ndDisp27V3Pub hCode d r =
  ruleTrans (ndBranchMiss n27 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n21 case21 (ndT22V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n22 case22 (ndT23V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n23 case23V3 (ndT24V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n24 case24 (ndT25V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n25 case25 (ndT26V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n27 n26 (case26 hCode) ndT27V3 d r refl)
             (ndBranchHit n27 case27 ndT28V3 d r)))))))))))))))))))))))))))

ndDisp28V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n28)) d) r)
                 (ap2 case28 (ap2 Pair (reify (natCode n28)) d) r))
ndDisp28V3Pub hCode d r =
  ruleTrans (ndBranchMiss n28 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n21 case21 (ndT22V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n22 case22 (ndT23V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n23 case23V3 (ndT24V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n24 case24 (ndT25V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n25 case25 (ndT26V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n28 n26 (case26 hCode) ndT27V3 d r refl)
  (ruleTrans (ndBranchMiss n28 n27 case27 ndT28V3 d r refl)
             (ndBranchHit n28 case28 ndT29V3 d r))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- encAxRecPLf: axRecPLf s p.  Tag n27.  Body = Pair sC pC.
-- Correctness: thmT hCode (encAxRecPLf sC pC)
--   = codeEqn (eqn (ap2 (RecP s) p O) O) reified.

encAxRecPLf : Term -> Term -> Term
encAxRecPLf sCr pCr = ap2 Pair (reify (natCode n27)) (ap2 Pair sCr pCr)

encAxRecPLfCorr : (hCode sCr pCr : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxRecPLf sCr pCr))
    (ap2 Pair
      (ap2 Pair tagAp2T
        (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr oCC)))
      oCC))
encAxRecPLfCorr hCode sCr pCr {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR sCr pCr recs)
  (ruleTrans (ndDisp27V3Pub hCode body recs)
    (mkEqFRed (mkAp2F recPCodeF origB (kF2 oCC)) (kF2 oCC) enc recs
      lhsReify oCC
      (mkAp2FRed recPCodeF origB (kF2 oCC) enc recs
        (ap2 Pair n33T sCr) pCr oCC
        recPCodeRed
        (origBRed tagR sCr pCr recs)
        (kF2Red oCC enc recs))
      (kF2Red oCC enc recs))))
  where
  tagR : Term ; tagR = reify (natCode n27)
  body : Term ; body = ap2 Pair sCr pCr
  enc  : Term ; enc  = ap2 Pair tagR body
  recs : Term
  recs = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  recPCodeF : Fun2
  recPCodeF = Fan (kF2 n33T) origA Pair

  recPCodeRed : Deriv hyp (eqn (ap2 recPCodeF enc recs) (ap2 Pair n33T sCr))
  recPCodeRed =
    ruleTrans (fanRed (kF2 n33T) origA Pair enc recs)
    (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red n33T enc recs))
               (congR Pair n33T (origARed tagR sCr pCr recs)))

  lhsReify : Term
  lhsReify = ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr oCC))

encAxRecPLfPass :
  (hCode : Term) (s : Fun2) (p : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxRecPLf (reify (codeF2 s)) (reify (code p))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxRecPLf (reify (codeF2 s)) (reify (code p))) x) rcs))
encAxRecPLfPass hCode s p x rcs =
  passthroughSucV3 hCode n26 (nd (codeF2 s) (code p)) x rcs

------------------------------------------------------------------------
-- encAxRecPNd: axRecPNd s p a b.  Tag n28.
-- Body = Pair sC (Pair pC (Pair aC bC)).

encAxRecPNd : Term -> Term -> Term -> Term -> Term
encAxRecPNd sCr pCr aCr bCr = ap2 Pair (reify (natCode n28))
  (ap2 Pair sCr (ap2 Pair pCr (ap2 Pair aCr bCr)))

encAxRecPNdCorr : (hCode sCr pCr aCr bCr : Term) {hyp : Equation} ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encAxRecPNd sCr pCr aCr bCr))
    (ap2 Pair
      (ap2 Pair tagAp2T (ap2 Pair
        (ap2 Pair n33T sCr)
        (ap2 Pair pCr
          (ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n26T O) (ap2 Pair aCr bCr))))))
      (ap2 Pair tagAp2T (ap2 Pair sCr (ap2 Pair
        (ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n26T O) (ap2 Pair pCr
          (ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n26T O) (ap2 Pair aCr bCr))))))
        (ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n26T O) (ap2 Pair
          (ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr aCr)))
          (ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr bCr)))))))))))
encAxRecPNdCorr hCode sCr pCr aCr bCr {hyp} =
  ruleTrans (recNdRed O (thmTStep hCode) tagR body)
  (ruleTrans (guardNdV3 hCode tagR sCr bInner recs)
  (ruleTrans (ndDisp28V3Pub hCode body recs)
    case28Red))
  where
  tagR    : Term ; tagR    = reify (natCode n28)
  bInner  : Term ; bInner  = ap2 Pair pCr (ap2 Pair aCr bCr)
  body    : Term ; body    = ap2 Pair sCr bInner
  enc     : Term ; enc     = ap2 Pair tagR body
  recs    : Term
  recs    = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  recPCodeF : Fun2
  recPCodeF = Fan (kF2 n33T) origA Pair
  pairF2F   : Fun2
  pairF2F   = Fan (kF2 n26T) (kF2 O) Pair

  origARedE : Deriv hyp (eqn (ap2 origA enc recs) sCr)
  origARedE = origARed tagR sCr bInner recs

  origB1RedE : Deriv hyp (eqn (ap2 origB1 enc recs) pCr)
  origB1RedE = origB1Red tagR sCr pCr (ap2 Pair aCr bCr) recs

  origB2aRedE : Deriv hyp (eqn (ap2 origB2a enc recs) aCr)
  origB2aRedE = origB2aRed tagR sCr pCr aCr bCr recs

  origB2bRedE : Deriv hyp (eqn (ap2 origB2b enc recs) bCr)
  origB2bRedE = origB2bRed tagR sCr pCr aCr bCr recs

  recPCodeRed : Deriv hyp (eqn (ap2 recPCodeF enc recs) (ap2 Pair n33T sCr))
  recPCodeRed =
    ruleTrans (fanRed (kF2 n33T) origA Pair enc recs)
    (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red n33T enc recs))
               (congR Pair n33T origARedE))

  pairF2FRed : Deriv hyp (eqn (ap2 pairF2F enc recs) (ap2 Pair n26T O))
  pairF2FRed =
    ruleTrans (fanRed (kF2 n26T) (kF2 O) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (kF2 O) enc recs) (kF2Red n26T enc recs))
               (congR Pair n26T (kF2Red O enc recs)))

  pairABReify : Term
  pairABReify = ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n26T O) (ap2 Pair aCr bCr))
  lhsReify : Term
  lhsReify =
    ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr pairABReify))
  xReify : Term
  xReify =
    ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n26T O) (ap2 Pair pCr pairABReify))
  recPaReify : Term
  recPaReify =
    ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr aCr))
  recPbReify : Term
  recPbReify =
    ap2 Pair tagAp2T (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr bCr))
  yReify : Term
  yReify =
    ap2 Pair tagAp2T
      (ap2 Pair (ap2 Pair n26T O) (ap2 Pair recPaReify recPbReify))
  rhsReify : Term
  rhsReify =
    ap2 Pair tagAp2T (ap2 Pair sCr (ap2 Pair xReify yReify))

  pairABRed : Deriv hyp (eqn (ap2 (mkAp2F pairF2F origB2a origB2b) enc recs) pairABReify)
  pairABRed =
    mkAp2FRed pairF2F origB2a origB2b enc recs
      (ap2 Pair n26T O) aCr bCr
      pairF2FRed origB2aRedE origB2bRedE

  lhsRed : Deriv hyp (eqn (ap2 (mkAp2F recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b))
                                enc recs) lhsReify)
  lhsRed =
    mkAp2FRed recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b) enc recs
      (ap2 Pair n33T sCr) pCr pairABReify
      recPCodeRed origB1RedE pairABRed

  xRed : Deriv hyp (eqn (ap2 (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
                              enc recs) xReify)
  xRed =
    mkAp2FRed pairF2F origB1 (mkAp2F pairF2F origB2a origB2b) enc recs
      (ap2 Pair n26T O) pCr pairABReify
      pairF2FRed origB1RedE pairABRed

  recPaRed : Deriv hyp (eqn (ap2 (mkAp2F recPCodeF origB1 origB2a) enc recs) recPaReify)
  recPaRed =
    mkAp2FRed recPCodeF origB1 origB2a enc recs
      (ap2 Pair n33T sCr) pCr aCr
      recPCodeRed origB1RedE origB2aRedE

  recPbRed : Deriv hyp (eqn (ap2 (mkAp2F recPCodeF origB1 origB2b) enc recs) recPbReify)
  recPbRed =
    mkAp2FRed recPCodeF origB1 origB2b enc recs
      (ap2 Pair n33T sCr) pCr bCr
      recPCodeRed origB1RedE origB2bRedE

  yRed : Deriv hyp (eqn (ap2 (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                                              (mkAp2F recPCodeF origB1 origB2b))
                              enc recs) yReify)
  yRed =
    mkAp2FRed pairF2F (mkAp2F recPCodeF origB1 origB2a)
                      (mkAp2F recPCodeF origB1 origB2b) enc recs
      (ap2 Pair n26T O) recPaReify recPbReify
      pairF2FRed recPaRed recPbRed

  rhsRed : Deriv hyp (eqn (ap2 (mkAp2F origA
                                 (mkAp2F pairF2F origB1
                                   (mkAp2F pairF2F origB2a origB2b))
                                 (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                                                 (mkAp2F recPCodeF origB1 origB2b)))
                              enc recs) rhsReify)
  rhsRed =
    mkAp2FRed origA (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
                    (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                                    (mkAp2F recPCodeF origB1 origB2b)) enc recs
      sCr xReify yReify
      origARedE xRed yRed

  case28Red : Deriv hyp (eqn (ap2 case28 enc recs) (ap2 Pair lhsReify rhsReify))
  case28Red =
    mkEqFRed (mkAp2F recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b))
             (mkAp2F origA
                     (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
                     (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                                     (mkAp2F recPCodeF origB1 origB2b)))
             enc recs lhsReify rhsReify lhsRed rhsRed

encAxRecPNdPass :
  (hCode : Term) (s : Fun2) (p a b : Term) (x rcs : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encAxRecPNd (reify (codeF2 s)) (reify (code p))
                                          (reify (code a)) (reify (code b))) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encAxRecPNd (reify (codeF2 s)) (reify (code p))
                                          (reify (code a)) (reify (code b))) x) rcs))
encAxRecPNdPass hCode s p a b x rcs =
  passthroughSucV3 hCode n27
    (nd (codeF2 s) (nd (code p) (nd (code a) (code b)))) x rcs

------------------------------------------------------------------------
-- Navigation: ndDispatchV3 -> case24 at tag n24 (ruleF / Schema F).

ndDisp24V3Pub : (hCode d r : Term) -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n24)) d) r)
                 (ap2 case24 (ap2 Pair (reify (natCode n24)) d) r))
ndDisp24V3Pub hCode d r =
  ruleTrans (ndBranchMiss n24 n0  case0  (ndT1V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n1  case1  (ndT2V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n2  case2  (ndT3V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n3  case3  (ndT4V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n4  case4  (ndT5V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n5  case5  (ndT6V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n6  case6  (ndT7V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n7  case7  (ndT8V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n8  case8  (ndT9V3  hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n9  case9  (ndT10V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n10 case10 (ndT11V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n11 case11 (ndT12V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n12 case12 (ndT13V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n13 case13 (ndT14V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n14 case14 (ndT15V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n15 case15 (ndT16V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n16 case16 (ndT17V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n17 case17 (ndT18V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n18 case18 (ndT19V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n19 case19V3 (ndT20V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n20 case20 (ndT21V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n21 case21 (ndT22V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n22 case22 (ndT23V3 hCode) d r refl)
  (ruleTrans (ndBranchMiss n24 n23 case23V3 (ndT24V3 hCode) d r refl)
             (ndBranchHit n24 case24 (ndT25V3 hCode) d r))))))))))))))))))))))))

------------------------------------------------------------------------
-- encRuleF: Schema F (uniqueness of tree recursion).  Tag n24.
--
-- Body shape:
--   Pair (Pair fC gC')                                -- functor codes
--        (Pair (Pair zC sC)                           -- base/step codes
--              (Pair (Pair sub1 sub2) (Pair sub3 sub4))) -- 4 sub-encodings
--
-- The 4 sub-encodings are the encoded sub-proofs that f, g both satisfy
-- the base equation  ap1 _ O = z  and the step equation
-- ap1 _ (Pair var0 var1) = ap2 s ... .  case24 dispatches purely on the
-- functor codes f, g and produces  codeEqn (eqn (ap1 f var0) (ap1 g var0))
-- without using the sub-encodings semantically — they are stored for
-- nested thm14EV3 reflection.
--
-- Caller supplies dispMiss for (Pair fC gC') tag-opacity (since it
-- depends on f's structure; f1gDispMissV3 in Guard.Thm14EV3 is the
-- corresponding case-splitting helper).
--
-- Note: v0C below is reify (code (var zero)) = Pair tagVarT O.

private
  v0CR : Term
  v0CR = reify (nd (nd (nd (nd lf lf) lf) lf) lf)

encRuleF : (f g : Fun1) (zC sC sub1 sub2 sub3 sub4 : Term) -> Term
encRuleF f g zC sC sub1 sub2 sub3 sub4 =
  ap2 Pair (reify (natCode n24))
    (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))
              (ap2 Pair (ap2 Pair zC sC)
                        (ap2 Pair (ap2 Pair sub1 sub2)
                                  (ap2 Pair sub3 sub4))))

encRuleFCorr :
  (hCode : Term) (f g : Fun1) (zC sC sub1 sub2 sub3 sub4 : Term)
  {hyp : Equation} ->
  ((x' rc' : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x') rc'))) ->
  Deriv hyp (eqn (ap1 (thmT hCode) (encRuleF f g zC sC sub1 sub2 sub3 sub4))
    (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) v0CR))
              (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 g)) v0CR))))
encRuleFCorr hCode f g zC sC sub1 sub2 sub3 sub4 {hyp} dispMiss =
  ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
  (ruleTrans (congR (thmTStep hCode) enc recsExpand)
  (ruleTrans (guardNdV3 hCode tagR aR bR recs')
  (ruleTrans (ndDisp24V3Pub hCode dat recs')
  (mkEqFRed (mkAp1F origAL (kF2 v0CR)) (mkAp1F origAR (kF2 v0CR)) enc recs'
    (ap2 Pair (reify tagAp1) (ap2 Pair fC v0CR))
    (ap2 Pair (reify tagAp1) (ap2 Pair gC' v0CR))
    (mkAp1FRed origAL (kF2 v0CR) enc recs' fC v0CR
      (origALRed tagR fC gC' bR recs')
      (kF2Red v0CR enc recs'))
    (mkAp1FRed origAR (kF2 v0CR) enc recs' gC' v0CR
      (origARRed tagR fC gC' bR recs')
      (kF2Red v0CR enc recs'))))))
  where
  fC      : Term ; fC      = reify (codeF1 f)
  gC'     : Term ; gC'     = reify (codeF1 g)
  tagR    : Term ; tagR    = reify (natCode n24)
  aR      : Term ; aR      = ap2 Pair fC gC'
  bChild1 : Term ; bChild1 = ap2 Pair zC sC
  bChild2 : Term ; bChild2 = ap2 Pair (ap2 Pair sub1 sub2) (ap2 Pair sub3 sub4)
  bR      : Term ; bR      = ap2 Pair bChild1 bChild2
  dat     : Term ; dat     = ap2 Pair aR bR
  enc     : Term ; enc     = ap2 Pair tagR dat
  recs'   : Term
  recs'   = ap2 Pair (ap1 (thmT hCode) tagR)
                     (ap2 Pair (ap1 (thmT hCode) aR) (ap1 (thmT hCode) bR))

  datExpand :
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap1 (thmT hCode) bR)))
  datExpand =
    intermediateGenericV3 hCode aR bR bChild1 bChild2
      (\x' rc' -> dispMiss x' rc')

  recsExpand :
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

encRuleFPass :
  (hCode : Term) (f g : Fun1) (zC sC sub1 sub2 sub3 sub4 : Term) (x rcs : Term)
  -> {hyp : Equation} ->
  Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                   (ap2 Pair (encRuleF f g zC sC sub1 sub2 sub3 sub4) x) rcs)
                 (ap2 sndArg2
                   (ap2 Pair (encRuleF f g zC sC sub1 sub2 sub3 sub4) x) rcs))
encRuleFPass hCode f g zC sC sub1 sub2 sub3 sub4 x rcs =
  ndDispatchV3PairMiss hCode O (reify (natCode n23))
    (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))
              (ap2 Pair (ap2 Pair zC sC)
                        (ap2 Pair (ap2 Pair sub1 sub2)
                                  (ap2 Pair sub3 sub4)))) x rcs
