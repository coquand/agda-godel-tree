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
