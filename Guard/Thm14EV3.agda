{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Thm14EV3 — hypothesis-aware Theorem 14.
--
-- Phase C of the Gödel-II redesign (see GODEL-II-REDESIGN.md).
--
-- ProofE3 H eq is a record containing an encoding term encT and a
-- proof that  ap1 (thmT (reify (codeEqn H))) encT = reify (codeEqn eq)
-- in every ambient hypothesis.  Constructors per rule of the
-- derivation system will be ported one at a time.
--
-- This file starts with the base case for axI (tag n0).

module Guard.Thm14EV3 where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.StepReduce
open import Guard.ThFun using (codeEqn)
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
open import Guard.SubstOp using (substOp ; substOpCorrect)

private
  n0 : Nat ; n0 = zero
  n1 : Nat ; n1 = suc n0
  n2 : Nat ; n2 = suc n1
  n3 : Nat ; n3 = suc n2
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
-- ProofE3: V3 correctness witness.
--
-- The H parameter is the ambient hypothesis used by the derivation
-- being witnessed.  hCode = reify (codeEqn H) is the Term encoding
-- of H passed to thmT.

record ProofE3 (H : Equation) (eq : Equation) : Set where
  constructor mkProofE3
  field
    pa : Tree
    pb : Tree
    corr : {hyp : Equation} ->
           Deriv hyp (eqn (ap1 (thmT (reify (codeEqn H)))
                              (ap2 Pair (reify pa) (reify pb)))
                          (reify (codeEqn eq)))
    pass : (x rcs : Term) -> {hyp : Equation} ->
           Deriv hyp (eqn (ap2 (ndDispatchV3 (reify (codeEqn H)))
                               (ap2 Pair (ap2 Pair (reify pa) (reify pb)) x) rcs)
                          (ap2 sndArg2 (ap2 Pair (ap2 Pair (reify pa) (reify pb)) x) rcs))
open ProofE3 public

-- Convenience: reified encoding as a Term.
encT : {H eq : Equation} -> ProofE3 H eq -> Term
encT pe = ap2 Pair (reify (pa pe)) (reify (pb pe))

------------------------------------------------------------------------
-- Case 0: axI t.
--
-- Encoding at Tree level:  encAxI (code t) = nd (natCode n0) (nd (code t) lf).
-- At Term level:            reify(encAxI (code t)) = ap2 Pair O (ap2 Pair tC O).
-- Expected conclusion:      codeEqn (eqn (ap1 I t) t).

thm14EV3AxI : (H : Equation) (t : Term) -> ProofE3 H (eqn (ap1 I t) t)
thm14EV3AxI H t = mkProofE3 (natCode n0) (nd (code t) lf) correct
  (\x' r' -> axIPassthroughV3 hCode t x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  tagR  : Term ; tagR  = O
  body  : Term ; body  = ap2 Pair tC O
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  codeIF : Term ; codeIF = reify (codeF1 I)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 I t) t))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR tC O recs)
    (ruleTrans (ndBranchHit n0 case0 (ndT1V3 hCode) body recs)
    (mkEqFRed (mkAp1F (kF2 codeIF) origA) origA enc recs
      (ap2 Pair (reify tagAp1) (ap2 Pair codeIF tC)) tC
      (mkAp1FRed (kF2 codeIF) origA enc recs codeIF tC
        (kF2Red codeIF enc recs)
        (origARed tagR tC O recs))
      (origARed tagR tC O recs))))

------------------------------------------------------------------------
-- Case 1: axFst a b.
--
-- Encoding at Tree level: encAxFst (code a) (code b) = nd (natCode n1) (nd (code a) (code b)).

thm14EV3AxFst : (H : Equation) (a b : Term) ->
                ProofE3 H (eqn (ap1 Fst (ap2 Pair a b)) a)
thm14EV3AxFst H a b = mkProofE3 (natCode n1) (nd (code a) (code b)) correct
  (\x' r' -> passthroughSucV3 hCode n0 (nd (code a) (code b)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n1)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  codeFstF : Term ; codeFstF = reify (codeF1 Fst)
  pairCF   : Term ; pairCF   = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 Fst (ap2 Pair a b)) a))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR aC bC recs)
    -- navigate ndDispatchV3 hCode from n0 (miss) to n1 (hit)
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

------------------------------------------------------------------------
-- Case 17: axRefl t.
--
-- Encoding: encRefl (code t) = nd (natCode n17) (nd (code t) lf).
-- At Term:  reify = Pair (reify(natCode n17)) (Pair tC O).
-- Conclusion: eqn t t, so codeEqn = nd (code t) (code t).

thm14EV3Refl : (H : Equation) (t : Term) -> ProofE3 H (eqn t t)
thm14EV3Refl H t = mkProofE3 (natCode n17) (nd (code t) lf) correct
  (\x' r' -> passthroughSucV3 hCode n16 (nd (code t) lf) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  tagR  : Term ; tagR  = reify (natCode n17)
  body  : Term ; body  = ap2 Pair tC O
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc) (reify (codeEqn (eqn t t))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR tC O recs)
    -- navigate from n0 through n16 (misses), hit at n17
    (ruleTrans (ndBranchMiss n17 n0  case0  (ndT1V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n1  case1  (ndT2V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n2  case2  (ndT3V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n3  case3  (ndT4V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n4  case4  (ndT5V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n5  case5  (ndT6V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n6  case6  (ndT7V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n7  case7  (ndT8V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n8  case8  (ndT9V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n9  case9  (ndT10V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n10 case10 (ndT11V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n11 case11 (ndT12V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n12 case12 (ndT13V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n13 case13 (ndT14V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n14 case14 (ndT15V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n15 case15 (ndT16V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n17 n16 case16 (ndT17V3 hCode) body recs refl)
    (ruleTrans (ndBranchHit n17 case17 (ndT18V3 hCode) body recs)
    (mkEqFRed origA origA enc recs tC tC
      (origARed tagR tC O recs)
      (origARed tagR tC O recs)))))))))))))))))))))

------------------------------------------------------------------------
-- Navigate ndDispatchV3 hCode from n0 past n0..n(k-1) to caseK, for
-- k = 18, 19, 20.  Private helpers used only by the composition cases.

private
  ndDisp18V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n18)) d) r)
                   (ap2 case18 (ap2 Pair (reify (natCode n18)) d) r))
  ndDisp18V3 hCode d r =
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

  ndDisp19V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n19)) d) r)
                   (ap2 case19V3 (ap2 Pair (reify (natCode n19)) d) r))
  ndDisp19V3 hCode d r =
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
-- Case 19: ruleTrans.  Composition of two ProofE3's.
--
-- Given  pe1 : ProofE3 H (eqn t u)  and  pe2 : ProofE3 H (eqn u v) ,
-- build  ProofE3 H (eqn t v) .
--
-- The encoding is  nd (natCode n19) (nd enc1 enc2)  — at Term level
-- Pair (natCode n19) (Pair (encT pe1) (encT pe2)).  The correctness
-- derivation uses intermediateGenericV3 (consuming pe1's pass) plus
-- corrPf1, corrPf2 (the corr fields of the two sub-proofs) to expand
-- recs into the shape case19 expects.

thm14EV3Trans : {H : Equation} {t u v : Term} ->
                ProofE3 H (eqn t u) -> ProofE3 H (eqn u v) ->
                ProofE3 H (eqn t v)
thm14EV3Trans {H} {t} {u} {v} pe1 pe2 =
  mkProofE3 (natCode n19) (nd (nd pa1 pb1) (nd pa2 pb2)) correct
    (\x' r' -> passthroughSucV3 hCode n18 (nd (nd pa1 pb1) (nd pa2 pb2)) x' r')
  where
  pa1 : Tree ; pa1 = pa pe1
  pb1 : Tree ; pb1 = pb pe1
  pa2 : Tree ; pa2 = pa pe2
  pb2 : Tree ; pb2 = pb pe2
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  uC    : Term ; uC    = reify (code u)
  vC    : Term ; vC    = reify (code v)
  sp1R  : Term ; sp1R  = ap2 Pair (reify pa1) (reify pb1)
  sp2R  : Term ; sp2R  = ap2 Pair (reify pa2) (reify pb2)
  tagR  : Term ; tagR  = reify (natCode n19)
  dat   : Term ; dat   = ap2 Pair sp1R sp2R
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC))

  -- Expand  thmT hCode dat  into  Pair (Pair tC uC) (Pair uC vC)  by
  -- passing through pe1's pass (which certifies sp1R is tag-opaque to
  -- ndDispatchV3) and then using the corr fields of both sub-proofs.
  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap2 Pair tC uC) (ap2 Pair uC vC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode sp1R sp2R (reify pa2) (reify pb2)
                (\x' rc' -> pass pe1 x' rc'))
    (ruleTrans (congL Pair (ap1 (thmT hCode) sp2R) (corr pe1))
               (congR Pair (ap2 Pair tC uC) (corr pe2)))

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc) (ap2 Pair tC vC))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR sp1R sp2R recs')
    (ruleTrans (ndDisp19V3 hCode dat recs')
               (case19V3Match tagR dat (ap1 (thmT hCode) tagR) tC uC vC))))

------------------------------------------------------------------------
-- Case 18: ruleSym.  One sub-proof.
--
-- Encoding: nd (natCode n18) (nd tagVar (nd pa pb))  where (pa, pb)
-- are the sub-proof components.  The presence of tagVar is a historical
-- quirk in the encoding (it is fixed data, not used as a variable).

thm14EV3Sym : {H : Equation} {t u : Term} ->
              ProofE3 H (eqn t u) -> ProofE3 H (eqn u t)
thm14EV3Sym {H} {t} {u} pe =
  mkProofE3 (natCode n18) (nd tagVar (nd pa1 pb1)) correct
    (\x' r' -> passthroughSucV3 hCode n17 (nd tagVar (nd pa1 pb1)) x' r')
  where
  pa1 : Tree ; pa1 = pa pe
  pb1 : Tree ; pb1 = pb pe
  hCode   : Term ; hCode   = reify (codeEqn H)
  tC      : Term ; tC      = reify (code t)
  uC      : Term ; uC      = reify (code u)
  spR     : Term ; spR     = ap2 Pair (reify pa1) (reify pb1)
  tagVarR : Term ; tagVarR = reify tagVar
  tagR    : Term ; tagR    = reify (natCode n18)
  dat     : Term ; dat     = ap2 Pair tagVarR spR
  enc     : Term ; enc     = ap2 Pair tagR dat
  recs'   : Term
  recs'   = ap2 Pair (ap1 (thmT hCode) tagR)
                     (ap2 Pair (ap1 (thmT hCode) tagVarR) (ap2 Pair tC uC))

  -- tagVar = nd (nd (nd lf lf) lf) lf , so reify tagVar has shape
  -- Pair (Pair (Pair O O) O) O — an instance of the Pair pattern needed
  -- by ndDispatchV3PairMiss.  Decomposing: a1 = Pair O O, a2 = O, b = O.
  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) tagVarR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode tagVarR spR (reify pa1) (reify pb1)
                (\x' rc' -> ndDispatchV3PairMiss hCode (ap2 Pair O O) O O x' rc'))
              (congR Pair (ap1 (thmT hCode) tagVarR) (corr pe))

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc) (ap2 Pair uC tC))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR tagVarR spR recs')
    (ruleTrans (ndDisp18V3 hCode dat recs')
    (mkEqFRed recsBR recsBL enc recs' uC tC
      (recsBRRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) tagVarR) tC uC)
      (recsBLRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) tagVarR) tC uC)))))

------------------------------------------------------------------------
-- f1DispMissV3: for every unary functor f, ndDispatchV3 misses at
-- the tag  reify (codeF1 f)  (it is always of Pair-Pair shape).
--
-- Mechanical case-split on f.  Each case reduces by Agda's
-- unfolding of codeF1 to a shape compatible with ndDispatchV3PairMiss.

private
  f1DispMissV3 : (hCode : Term) (f : Fun1) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (codeF1 f)) x') rc')
                   (ap2 sndArg2 (ap2 Pair (reify (codeF1 f)) x') rc'))
  f1DispMissV3 hCode I             x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode n25)) O x' rc'
  f1DispMissV3 hCode Fst           x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc n25))) O x' rc'
  f1DispMissV3 hCode Snd           x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc n25)))) O x' rc'
  f1DispMissV3 hCode (Comp f g)    x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc n25)))))
      (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x' rc'
  f1DispMissV3 hCode (Comp2 h f g) x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc (suc n25))))))
      (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))))
      x' rc'
  f1DispMissV3 hCode (Rec z s)     x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc (suc (suc n25)))))))
      (ap2 Pair (reify (code z)) (reify (codeF2 s))) x' rc'
  f1DispMissV3 hCode (KT t)        x' rc' =
    ndDispatchV3PairMiss hCode O (reify (natCode (suc (suc (suc (suc (suc (suc n25))))))))
      (reify (code t)) x' rc'

------------------------------------------------------------------------
-- Navigate to case20 (needed for cong1).

private
  ndDisp20V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n20)) d) r)
                   (ap2 case20 (ap2 Pair (reify (natCode n20)) d) r))
  ndDisp20V3 hCode d r =
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
-- Case 20: ruleCong1 f.  One sub-proof.
--
-- Encoding: nd (natCode n20) (nd (codeF1 f) (nd pa pb)).

thm14EV3Cong1 : {H : Equation} {t u : Term} (f : Fun1) ->
                ProofE3 H (eqn t u) -> ProofE3 H (eqn (ap1 f t) (ap1 f u))
thm14EV3Cong1 {H} {t} {u} f pe =
  mkProofE3 (natCode n20) (nd (codeF1 f) (nd pa1 pb1)) correct
    (\x' r' -> passthroughSucV3 hCode n19 (nd (codeF1 f) (nd pa1 pb1)) x' r')
  where
  pa1 : Tree ; pa1 = pa pe
  pb1 : Tree ; pb1 = pb pe
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  uC    : Term ; uC    = reify (code u)
  fC    : Term ; fC    = reify (codeF1 f)
  spR   : Term ; spR   = ap2 Pair (reify pa1) (reify pb1)
  tagR  : Term ; tagR  = reify (natCode n20)
  dat   : Term ; dat   = ap2 Pair fC spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) fC) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) fC) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode fC spR (reify pa1) (reify pb1)
                (\x' rc' -> f1DispMissV3 hCode f x' rc'))
              (congR Pair (ap1 (thmT hCode) fC) (corr pe))

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
      (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
                (ap2 Pair (reify tagAp1) (ap2 Pair fC uC))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR fC spR recs')
    (ruleTrans (ndDisp20V3 hCode dat recs')
    (mkEqFRed (mkAp1F origA recsBL) (mkAp1F origA recsBR) enc recs'
      (ap2 Pair (reify tagAp1) (ap2 Pair fC tC))
      (ap2 Pair (reify tagAp1) (ap2 Pair fC uC))
      (mkAp1FRed origA recsBL enc recs' fC tC
        (origARed tagR fC spR recs')
        (recsBLRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) fC) tC uC))
      (mkAp1FRed origA recsBR enc recs' fC uC
        (origARed tagR fC spR recs')
        (recsBRRed enc (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) fC) tC uC))))))

------------------------------------------------------------------------
-- Case 2: axSnd a b.  Mirror of axFst.

thm14EV3AxSnd : (H : Equation) (a b : Term) ->
                ProofE3 H (eqn (ap1 Snd (ap2 Pair a b)) b)
thm14EV3AxSnd H a b = mkProofE3 (natCode n2) (nd (code a) (code b)) correct
  (\x' r' -> passthroughSucV3 hCode n1 (nd (code a) (code b)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n2)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  codeSndF : Term ; codeSndF = reify (codeF1 Snd)
  pairCF   : Term ; pairCF   = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 Snd (ap2 Pair a b)) b))))
  correct =
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

------------------------------------------------------------------------
-- Case 3: axConst a b.

thm14EV3AxConst : (H : Equation) (a b : Term) ->
                  ProofE3 H (eqn (ap2 Const a b) a)
thm14EV3AxConst H a b = mkProofE3 (natCode n3) (nd (code a) (code b)) correct
  (\x' r' -> passthroughSucV3 hCode n2 (nd (code a) (code b)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n3)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  constCF : Term ; constCF = reify (codeF2 Const)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 Const a b) a))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR aC bC recs)
    (ruleTrans (ndBranchMiss n3 n0 case0 (ndT1V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n3 n1 case1 (ndT2V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n3 n2 case2 (ndT3V3 hCode) body recs refl)
    (ruleTrans (ndBranchHit n3 case3 (ndT4V3 hCode) body recs)
    (mkEqFRed (mkAp2F (kF2 constCF) origA origB) origA enc recs
      (ap2 Pair (reify tagAp2) (ap2 Pair constCF (ap2 Pair aC bC)))
      aC
      (mkAp2FRed (kF2 constCF) origA origB enc recs constCF aC bC
        (kF2Red constCF enc recs)
        (origARed tagR aC bC recs)
        (origBRed tagR aC bC recs))
      (origARed tagR aC bC recs)))))))

------------------------------------------------------------------------
-- Navigate ndDispatchV3 hCode to case26 (the hypothesis case).

private
  ndDisp26V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n26)) d) r)
                   (ap2 (case26 hCode) (ap2 Pair (reify (natCode n26)) d) r))
  ndDisp26V3 hCode d r =
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
-- Case 26: ruleHyp.  The semantic heart of the redesign.
--
-- Encoding: encHyp (codeEqn H) = nd (natCode n26) (codeEqn H).
-- At Term:  reify encHyp = Pair (reify(natCode n26)) (reify(codeEqn H)) = Pair tagR hCode.
-- Conclusion: H = eqn l r, so codeEqn H = hCode, i.e., the encoding's
-- thmT-value IS the hypothesis code itself.

thm14EV3Hyp : (H : Equation) -> ProofE3 H H
thm14EV3Hyp (eqn l r) = mkProofE3 (natCode n26) (codeEqn (eqn l r)) correct passF
  where
  lC    : Term ; lC    = reify (code l)
  rC    : Term ; rC    = reify (code r)
  hCode : Term ; hCode = ap2 Pair lC rC      -- = reify (codeEqn (eqn l r))
  tagR  : Term ; tagR  = reify (natCode n26)
  enc   : Term ; enc   = ap2 Pair tagR hCode
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) hCode)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc) (reify (codeEqn (eqn l r))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR hCode)
    (ruleTrans (guardNdV3 hCode tagR lC rC recs)
    (ruleTrans (ndDisp26V3 hCode hCode recs)
               (case26Match hCode tagR recs)))

  -- Passthrough: encoding's outer tag is natCode n26 = suc n25, so it
  -- has shape Pair O (reify (natCode n25)).  Matches the "natCode (suc n)"
  -- passthrough pattern (a1 = O, a2 = natCode n25, b = hCode).
  passF : (x rcs : Term) -> {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair enc x) rcs)
                         (ap2 sndArg2 (ap2 Pair enc x) rcs))
  passF x rcs = ndDispatchV3PairMiss hCode O (reify (natCode n25)) hCode x rcs

------------------------------------------------------------------------
-- f2xDispMissV3: for every binary functor g and term x, ndDispatchV3 hCode
-- misses at the tag  Pair (reify (codeF2 g)) (reify (code x))  — the
-- "functor-and-argument" shape used by congL/congR.
--
-- Case-split on Fun2 constructors.  Each case is a direct ndDispatchV3PairMiss.

private
  f2xDispMissV3 : (hCode : Term) (g : Fun2) (x : Term) (x' rc' : Term) ->
                  {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x))) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF2 g)) (reify (code x))) x') rc'))
  f2xDispMissV3 hCode Pair         x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc n25))) O (reify (code x)) x' rc'
  f2xDispMissV3 hCode Const        x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc n25)))) O (reify (code x)) x' rc'
  f2xDispMissV3 hCode (Lift f)     x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc n25))))) (reify (codeF1 f))
      (reify (code x)) x' rc'
  f2xDispMissV3 hCode (Post f h)   x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc n25))))))
      (ap2 Pair (reify (codeF1 f)) (reify (codeF2 h)))
      (reify (code x)) x' rc'
  f2xDispMissV3 hCode (Fan h1 h2 h) x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc n25)))))))
      (ap2 Pair (reify (codeF2 h1)) (ap2 Pair (reify (codeF2 h2)) (reify (codeF2 h))))
      (reify (code x)) x' rc'
  f2xDispMissV3 hCode IfLf         x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc n25))))))))
      O (reify (code x)) x' rc'
  f2xDispMissV3 hCode TreeEq       x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc (suc n25)))))))))
      O (reify (code x)) x' rc'
  f2xDispMissV3 hCode (RecP s)     x x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc n25))))))))))
      (reify (codeF2 s)) (reify (code x)) x' rc'

------------------------------------------------------------------------
-- Navigate to case21 and case22 (for congL and congR).

private
  missNgen : (k : Nat) (hCode d r : Term) -> {hyp : Equation} ->
    (n : Nat) -> (c : Fun2) -> (t : Fun2) -> Eq (natEq k n) false ->
    Deriv hyp (eqn (ap2 (branch (tagCheck n) c t) (ap2 Pair (reify (natCode k)) d) r)
                   (ap2 t (ap2 Pair (reify (natCode k)) d) r))
  missNgen k hCode d r n c t neq = ndBranchMiss k n c t d r neq

  ndDisp21V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n21)) d) r)
                   (ap2 case21 (ap2 Pair (reify (natCode n21)) d) r))
  ndDisp21V3 hCode d r =
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

  ndDisp22V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n22)) d) r)
                   (ap2 case22 (ap2 Pair (reify (natCode n22)) d) r))
  ndDisp22V3 hCode d r =
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
-- Case 21: ruleCongL g x.  One sub-proof.
--
-- Encoding: nd (natCode n21) (nd (nd (codeF2 g) (code x)) (nd pa pb))

thm14EV3CongL : {H : Equation} {t u : Term} (g : Fun2) (x : Term) ->
                ProofE3 H (eqn t u) -> ProofE3 H (eqn (ap2 g t x) (ap2 g u x))
thm14EV3CongL {H} {t} {u} g x pe =
  mkProofE3 (natCode n21) (nd (nd (codeF2 g) (code x)) (nd pa1 pb1)) correct
    (\x' r' -> passthroughSucV3 hCode n20
                 (nd (nd (codeF2 g) (code x)) (nd pa1 pb1)) x' r')
  where
  pa1 : Tree ; pa1 = pa pe
  pb1 : Tree ; pb1 = pb pe
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  uC    : Term ; uC    = reify (code u)
  gC    : Term ; gC    = reify (codeF2 g)
  xC    : Term ; xC    = reify (code x)
  spR   : Term ; spR   = ap2 Pair (reify pa1) (reify pb1)
  aR    : Term ; aR    = ap2 Pair gC xC
  tagR  : Term ; tagR  = reify (natCode n21)
  dat   : Term ; dat   = ap2 Pair aR spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode aR spR (reify pa1) (reify pb1)
                (\x' rc' -> f2xDispMissV3 hCode g x x' rc'))
              (congR Pair (ap1 (thmT hCode) aR) (corr pe))

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
      (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair tC xC)))
                (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair uC xC)))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR aR spR recs')
    (ruleTrans (ndDisp21V3 hCode dat recs')
    (mkEqFRed (mkAp2F origAL recsBL origAR) (mkAp2F origAL recsBR origAR) enc recs'
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

------------------------------------------------------------------------
-- Case 22: ruleCongR g x.  Mirror of congL with t/u on the right.

thm14EV3CongR : {H : Equation} {t u : Term} (g : Fun2) (x : Term) ->
                ProofE3 H (eqn t u) -> ProofE3 H (eqn (ap2 g x t) (ap2 g x u))
thm14EV3CongR {H} {t} {u} g x pe =
  mkProofE3 (natCode n22) (nd (nd (codeF2 g) (code x)) (nd pa1 pb1)) correct
    (\x' r' -> passthroughSucV3 hCode n21
                 (nd (nd (codeF2 g) (code x)) (nd pa1 pb1)) x' r')
  where
  pa1 : Tree ; pa1 = pa pe
  pb1 : Tree ; pb1 = pb pe
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  uC    : Term ; uC    = reify (code u)
  gC    : Term ; gC    = reify (codeF2 g)
  xC    : Term ; xC    = reify (code x)
  spR   : Term ; spR   = ap2 Pair (reify pa1) (reify pb1)
  aR    : Term ; aR    = ap2 Pair gC xC
  tagR  : Term ; tagR  = reify (natCode n22)
  dat   : Term ; dat   = ap2 Pair aR spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair tC uC)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode aR spR (reify pa1) (reify pb1)
                (\x' rc' -> f2xDispMissV3 hCode g x x' rc'))
              (congR Pair (ap1 (thmT hCode) aR) (corr pe))

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
      (ap2 Pair (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC tC)))
                (ap2 Pair (reify tagAp2) (ap2 Pair gC (ap2 Pair xC uC)))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR aR spR recs')
    (ruleTrans (ndDisp22V3 hCode dat recs')
    (mkEqFRed (mkAp2F origAL origAR recsBL) (mkAp2F origAL origAR recsBR) enc recs'
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

------------------------------------------------------------------------
-- Case 11: axIfLfL a b.

thm14EV3AxIfLfL : (H : Equation) (a b : Term) ->
                  ProofE3 H (eqn (ap2 IfLf O (ap2 Pair a b)) a)
thm14EV3AxIfLfL H a b = mkProofE3 (natCode n11) (nd (code a) (code b)) correct
  (\x' r' -> passthroughSucV3 hCode n10 (nd (code a) (code b)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n11)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  oCC    : Term ; oCC    = ap2 Pair O O

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 IfLf O (ap2 Pair a b)) a))))
  correct =
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
    (mkEqFRed (mkAp2F (kF2 iflfCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB))
              origA enc recs
      (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair oCC
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))))
      aC
      (mkAp2FRed (kF2 iflfCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB)
        enc recs iflfCF oCC
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red iflfCF enc recs)
        (kF2Red oCC enc recs)
        (mkAp2FRed (kF2 pairCF) origA origB enc recs pairCF aC bC
          (kF2Red pairCF enc recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (origARed tagR aC bC recs)))))))))))))))

------------------------------------------------------------------------
-- Case 12: axIfLfN x y a b.

thm14EV3AxIfLfN : (H : Equation) (x y a b : Term) ->
                  ProofE3 H (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b)
thm14EV3AxIfLfN H x y a b = mkProofE3 (natCode n12)
    (nd (code x) (nd (code y) (nd (code a) (code b)))) correct
  (\x' r' -> passthroughSucV3 hCode n11
               (nd (code x) (nd (code y) (nd (code a) (code b)))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  xC    : Term ; xC    = reify (code x)
  yC    : Term ; yC    = reify (code y)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n12)
  body  : Term ; body  = ap2 Pair xC (ap2 Pair yC (ap2 Pair aC bC))
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  iflfCF : Term ; iflfCF = reify (codeF2 IfLf)
  pairCF : Term ; pairCF = reify (codeF2 Pair)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a b)) b))))
  correct =
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
      (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                            (mkAp2F (kF2 pairCF) origB2a origB2b))
      origB2b enc recs
      (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair xC yC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))))))
      bC
      (mkAp2FRed (kF2 iflfCF) (mkAp2F (kF2 pairCF) origA origB1)
                               (mkAp2F (kF2 pairCF) origB2a origB2b) enc recs
        iflfCF
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair xC yC)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red iflfCF enc recs)
        (mkAp2FRed (kF2 pairCF) origA origB1 enc recs pairCF xC yC
          (kF2Red pairCF enc recs)
          (origARed tagR xC (ap2 Pair yC (ap2 Pair aC bC)) recs)
          (origB1Red tagR xC yC (ap2 Pair aC bC) recs))
        (mkAp2FRed (kF2 pairCF) origB2a origB2b enc recs pairCF aC bC
          (kF2Red pairCF enc recs)
          (origB2aRed tagR xC yC aC bC recs)
          (origB2bRed tagR xC yC aC bC recs)))
      (origB2bRed tagR xC yC aC bC recs))))))))))))))))

------------------------------------------------------------------------
-- Case 13: axTreeEqLL.  Body is O (lf).  Uses guardLfV3 + lfDispatchV3.

thm14EV3AxTreeEqLL : (H : Equation) -> ProofE3 H (eqn (ap2 TreeEq O O) O)
thm14EV3AxTreeEqLL H = mkProofE3 (natCode n13) lf correct
  (\x' r' -> passthroughSucV3 hCode n12 lf x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  tagR  : Term ; tagR  = reify (natCode n13)
  enc   : Term ; enc   = ap2 Pair tagR O
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) O)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  oCC   : Term ; oCC = ap2 Pair O O

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 TreeEq O O) O))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR O)
    (ruleTrans (guardLfV3 hCode tagR recs)
    (ruleTrans (ndBranchHit n13 case13 (kF2 O) O recs)
    (mkEqFRed (mkAp2F (kF2 treeeqCF) (kF2 oCC) (kF2 oCC)) (kF2 oCC) enc recs
      (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair oCC oCC)))
      oCC
      (mkAp2FRed (kF2 treeeqCF) (kF2 oCC) (kF2 oCC) enc recs treeeqCF oCC oCC
        (kF2Red treeeqCF enc recs)
        (kF2Red oCC enc recs)
        (kF2Red oCC enc recs))
      (kF2Red oCC enc recs))))

------------------------------------------------------------------------
-- Case 14: axTreeEqLN a b.

thm14EV3AxTreeEqLN : (H : Equation) (a b : Term) ->
  ProofE3 H (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O))
thm14EV3AxTreeEqLN H a b = mkProofE3 (natCode n14) (nd (code a) (code b)) correct
  (\x' r' -> passthroughSucV3 hCode n13 (nd (code a) (code b)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n14)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  treeeqCF    : Term ; treeeqCF    = reify (codeF2 TreeEq)
  pairCF      : Term ; pairCF      = reify (codeF2 Pair)
  oCC         : Term ; oCC         = ap2 Pair O O
  reifyTagAp2 : Term ; reifyTagAp2 = reify tagAp2
  oneC        : Term
  oneC        = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oCC oCC))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 TreeEq O (ap2 Pair a b)) (ap2 Pair O O)))))
  correct =
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
    (mkEqFRed (mkAp2F (kF2 treeeqCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB))
              (kF2 oneC) enc recs
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCF (ap2 Pair oCC
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC))))))
      oneC
      (mkAp2FRed (kF2 treeeqCF) (kF2 oCC) (mkAp2F (kF2 pairCF) origA origB)
        enc recs treeeqCF oCC
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC)))
        (kF2Red treeeqCF enc recs)
        (kF2Red oCC enc recs)
        (mkAp2FRed (kF2 pairCF) origA origB enc recs pairCF aC bC
          (kF2Red pairCF enc recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs)))
      (kF2Red oneC enc recs))))))))))))))))))

------------------------------------------------------------------------
-- Case 15: axTreeEqNL a b.

thm14EV3AxTreeEqNL : (H : Equation) (a b : Term) ->
  ProofE3 H (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O))
thm14EV3AxTreeEqNL H a b = mkProofE3 (natCode n15) (nd (code a) (code b)) correct
  (\x' r' -> passthroughSucV3 hCode n14 (nd (code a) (code b)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n15)
  body  : Term ; body  = ap2 Pair aC bC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  treeeqCF    : Term ; treeeqCF    = reify (codeF2 TreeEq)
  pairCF      : Term ; pairCF      = reify (codeF2 Pair)
  oCC         : Term ; oCC         = ap2 Pair O O
  reifyTagAp2 : Term ; reifyTagAp2 = reify tagAp2
  oneC        : Term
  oneC        = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oCC oCC))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 TreeEq (ap2 Pair a b) O) (ap2 Pair O O)))))
  correct =
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
    (mkEqFRed (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oCC))
              (kF2 oneC) enc recs
      (ap2 Pair reifyTagAp2 (ap2 Pair treeeqCF (ap2 Pair
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC)))
        oCC)))
      oneC
      (mkAp2FRed (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB) (kF2 oCC)
        enc recs treeeqCF
        (ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair aC bC)))
        oCC
        (kF2Red treeeqCF enc recs)
        (mkAp2FRed (kF2 pairCF) origA origB enc recs pairCF aC bC
          (kF2Red pairCF enc recs)
          (origARed tagR aC bC recs)
          (origBRed tagR aC bC recs))
        (kF2Red oCC enc recs))
      (kF2Red oneC enc recs)))))))))))))))))))

------------------------------------------------------------------------
-- Case 25: axKT t x.

thm14EV3AxKT : (H : Equation) (t x : Term) ->
               ProofE3 H (eqn (ap1 (KT t) x) t)
thm14EV3AxKT H t x = mkProofE3 (natCode n25) (nd (code t) (code x)) correct
  (\x' r' -> passthroughSucV3 hCode n24 (nd (code t) (code x)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  tC    : Term ; tC    = reify (code t)
  xC    : Term ; xC    = reify (code x)
  tagR  : Term ; tagR  = reify (natCode n25)
  body  : Term ; body  = ap2 Pair tC xC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  codeKTTag : Term
  codeKTTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 (KT t) x) t))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR tC xC recs)
    (ruleTrans (ndBranchMiss n25 n0  case0  (ndT1V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n1  case1  (ndT2V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n2  case2  (ndT3V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n3  case3  (ndT4V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n4  case4  (ndT5V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n5  case5  (ndT6V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n6  case6  (ndT7V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n7  case7  (ndT8V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n8  case8  (ndT9V3  hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n9  case9  (ndT10V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n10 case10 (ndT11V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n11 case11 (ndT12V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n12 case12 (ndT13V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n13 case13 (ndT14V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n14 case14 (ndT15V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n15 case15 (ndT16V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n16 case16 (ndT17V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n17 case17 (ndT18V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n18 case18 (ndT19V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n19 case19V3 (ndT20V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n20 case20 (ndT21V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n21 case21 (ndT22V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n22 case22 (ndT23V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n23 case23V3 (ndT24V3 hCode) body recs refl)
    (ruleTrans (ndBranchMiss n25 n24 case24 (ndT25V3 hCode) body recs refl)
    (ruleTrans (ndBranchHit n25 case25 (ndT26V3 hCode) body recs)
    (mkEqFRed (mkAp1F (Fan (kF2 codeKTTag) origA Pair) origB) origA enc recs
      (ap2 Pair (reify tagAp1) (ap2 Pair (ap2 Pair codeKTTag tC) xC))
      tC
      (mkAp1FRed (Fan (kF2 codeKTTag) origA Pair) origB enc recs
        (ap2 Pair codeKTTag tC) xC
        (ruleTrans (fanRed (kF2 codeKTTag) origA Pair enc recs)
        (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red codeKTTag enc recs))
                   (congR Pair codeKTTag (origARed tagR tC xC recs))))
        (origBRed tagR tC xC recs))
      (origARed tagR tC xC recs)))))))))))))))))))))))))))))

------------------------------------------------------------------------
-- Case 6: axLift f a b.

thm14EV3AxLift : (H : Equation) (f : Fun1) (a b : Term) ->
                 ProofE3 H (eqn (ap2 (Lift f) a b) (ap1 f a))
thm14EV3AxLift H f a b = mkProofE3 (natCode n6) (nd (codeF1 f) (nd (code a) (code b))) correct
  (\x' r' -> passthroughSucV3 hCode n5 (nd (codeF1 f) (nd (code a) (code b))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  fC    : Term ; fC    = reify (codeF1 f)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n6)
  body  : Term ; body  = ap2 Pair fC (ap2 Pair aC bC)
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  liftCTag : Term
  liftCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 (Lift f) a b) (ap1 f a)))))
  correct =
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

------------------------------------------------------------------------
-- Case 7: axPost f h a b.

thm14EV3AxPost : (H : Equation) (f : Fun1) (h : Fun2) (a b : Term) ->
                 ProofE3 H (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b)))
thm14EV3AxPost H f h a b = mkProofE3 (natCode n7)
    (nd (codeF1 f) (nd (codeF2 h) (nd (code a) (code b)))) correct
  (\x' r' -> passthroughSucV3 hCode n6
               (nd (codeF1 f) (nd (codeF2 h) (nd (code a) (code b)))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  fC    : Term ; fC    = reify (codeF1 f)
  hhC   : Term ; hhC   = reify (codeF2 h)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n7)
  body  : Term ; body  = ap2 Pair fC (ap2 Pair hhC (ap2 Pair aC bC))
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  postCTag : Term
  postCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 (Post f h) a b) (ap1 f (ap2 h a b))))))
  correct =
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

------------------------------------------------------------------------
-- Case 4: axComp f g t.

thm14EV3AxComp : (H : Equation) (f g : Fun1) (t : Term) ->
                 ProofE3 H (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))
thm14EV3AxComp H f g t = mkProofE3 (natCode n4) (nd (codeF1 f) (nd (codeF1 g) (code t))) correct
  (\x' r' -> passthroughSucV3 hCode n3 (nd (codeF1 f) (nd (codeF1 g) (code t))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  fC    : Term ; fC    = reify (codeF1 f)
  gC    : Term ; gC    = reify (codeF1 g)
  tC    : Term ; tC    = reify (code t)
  tagR  : Term ; tagR  = reify (natCode n4)
  body  : Term ; body  = ap2 Pair fC (ap2 Pair gC tC)
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  compCTag : Term
  compCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t))))))
  correct =
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

------------------------------------------------------------------------
-- Case 9: axRecLf z s.

thm14EV3AxRecLf : (H : Equation) (z : Term) (s : Fun2) ->
                  ProofE3 H (eqn (ap1 (Rec z s) O) z)
thm14EV3AxRecLf H z s = mkProofE3 (natCode n9) (nd (code z) (codeF2 s)) correct
  (\x' r' -> passthroughSucV3 hCode n8 (nd (code z) (codeF2 s)) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  zC    : Term ; zC    = reify (code z)
  sC    : Term ; sC    = reify (codeF2 s)
  tagR  : Term ; tagR  = reify (natCode n9)
  body  : Term ; body  = ap2 Pair zC sC
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  oCC   : Term ; oCC   = ap2 Pair O O
  recTagC : Term
  recTagC = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 (Rec z s) O) z))))
  correct =
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

------------------------------------------------------------------------
-- Case 10: axRecNd z s a b.

thm14EV3AxRecNd : (H : Equation) (z : Term) (s : Fun2) (a b : Term) ->
  ProofE3 H (eqn (ap1 (Rec z s) (ap2 Pair a b))
                 (ap2 s (ap2 Pair a b) (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b))))
thm14EV3AxRecNd H z s a b = mkProofE3 (natCode n10)
    (nd (code z) (nd (codeF2 s) (nd (code a) (code b)))) correct
  (\x' r' -> passthroughSucV3 hCode n9
               (nd (code z) (nd (codeF2 s) (nd (code a) (code b)))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  zC    : Term ; zC    = reify (code z)
  sC    : Term ; sC    = reify (codeF2 s)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n10)
  body  : Term ; body  = ap2 Pair zC (ap2 Pair sC (ap2 Pair aC bC))
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  oCC : Term ; oCC = ap2 Pair O O
  pairCF : Term ; pairCF = reify (codeF2 Pair)
  recTagC : Term
  recTagC = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))))
  recF : Fun2 ; recF = Fan (kF2 recTagC) (Fan origA origB1 Pair) Pair
  pairAB : Fun2 ; pairAB = mkAp2F (kF2 pairCF) origB2a origB2b

  recFVal : Term ; recFVal = ap2 Pair recTagC (ap2 Pair zC sC)
  pairABVal : Term
  pairABVal = ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair aC bC))

  recFPf : {hyp : Equation} -> Deriv hyp (eqn (ap2 recF enc recs) recFVal)
  recFPf =
    ruleTrans (fanRed (kF2 recTagC) (Fan origA origB1 Pair) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (Fan origA origB1 Pair) enc recs) (kF2Red recTagC enc recs))
    (congR Pair recTagC
      (ruleTrans (fanRed origA origB1 Pair enc recs)
      (ruleTrans (congL Pair (ap2 origB1 enc recs)
                   (origARed tagR zC (ap2 Pair sC (ap2 Pair aC bC)) recs))
                 (congR Pair zC (origB1Red tagR zC sC (ap2 Pair aC bC) recs))))))

  pairABPf : {hyp : Equation} -> Deriv hyp (eqn (ap2 pairAB enc recs) pairABVal)
  pairABPf =
    mkAp2FRed (kF2 pairCF) origB2a origB2b enc recs pairCF aC bC
      (kF2Red pairCF enc recs)
      (origB2aRed tagR zC sC aC bC recs)
      (origB2bRed tagR zC sC aC bC recs)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 (Rec z s) (ap2 Pair a b))
                     (ap2 s (ap2 Pair a b) (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b)))))))
  correct =
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
              (mkAp2F origB1 pairAB (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b)))
      enc recs
      (ap2 Pair (reify tagAp1) (ap2 Pair recFVal pairABVal))
      (ap2 Pair (reify tagAp2) (ap2 Pair sC (ap2 Pair pairABVal
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC))))))))
      (mkAp1FRed recF pairAB enc recs recFVal pairABVal recFPf pairABPf)
      (mkAp2FRed origB1 pairAB
        (mkAp2F (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b))
        enc recs sC pairABVal
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC)))))
        (origB1Red tagR zC sC (ap2 Pair aC bC) recs)
        pairABPf
        (mkAp2FRed (kF2 pairCF) (mkAp1F recF origB2a) (mkAp1F recF origB2b) enc recs
          pairCF
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal aC))
          (ap2 Pair (reify tagAp1) (ap2 Pair recFVal bC))
          (kF2Red pairCF enc recs)
          (mkAp1FRed recF origB2a enc recs recFVal aC recFPf
            (origB2aRed tagR zC sC aC bC recs))
          (mkAp1FRed recF origB2b enc recs recFVal bC recFPf
            (origB2bRed tagR zC sC aC bC recs)))))))))))))))))

------------------------------------------------------------------------
-- Case 16: axTreeEqNN a1 a2 b1 b2.

thm14EV3AxTreeEqNN : (H : Equation) (a1 a2 b1 b2 : Term) ->
  ProofE3 H (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                 (ap2 IfLf (ap2 TreeEq a1 b1)
                           (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O))))
thm14EV3AxTreeEqNN H a1 a2 b1 b2 = mkProofE3 (natCode n16)
    (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))) correct
  (\x' r' -> passthroughSucV3 hCode n15
               (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  a1C   : Term ; a1C   = reify (code a1)
  a2C   : Term ; a2C   = reify (code a2)
  b1C   : Term ; b1C   = reify (code b1)
  b2C   : Term ; b2C   = reify (code b2)
  tagR  : Term ; tagR  = reify (natCode n16)
  body  : Term ; body  = ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C))
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  treeeqCF : Term ; treeeqCF = reify (codeF2 TreeEq)
  pairCF   : Term ; pairCF   = reify (codeF2 Pair)
  iflfCF   : Term ; iflfCF   = reify (codeF2 IfLf)
  oCC      : Term ; oCC      = ap2 Pair O O
  reifyTagAp2 : Term
  reifyTagAp2 = ap2 Pair O (ap2 Pair O (ap2 Pair O O))
  oneCF       : Term
  oneCF       = ap2 Pair reifyTagAp2 (ap2 Pair pairCF (ap2 Pair oCC oCC))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                     (ap2 IfLf (ap2 TreeEq a1 b1)
                               (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O)))))))
  correct =
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
      (mkAp2F (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                              (mkAp2F (kF2 pairCF) origB2a origB2b))
      (mkAp2F (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                            (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b)
                                                  (kF2 oneCF)))
      enc recs
      (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair a1C a2C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair b1C b2C))))))
      (ap2 Pair (reify tagAp2) (ap2 Pair iflfCF (ap2 Pair
        (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a1C b1C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C))) oneCF))))))
      (mkAp2FRed (kF2 treeeqCF) (mkAp2F (kF2 pairCF) origA origB1)
                                 (mkAp2F (kF2 pairCF) origB2a origB2b) enc recs
        treeeqCF
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair a1C a2C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair b1C b2C)))
        (kF2Red treeeqCF enc recs)
        (mkAp2FRed (kF2 pairCF) origA origB1 enc recs pairCF a1C a2C
          (kF2Red pairCF enc recs)
          (origARed tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
          (origB1Red tagR a1C a2C (ap2 Pair b1C b2C) recs))
        (mkAp2FRed (kF2 pairCF) origB2a origB2b enc recs pairCF b1C b2C
          (kF2Red pairCF enc recs)
          (origB2aRed tagR a1C a2C b1C b2C recs)
          (origB2bRed tagR a1C a2C b1C b2C recs)))
      (mkAp2FRed (kF2 iflfCF) (mkAp2F (kF2 treeeqCF) origA origB2a)
                               (mkAp2F (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b)
                                                     (kF2 oneCF))
        enc recs iflfCF
        (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a1C b1C)))
        (ap2 Pair (reify tagAp2) (ap2 Pair pairCF (ap2 Pair
          (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C))) oneCF)))
        (kF2Red iflfCF enc recs)
        (mkAp2FRed (kF2 treeeqCF) origA origB2a enc recs treeeqCF a1C b1C
          (kF2Red treeeqCF enc recs)
          (origARed tagR a1C (ap2 Pair a2C (ap2 Pair b1C b2C)) recs)
          (origB2aRed tagR a1C a2C b1C b2C recs))
        (mkAp2FRed (kF2 pairCF) (mkAp2F (kF2 treeeqCF) origB1 origB2b) (kF2 oneCF)
          enc recs pairCF
          (ap2 Pair (reify tagAp2) (ap2 Pair treeeqCF (ap2 Pair a2C b2C)))
          oneCF
          (kF2Red pairCF enc recs)
          (mkAp2FRed (kF2 treeeqCF) origB1 origB2b enc recs treeeqCF a2C b2C
            (kF2Red treeeqCF enc recs)
            (origB1Red tagR a1C a2C (ap2 Pair b1C b2C) recs)
            (origB2bRed tagR a1C a2C b1C b2C recs))
          (kF2Red oneCF enc recs))))))))))))))))))))))

------------------------------------------------------------------------
-- f1gDispMissV3: dispatch-miss for tag  Pair (codeF1 f) (codeF1 g) .
-- Case-split on f; analogue of V2's f1gDispMiss.

private
  f1gDispMissV3 : (hCode : Term) (f g : Fun1) (x' rc' : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                     (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x') rc')
                   (ap2 sndArg2
                     (ap2 Pair (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g))) x') rc'))
  f1gDispMissV3 hCode I             g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc n25))) O (reify (codeF1 g')) x' rc'
  f1gDispMissV3 hCode Fst           g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc n25)))) O (reify (codeF1 g')) x' rc'
  f1gDispMissV3 hCode Snd           g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc n25))))) O (reify (codeF1 g')) x' rc'
  f1gDispMissV3 hCode (Comp f1 f2)  g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc n25))))))
      (ap2 Pair (reify (codeF1 f1)) (reify (codeF1 f2))) (reify (codeF1 g')) x' rc'
  f1gDispMissV3 hCode (Comp2 h f1 f2) g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc n25)))))))
      (ap2 Pair (reify (codeF2 h)) (ap2 Pair (reify (codeF1 f1)) (reify (codeF1 f2))))
      (reify (codeF1 g')) x' rc'
  f1gDispMissV3 hCode (Rec z' s')   g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc n25))))))))
      (ap2 Pair (reify (code z')) (reify (codeF2 s'))) (reify (codeF1 g')) x' rc'
  f1gDispMissV3 hCode (KT t)        g' x' rc' =
    ndDispatchV3PairMiss hCode (reify (natCode (suc (suc (suc (suc (suc (suc (suc n25)))))))))
      (reify (code t)) (reify (codeF1 g')) x' rc'

------------------------------------------------------------------------
-- ndDisp24V3: navigate to case24.

private
  ndDisp24V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n24)) d) r)
                   (ap2 case24 (ap2 Pair (reify (natCode n24)) d) r))
  ndDisp24V3 hCode d r =
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
-- Case 24: ruleF f g z s bf sf bg sg.  Four sub-proofs.
--
-- Encoding: nd (natCode n24) (nd (nd (codeF1 f) (codeF1 g))
--              (nd bChild1 bChild2))
-- where bChild1 = nd (code z) (codeF2 s) and
--       bChild2 = nd (nd (nd pa1 pb1) (nd pa2 pb2)) (nd (nd pa3 pb3) (nd pa4 pb4)).
--
-- case24 does NOT use the sub-proofs' content — it only extracts the
-- functor codes f and g from origAL, origAR, applying each to var0.
-- The conclusion is  ap1 f (var 0) = ap1 g (var 0) .

thm14EV3F : {H : Equation} (f g : Fun1) (z : Term) (s : Fun2) ->
  ProofE3 H (eqn (ap1 f O) z) ->
  ProofE3 H (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
                 (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                        (ap2 Pair (ap1 f (var zero)) (ap1 f (var (suc zero)))))) ->
  ProofE3 H (eqn (ap1 g O) z) ->
  ProofE3 H (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
                 (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                        (ap2 Pair (ap1 g (var zero)) (ap1 g (var (suc zero)))))) ->
  ProofE3 H (eqn (ap1 f (var zero)) (ap1 g (var zero)))
thm14EV3F {H} f g z s pe1 pe2 pe3 pe4 =
  mkProofE3 (natCode n24) (nd (nd (codeF1 f) (codeF1 g)) pbTree) correct
    (\x' r' -> passthroughSucV3 hCode n23 (nd (nd (codeF1 f) (codeF1 g)) pbTree) x' r')
  where
  pa1 = pa pe1 ; pb1 = pb pe1
  pa2 = pa pe2 ; pb2 = pb pe2
  pa3 = pa pe3 ; pb3 = pb pe3
  pa4 = pa pe4 ; pb4 = pb pe4
  pbTree : Tree
  pbTree = nd (nd (code z) (codeF2 s))
              (nd (nd (nd pa1 pb1) (nd pa2 pb2)) (nd (nd pa3 pb3) (nd pa4 pb4)))

  hCode : Term ; hCode = reify (codeEqn H)
  fC    : Term ; fC    = reify (codeF1 f)
  gC'   : Term ; gC'   = reify (codeF1 g)
  v0C   : Term
  v0C   = reify (nd (nd (nd (nd lf lf) lf) lf) lf)
  tagR  : Term ; tagR  = reify (natCode n24)
  aR    : Term ; aR    = ap2 Pair fC gC'
  bChild1 : Term
  bChild1 = ap2 Pair (reify (code z)) (reify (codeF2 s))
  bChild2 : Term
  bChild2 = ap2 Pair (ap2 Pair (reify (nd pa1 pb1)) (reify (nd pa2 pb2)))
                     (ap2 Pair (reify (nd pa3 pb3)) (reify (nd pa4 pb4)))
  bR    : Term ; bR    = ap2 Pair bChild1 bChild2
  dat   : Term ; dat   = ap2 Pair aR bR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap1 (thmT hCode) bR))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap1 (thmT hCode) bR)))
  datExpand =
    intermediateGenericV3 hCode aR bR bChild1 bChild2
      (\x' rc' -> f1gDispMissV3 hCode f g x' rc')

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
      (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair fC v0C))
                (ap2 Pair (reify tagAp1) (ap2 Pair gC' v0C))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR aR bR recs')
    (ruleTrans (ndDisp24V3 hCode dat recs')
    (mkEqFRed (mkAp1F origAL (kF2 v0C)) (mkAp1F origAR (kF2 v0C)) enc recs'
      (ap2 Pair (reify tagAp1) (ap2 Pair fC v0C))
      (ap2 Pair (reify tagAp1) (ap2 Pair gC' v0C))
      (mkAp1FRed origAL (kF2 v0C) enc recs' fC v0C
        (origALRed tagR fC gC' bR recs')
        (kF2Red v0C enc recs'))
      (mkAp1FRed origAR (kF2 v0C) enc recs' gC' v0C
        (origARRed tagR fC gC' bR recs')
        (kF2Red v0C enc recs'))))))

------------------------------------------------------------------------
-- Case 5: axComp2 h f g t.

thm14EV3AxComp2 : (H : Equation) (h : Fun2) (f g : Fun1) (t : Term) ->
                  ProofE3 H (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t)))
thm14EV3AxComp2 H h f g t = mkProofE3 (natCode n5)
    (nd (codeF2 h) (nd (codeF1 f) (nd (codeF1 g) (code t)))) correct
  (\x' r' -> passthroughSucV3 hCode n4
               (nd (codeF2 h) (nd (codeF1 f) (nd (codeF1 g) (code t)))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  hhC   : Term ; hhC   = reify (codeF2 h)
  fC    : Term ; fC    = reify (codeF1 f)
  gC    : Term ; gC    = reify (codeF1 g)
  tC    : Term ; tC    = reify (code t)
  tagR  : Term ; tagR  = reify (natCode n5)
  body  : Term ; body  = ap2 Pair hhC (ap2 Pair fC (ap2 Pair gC tC))
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  comp2CTag : Term
  comp2CTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap1 (Comp2 h f g) t) (ap2 h (ap1 f t) (ap1 g t))))))
  correct =
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

------------------------------------------------------------------------
-- Case 8: axFan h1 h2 h a b.

thm14EV3AxFan : (H : Equation) (h1 h2 h : Fun2) (a b : Term) ->
                ProofE3 H (eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b)))
thm14EV3AxFan H h1 h2 h a b = mkProofE3 (natCode n8)
    (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h) (nd (code a) (code b))))) correct
  (\x' r' -> passthroughSucV3 hCode n7
               (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h) (nd (code a) (code b))))) x' r')
  where
  hCode : Term ; hCode = reify (codeEqn H)
  h1C   : Term ; h1C   = reify (codeF2 h1)
  h2C   : Term ; h2C   = reify (codeF2 h2)
  hhC   : Term ; hhC   = reify (codeF2 h)
  aC    : Term ; aC    = reify (code a)
  bC    : Term ; bC    = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n8)
  body  : Term ; body  = ap2 Pair h1C (ap2 Pair h2C (ap2 Pair hhC (ap2 Pair aC bC)))
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)
  fanCTag : Term
  fanCTag = reify (natCode (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))))
  ob2b1F : Fun2 ; ob2b1F = Post Fst origB2b
  ob2b2F : Fun2 ; ob2b2F = Post Snd origB2b

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 (Fan h1 h2 h) a b) (ap2 h (ap2 h1 a b) (ap2 h2 a b))))))
  correct =
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

------------------------------------------------------------------------
-- ndDisp23V3: navigate from the start of ndDispatchV3 to case23V3.

private
  ndDisp23V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n23)) d) r)
                   (ap2 case23V3 (ap2 Pair (reify (natCode n23)) d) r))
  ndDisp23V3 hCode d r =
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
-- aRPassV3: ndDispatchV3 passthrough at tag  aR = Pair tCt xCt  where
-- tCt = reify (code t), xCt = reify (natCode x).
--
-- Since tCt is always a Pair (every  code t  is an nd), aR has shape
-- Pair (Pair a1 a2) b with (a1, a2) = components of tCt and b = xCt.
-- So ndDispatchV3 misses at aR via ndDispatchV3PairMiss.  Case-split
-- on t to extract (a1, a2).

private
  aRPassV3 : (hCode : Term) (t : Term) (x : Nat) (x' rc' : Term) ->
             {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode)
                    (ap2 Pair (ap2 Pair (reify (code t)) (reify (natCode x))) x') rc')
                   (ap2 sndArg2
                    (ap2 Pair (ap2 Pair (reify (code t)) (reify (natCode x))) x') rc'))
  aRPassV3 hCode O         x x' rc' =
    ndDispatchV3PairMiss hCode O O (reify (natCode x)) x' rc'
  aRPassV3 hCode (var n)   x x' rc' =
    ndDispatchV3PairMiss hCode (reify tagVar) (reify (natCode n))
                               (reify (natCode x)) x' rc'
  aRPassV3 hCode (ap1 f t) x x' rc' =
    ndDispatchV3PairMiss hCode (reify tagAp1)
      (ap2 Pair (reify (codeF1 f)) (reify (code t)))
      (reify (natCode x)) x' rc'
  aRPassV3 hCode (ap2 g a b) x x' rc' =
    ndDispatchV3PairMiss hCode (reify tagAp2)
      (ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code a)) (reify (code b))))
      (reify (natCode x)) x' rc'

------------------------------------------------------------------------
-- Case 23: ruleInst x t pe.  One sub-proof.
--
-- Encoding: nd (natCode n23) (nd (nd (code t) (natCode x)) (nd pa pb))
-- where (pa, pb) come from the sub-proof's ProofE3.
--
-- Semantics at Fun2 level (case23V3Match + substOpCorrect):
--   thmT hCode  applied to the encoding reduces to
--     Pair (reify (code (subst x t l)))  (reify (code (subst x t r')))
--   = reify (codeEqn (eqn (subst x t l) (subst x t r')))
--   where (l, r') are the sides of the sub-equation witnessed by pe.

thm14EV3Inst : {H : Equation} {l r' : Term} (x : Nat) (t : Term) ->
               ProofE3 H (eqn l r') ->
               ProofE3 H (eqn (subst x t l) (subst x t r'))
thm14EV3Inst {H} {l} {r'} x t pe =
  mkProofE3 (natCode n23) (nd (nd (code t) (natCode x)) (nd pa1 pb1)) correct
    (\x' r'' -> passthroughSucV3 hCode n22
                  (nd (nd (code t) (natCode x)) (nd pa1 pb1)) x' r'')
  where
  pa1 : Tree ; pa1 = pa pe
  pb1 : Tree ; pb1 = pb pe
  hCode : Term ; hCode = reify (codeEqn H)
  tCt   : Term ; tCt   = reify (code t)
  xCt   : Term ; xCt   = reify (natCode x)
  lC    : Term ; lC    = reify (code l)
  r'C   : Term ; r'C   = reify (code r')
  aR    : Term ; aR    = ap2 Pair tCt xCt
  spR   : Term ; spR   = ap2 Pair (reify pa1) (reify pb1)
  tagR  : Term ; tagR  = reify (natCode n23)
  dat   : Term ; dat   = ap2 Pair aR spR
  enc   : Term ; enc   = ap2 Pair tagR dat
  recs' : Term
  recs' = ap2 Pair (ap1 (thmT hCode) tagR)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair lC r'C))

  datExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) dat)
                   (ap2 Pair (ap1 (thmT hCode) aR) (ap2 Pair lC r'C)))
  datExpand =
    ruleTrans (intermediateGenericV3 hCode aR spR (reify pa1) (reify pb1)
                (\x'' rc' -> aRPassV3 hCode t x x'' rc'))
              (congR Pair (ap1 (thmT hCode) aR) (corr pe))

  recsExpand : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) dat))
                   recs')
  recsExpand = congR Pair (ap1 (thmT hCode) tagR) datExpand

  -- substOpCorrect gives  substOp aR lC = reify (code (subst x t l))
  -- and similarly for r'.  Combine via congL/congR on Pair.
  substBoth : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 Pair (ap2 substOp aR lC) (ap2 substOp aR r'C))
                   (ap2 Pair (reify (code (subst x t l)))
                             (reify (code (subst x t r')))))
  substBoth =
    ruleTrans (congL Pair (ap2 substOp aR r'C) (substOpCorrect t x l))
              (congR Pair (reify (code (subst x t l))) (substOpCorrect t x r'))

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (subst x t l) (subst x t r')))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR dat)
    (ruleTrans (congR (thmTStep hCode) enc recsExpand)
    (ruleTrans (guardNdV3 hCode tagR aR spR recs')
    (ruleTrans (ndDisp23V3 hCode dat recs')
    (ruleTrans (case23V3Match tagR aR spR
                  (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) aR) lC r'C)
               substBoth))))

------------------------------------------------------------------------
-- ndDisp27V3 and ndDisp28V3: navigation to case27, case28.

private
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n33 : Nat ; n33 = suc (suc (suc (suc (suc n28))))

  tagAp2T : Term ; tagAp2T = reify tagAp2
  n26T    : Term ; n26T    = reify (natCode n26)
  n33T    : Term ; n33T    = reify (natCode n33)
  poo     : Term ; poo     = ap2 Pair O O

  ndDisp27V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n27)) d) r)
                   (ap2 case27 (ap2 Pair (reify (natCode n27)) d) r))
  ndDisp27V3 hCode d r =
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

  ndDisp28V3 : (hCode d r : Term) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair (reify (natCode n28)) d) r)
                   (ap2 case28 (ap2 Pair (reify (natCode n28)) d) r))
  ndDisp28V3 hCode d r =
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
-- Case 27: axRecPLf s p.  No sub-proofs; direct computation axiom.
--
-- Encoding:  nd (natCode n27) (nd (codeF2 s) (code p))
-- Conclusion: eqn (ap2 (RecP s) p O) O
-- codeEqn reify:
--   Pair (Pair tagAp2T (Pair (Pair n33T sCr) (Pair pCr poo))) poo

thm14EV3AxRecPLf : (H : Equation) (s : Fun2) (p : Term) ->
                   ProofE3 H (eqn (ap2 (RecP s) p O) O)
thm14EV3AxRecPLf H s p =
  mkProofE3 (natCode n27) (nd (codeF2 s) (code p)) correct passF
  where
  hCode : Term ; hCode = reify (codeEqn H)
  sCr   : Term ; sCr   = reify (codeF2 s)
  pCr   : Term ; pCr   = reify (code p)
  tagR  : Term ; tagR  = reify (natCode n27)
  body  : Term ; body  = ap2 Pair sCr pCr
  enc   : Term ; enc   = ap2 Pair tagR body
  recs  : Term
  recs  = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  passF : (x rcs : Term) -> {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair enc x) rcs)
                         (ap2 sndArg2 (ap2 Pair enc x) rcs))
  passF x rcs = passthroughSucV3 hCode n26 (nd (codeF2 s) (code p)) x rcs

  recPCodeF : Fun2
  recPCodeF = Fan (kF2 n33T) origA Pair

  recPCodeRed : {hyp : Equation} ->
                Deriv hyp (eqn (ap2 recPCodeF enc recs) (ap2 Pair n33T sCr))
  recPCodeRed =
    ruleTrans (fanRed (kF2 n33T) origA Pair enc recs)
    (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red n33T enc recs))
               (congR Pair n33T (origARed tagR sCr pCr recs)))

  lhsReify : Term
  lhsReify = ap2 Pair tagAp2T
               (ap2 Pair (ap2 Pair n33T sCr) (ap2 Pair pCr poo))

  case27Red : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 case27 enc recs) (ap2 Pair lhsReify poo))
  case27Red =
    mkEqFRed (mkAp2F recPCodeF origB (kF2 poo)) (kF2 poo) enc recs
      lhsReify poo
      (mkAp2FRed recPCodeF origB (kF2 poo) enc recs
        (ap2 Pair n33T sCr) pCr poo
        recPCodeRed
        (origBRed tagR sCr pCr recs)
        (kF2Red poo enc recs))
      (kF2Red poo enc recs)

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn (eqn (ap2 (RecP s) p O) O))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR sCr pCr recs)
    (ruleTrans (ndDisp27V3 hCode body recs)
               case27Red))

------------------------------------------------------------------------
-- Case 28: axRecPNd s p a b.  No sub-proofs; direct computation axiom.
--
-- Encoding:  nd (natCode n28) (nd (codeF2 s) (nd (code p) (nd (code a) (code b))))
-- Conclusion:
--   eqn (ap2 (RecP s) p (Pair a b))
--       (ap2 s (Pair p (Pair a b))
--              (Pair (ap2 (RecP s) p a) (ap2 (RecP s) p b)))

thm14EV3AxRecPNd : (H : Equation) (s : Fun2) (p a b : Term) ->
                   ProofE3 H (eqn (ap2 (RecP s) p (ap2 Pair a b))
                                  (ap2 s (ap2 Pair p (ap2 Pair a b))
                                         (ap2 Pair (ap2 (RecP s) p a)
                                                   (ap2 (RecP s) p b))))
thm14EV3AxRecPNd H s p a b =
  mkProofE3 (natCode n28)
            (nd (codeF2 s) (nd (code p) (nd (code a) (code b)))) correct passF
  where
  hCode : Term ; hCode = reify (codeEqn H)
  sCr   : Term ; sCr   = reify (codeF2 s)
  pCr   : Term ; pCr   = reify (code p)
  aCr   : Term ; aCr   = reify (code a)
  bCr   : Term ; bCr   = reify (code b)
  tagR  : Term ; tagR  = reify (natCode n28)
  bInner  : Term ; bInner  = ap2 Pair pCr (ap2 Pair aCr bCr)
  body    : Term ; body    = ap2 Pair sCr bInner
  enc     : Term ; enc     = ap2 Pair tagR body
  recs    : Term
  recs    = ap2 Pair (ap1 (thmT hCode) tagR) (ap1 (thmT hCode) body)

  passF : (x rcs : Term) -> {hyp : Equation} ->
          Deriv hyp (eqn (ap2 (ndDispatchV3 hCode) (ap2 Pair enc x) rcs)
                         (ap2 sndArg2 (ap2 Pair enc x) rcs))
  passF x rcs = passthroughSucV3 hCode n27
                  (nd (codeF2 s) (nd (code p) (nd (code a) (code b)))) x rcs

  -- Building blocks
  recPCodeF : Fun2
  recPCodeF = Fan (kF2 n33T) origA Pair
  pairF2F   : Fun2
  pairF2F   = Fan (kF2 n26T) (kF2 O) Pair

  -- Extractor reductions at enc
  origARedE : {hyp : Equation} ->
              Deriv hyp (eqn (ap2 origA enc recs) sCr)
  origARedE = origARed tagR sCr bInner recs

  origB1RedE : {hyp : Equation} ->
               Deriv hyp (eqn (ap2 origB1 enc recs) pCr)
  origB1RedE = origB1Red tagR sCr pCr (ap2 Pair aCr bCr) recs

  origB2aRedE : {hyp : Equation} ->
                Deriv hyp (eqn (ap2 origB2a enc recs) aCr)
  origB2aRedE = origB2aRed tagR sCr pCr aCr bCr recs

  origB2bRedE : {hyp : Equation} ->
                Deriv hyp (eqn (ap2 origB2b enc recs) bCr)
  origB2bRedE = origB2bRed tagR sCr pCr aCr bCr recs

  recPCodeRed : {hyp : Equation} ->
                Deriv hyp (eqn (ap2 recPCodeF enc recs) (ap2 Pair n33T sCr))
  recPCodeRed =
    ruleTrans (fanRed (kF2 n33T) origA Pair enc recs)
    (ruleTrans (congL Pair (ap2 origA enc recs) (kF2Red n33T enc recs))
               (congR Pair n33T origARedE))

  pairF2FRed : {hyp : Equation} ->
               Deriv hyp (eqn (ap2 pairF2F enc recs) (ap2 Pair n26T O))
  pairF2FRed =
    ruleTrans (fanRed (kF2 n26T) (kF2 O) Pair enc recs)
    (ruleTrans (congL Pair (ap2 (kF2 O) enc recs) (kF2Red n26T enc recs))
               (congR Pair n26T (kF2Red O enc recs)))

  -- Reify values we want
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

  -- Sub-Fun2 reductions
  pairABRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F pairF2F origB2a origB2b) enc recs) pairABReify)
  pairABRed =
    mkAp2FRed pairF2F origB2a origB2b enc recs
      (ap2 Pair n26T O) aCr bCr
      pairF2FRed origB2aRedE origB2bRedE

  lhsRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b))
                        enc recs) lhsReify)
  lhsRed =
    mkAp2FRed recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b) enc recs
      (ap2 Pair n33T sCr) pCr pairABReify
      recPCodeRed origB1RedE pairABRed

  xRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
                        enc recs) xReify)
  xRed =
    mkAp2FRed pairF2F origB1 (mkAp2F pairF2F origB2a origB2b) enc recs
      (ap2 Pair n26T O) pCr pairABReify
      pairF2FRed origB1RedE pairABRed

  recPaRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F recPCodeF origB1 origB2a) enc recs) recPaReify)
  recPaRed =
    mkAp2FRed recPCodeF origB1 origB2a enc recs
      (ap2 Pair n33T sCr) pCr aCr
      recPCodeRed origB1RedE origB2aRedE

  recPbRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F recPCodeF origB1 origB2b) enc recs) recPbReify)
  recPbRed =
    mkAp2FRed recPCodeF origB1 origB2b enc recs
      (ap2 Pair n33T sCr) pCr bCr
      recPCodeRed origB1RedE origB2bRedE

  yRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                                        (mkAp2F recPCodeF origB1 origB2b))
                        enc recs) yReify)
  yRed =
    mkAp2FRed pairF2F (mkAp2F recPCodeF origB1 origB2a)
                      (mkAp2F recPCodeF origB1 origB2b) enc recs
      (ap2 Pair n26T O) recPaReify recPbReify
      pairF2FRed recPaRed recPbRed

  rhsRed : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 (mkAp2F origA
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

  case28Red : {hyp : Equation} ->
    Deriv hyp (eqn (ap2 case28 enc recs) (ap2 Pair lhsReify rhsReify))
  case28Red =
    mkEqFRed (mkAp2F recPCodeF origB1 (mkAp2F pairF2F origB2a origB2b))
             (mkAp2F origA
                     (mkAp2F pairF2F origB1 (mkAp2F pairF2F origB2a origB2b))
                     (mkAp2F pairF2F (mkAp2F recPCodeF origB1 origB2a)
                                     (mkAp2F recPCodeF origB1 origB2b)))
             enc recs lhsReify rhsReify lhsRed rhsRed

  correct : {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT hCode) enc)
                   (reify (codeEqn
                     (eqn (ap2 (RecP s) p (ap2 Pair a b))
                          (ap2 s (ap2 Pair p (ap2 Pair a b))
                                 (ap2 Pair (ap2 (RecP s) p a)
                                           (ap2 (RecP s) p b)))))))
  correct =
    ruleTrans (recNdRed O (thmTStep hCode) tagR body)
    (ruleTrans (guardNdV3 hCode tagR sCr bInner recs)
    (ruleTrans (ndDisp28V3 hCode body recs)
               case28Red))

------------------------------------------------------------------------
-- Top-level thm14EV3 : Deriv H eq -> ProofE3 H eq.
--
-- The recursive dispatcher.  One arm per Deriv constructor.  All
-- computation axioms (ax*) are base cases; all rule* constructors
-- recurse on sub-derivations.

thm14EV3 : {H eq : Equation} -> Deriv H eq -> ProofE3 H eq
thm14EV3 {H} (axI t)               = thm14EV3AxI H t
thm14EV3 {H} (axFst a b)           = thm14EV3AxFst H a b
thm14EV3 {H} (axSnd a b)           = thm14EV3AxSnd H a b
thm14EV3 {H} (axConst a b)         = thm14EV3AxConst H a b
thm14EV3 {H} (axComp f g t)        = thm14EV3AxComp H f g t
thm14EV3 {H} (axComp2 h f g t)     = thm14EV3AxComp2 H h f g t
thm14EV3 {H} (axLift f a b)        = thm14EV3AxLift H f a b
thm14EV3 {H} (axPost f h a b)      = thm14EV3AxPost H f h a b
thm14EV3 {H} (axFan h1 h2 h a b)   = thm14EV3AxFan H h1 h2 h a b
thm14EV3 {H} (axKT t x)            = thm14EV3AxKT H t x
thm14EV3 {H} (axRecLf z s)         = thm14EV3AxRecLf H z s
thm14EV3 {H} (axRecNd z s a b)     = thm14EV3AxRecNd H z s a b
thm14EV3 {H} (axRecPLf s p)        = thm14EV3AxRecPLf H s p
thm14EV3 {H} (axRecPNd s p a b)    = thm14EV3AxRecPNd H s p a b
thm14EV3 {H} (axIfLfL a b)         = thm14EV3AxIfLfL H a b
thm14EV3 {H} (axIfLfN x y a b)     = thm14EV3AxIfLfN H x y a b
thm14EV3 {H} axTreeEqLL            = thm14EV3AxTreeEqLL H
thm14EV3 {H} (axTreeEqLN a b)      = thm14EV3AxTreeEqLN H a b
thm14EV3 {H} (axTreeEqNL a b)      = thm14EV3AxTreeEqNL H a b
thm14EV3 {H} (axTreeEqNN a1 a2 b1 b2) = thm14EV3AxTreeEqNN H a1 a2 b1 b2
thm14EV3 {H} (axRefl t)            = thm14EV3Refl H t
thm14EV3 {H} (ruleSym d)           = thm14EV3Sym (thm14EV3 d)
thm14EV3 {H} (ruleTrans d1 d2)     = thm14EV3Trans (thm14EV3 d1) (thm14EV3 d2)
thm14EV3 {H} (cong1 f d)           = thm14EV3Cong1 f (thm14EV3 d)
thm14EV3 {H} (congL g x d)         = thm14EV3CongL g x (thm14EV3 d)
thm14EV3 {H} (congR g x d)         = thm14EV3CongR g x (thm14EV3 d)
thm14EV3 {H} (ruleInst x t {eqn l r'} d) = thm14EV3Inst x t (thm14EV3 d)
thm14EV3 {H} ruleHyp               = thm14EV3Hyp H
thm14EV3 {H} (ruleF f g z s bf sf bg sg) =
  thm14EV3F f g z s (thm14EV3 bf) (thm14EV3 sf) (thm14EV3 bg) (thm14EV3 sg)
