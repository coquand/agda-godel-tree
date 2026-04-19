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
                   (ap2 case19 (ap2 Pair (reify (natCode n19)) d) r))
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
               (ndBranchHit n19 case19 (ndT20V3 hCode) d r)))))))))))))))))))

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
    (mkEqFRed recsAL recsBR enc recs' tC vC
      (recsALRed enc (ap1 (thmT hCode) tagR) tC uC (ap2 Pair uC vC))
      (recsBRRed enc (ap1 (thmT hCode) tagR) (ap2 Pair tC uC) uC vC)))))

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
    (ruleTrans (ndBranchMiss n20 n19 case19 (ndT20V3 hCode) d r refl)
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
    (ruleTrans (ndBranchMiss n26 n19 case19 (ndT20V3 hCode) d r refl)
    (ruleTrans (ndBranchMiss n26 n20 case20 (ndT21V3 hCode) d r refl)
    (ruleTrans (ndBranchMiss n26 n21 case21 (ndT22V3 hCode) d r refl)
    (ruleTrans (ndBranchMiss n26 n22 case22 (ndT23V3 hCode) d r refl)
    (ruleTrans (ndBranchMiss n26 n23 case23 (ndT24V3 hCode) d r refl)
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
    (ruleTrans (ndBranchMiss n21 n19 case19 (ndT20V3 hCode) d r refl)
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
    (ruleTrans (ndBranchMiss n22 n19 case19 (ndT20V3 hCode) d r refl)
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
