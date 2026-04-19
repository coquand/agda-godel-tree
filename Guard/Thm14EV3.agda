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
-- Navigate ndDispatchV3 hCode from n0 past n0..n18 to case19.
-- Private helper used only by thm14EV3Trans.

private
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
