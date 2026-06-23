{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParProof -- STEP 1 of the PR diagram-completion plan for internal
-- Church-Rosser (see HANDOFF-PR-COMPLETION-NEXT-SESSION.md /
-- project_t4_internal_cr_PR_completion_PLAN).
--
-- The parallel-reduction PROOF TREE and its QUANTIFIER-FREE verifier.
--
-- The proof-tree carrier is the 5-constructor meta shadow  CertM  (= the
-- parallel-reduction constructors  pZe / pSu / pAd / pRO / pRS  of
-- T4.ChurchRosserProto.Par) with its embedding  codeC : CertM -> Term  into
-- coded proof trees.  This is exactly the "reason internally with binary
-- trees" idiom of T4.BinTree (meta shadow + object recursor + structural
-- induction) already instantiated for this 5-constructor tree in T4.CertTree;
-- we EXTEND that green line rather than rebuild the recursor.
--
-- The object verifier is built from the already-green object PR functions
--     src , tgt , isCert : Fun1            (T4.ParEnds, course-of-values folds)
-- as the QUANTIFIER-FREE characteristic value
--
--     parProof p t u  :=  ap1 (parBody t u) p
--                      =  pi (pi (isCert p) (eqTest (src p) t)) (eqTest (tgt p) u)
--
-- ( = O  iff  p is a valid cert with  src p = t  and  tgt p = u ).  This is the
-- PR plan's verifier:  NO existential, NO  E -elimination -- a plain Term-valued
-- test.  ( parBody / eqTest machinery is reused from T4.ParIntro; we use ONLY
-- its quantifier-free parts, NOT the  E -wrapped  Par  predicate.)
--
-- DELIVERABLES (all by structural recursion on the CertM shadow -- the
-- BinTree/CertTree idiom: meta structure carries the dispatch, object content
-- is per-constructor Deriv equations + IH):
--
--   tgtM    : CertM -> Term                          -- meta TARGET endpoint
--   tgtC    : tgt (codeC c) = tgtM c                  -- target preservation
--             (mirror of T4.CertTree.srcC; the missing third projector)
--   noVar_srcM / noVar_tgtM : srcM c , tgtM c are CLOSED (NoVar)
--   parProof_accepts : parProof (codeC c) (srcM c) (tgtM c) = O
--             -- the verifier ACCEPTS every well-formed proof tree at its own
--             -- endpoints.  This is the only direction the PR plan needs:
--             -- diamond / cr CONSTRUCT proof trees (as CertM values), they
--             -- never INVERT an opaque verifier (which was the E-route trap).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ParProof where

open import T4.Base

open import T4.CertTree using
  ( CertM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeC ; srcM ; srcC ; isCertC )
open import T4.ParEnds using
  ( src ; tgt ; isCert ; pi_O_O
  ; tgt_cZe ; tgt_cSu ; tgt_cRO ; tgt_cAd ; tgt_cRS )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )
open import T4.ParIntro using
  ( eqTestF ; eqTestF_const_zero ; parBody ; parBody_app )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; mkAnd ; constTermFun1 )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  The meta TARGET endpoint  tgtM  (mirror of CertTree.srcM).
--
-- Endpoints follow the Par constructors (T4.ChurchRosserProto):
--   pZe : ze => ze                       tgt = ze#
--   pSu p : su t => su t'                tgt = su# (tgt p)
--   pAd p q : ad a b => ad a' b'         tgt = ad# (tgt p) (tgt q)
--   pRO p : ad ze y => y'                tgt = tgt p           (the contractum)
--   pRS p q : ad (su x) y => su (ad x' y')
--                                        tgt = su# (ad# (tgt p) (tgt q))

tgtM : CertM -> Term
tgtM mZe         = ze#
tgtM (mSu c)     = su# (tgtM c)
tgtM (mAd c1 c2) = ad# (tgtM c1) (tgtM c2)
tgtM (mRO c)     = tgtM c
tgtM (mRS c1 c2) = su# (ad# (tgtM c1) (tgtM c2))

------------------------------------------------------------------------
-- SECTION 2.  Target-endpoint preservation by structural induction.
--   tgtC : tgt (codeC c) = tgtM c .
-- Mirror of T4.CertTree.srcC; differs only at mRO (tgt is the contractum,
-- no  ad# ze#  wrapper) and mRS (the  su#  is OUTSIDE the  ad#  for the
-- target, INSIDE the first arg for the source).

tgtC : (c : CertM) -> Deriv (eqF (ap1 tgt (codeC c)) (tgtM c))
tgtC mZe     = tgt_cZe
tgtC (mSu c) =
  ruleTrans (tgt_cSu (codeC c)) (congR Pair tagSu (tgtC c))
tgtC (mAd c1 c2) =
  ruleTrans (tgt_cAd (codeC c1) (codeC c2))
    (congR Pair tagAd
      (ruleTrans (congL Pair (ap1 tgt (codeC c2)) (tgtC c1))
                 (congR Pair (tgtM c1) (tgtC c2))))
tgtC (mRO c) =
  ruleTrans (tgt_cRO (codeC c)) (tgtC c)
tgtC (mRS c1 c2) =
  ruleTrans (tgt_cRS (codeC c1) (codeC c2))
    (congR Pair tagSu
      (congR Pair tagAd
        (ruleTrans (congL Pair (ap1 tgt (codeC c2)) (tgtC c1))
                   (congR Pair (tgtM c1) (tgtC c2)))))

------------------------------------------------------------------------
-- SECTION 3.  The endpoint codes are CLOSED (NoVar), so they may be used as
-- the constant comparands of  eqTestF  ( eqTestF_const_zero  needs NoVar z ).
--
-- ze# = Pair O O ,  su# t = Pair (s O) t ,  ad# a b = Pair (s(s O)) (Pair a b) ;
-- NoVar (ap2 _ a b) = NoVarAnd (NoVar a)(NoVar b) , NoVar (ap1 _ t) = NoVar t ,
-- NoVar O = Unit -- so the tags  tagSu / tagAd  are var-free ( tt ).

noVar_srcM : (c : CertM) -> NoVar (srcM c)
noVar_srcM mZe         = mkAnd tt tt
noVar_srcM (mSu c)     = mkAnd tt (noVar_srcM c)
noVar_srcM (mAd c1 c2) = mkAnd tt (mkAnd (noVar_srcM c1) (noVar_srcM c2))
noVar_srcM (mRO c)     = mkAnd tt (mkAnd (mkAnd tt tt) (noVar_srcM c))
noVar_srcM (mRS c1 c2) =
  mkAnd tt (mkAnd (mkAnd tt (noVar_srcM c1)) (noVar_srcM c2))

noVar_tgtM : (c : CertM) -> NoVar (tgtM c)
noVar_tgtM mZe         = mkAnd tt tt
noVar_tgtM (mSu c)     = mkAnd tt (noVar_tgtM c)
noVar_tgtM (mAd c1 c2) = mkAnd tt (mkAnd (noVar_tgtM c1) (noVar_tgtM c2))
noVar_tgtM (mRO c)     = noVar_tgtM c
noVar_tgtM (mRS c1 c2) =
  mkAnd tt (mkAnd tt (mkAnd (noVar_tgtM c1) (noVar_tgtM c2)))

------------------------------------------------------------------------
-- SECTION 4.  The quantifier-free verifier  parProof  and its soundness.

parProof : Term -> Term -> Term -> Term
parProof p t uu = ap1 (parBody t uu) p

-- parProof ACCEPTS every well-formed proof tree at its own endpoints.
-- (Construction mirrors T4.ParIntro.parIntro's  bodyZero , but generalised
-- over the CertM shadow: validity from  isCertC , endpoints from  srcC / tgtC ,
-- closedness from  noVar_srcM / noVar_tgtM .)

parProof_accepts :
  (c : CertM) -> Deriv (eqF (parProof (codeC c) (srcM c) (tgtM c)) O)
parProof_accepts c =
  let d : Term
      d = codeC c
      ts : Term
      ts = srcM c
      uu : Term
      uu = tgtM c
      eSrc : Deriv (eqF (ap1 (eqTestF src (constTermFun1 ts)) d) O)
      eSrc = eqTestF_const_zero src ts (noVar_srcM c) d (srcC c)
      eTgt : Deriv (eqF (ap1 (eqTestF tgt (constTermFun1 uu)) d) O)
      eTgt = eqTestF_const_zero tgt uu (noVar_tgtM c) d (tgtC c)
      innerZero :
        Deriv (eqF (ap2 pi (ap1 isCert d)
                           (ap1 (eqTestF src (constTermFun1 ts)) d)) O)
      innerZero =
        ruleTrans (congL pi (ap1 (eqTestF src (constTermFun1 ts)) d) (isCertC c))
          (ruleTrans (congR pi O eSrc) pi_O_O)
      outerZero :
        Deriv (eqF (ap2 pi (ap2 pi (ap1 isCert d)
                                   (ap1 (eqTestF src (constTermFun1 ts)) d))
                           (ap1 (eqTestF tgt (constTermFun1 uu)) d)) O)
      outerZero =
        ruleTrans (congL pi (ap1 (eqTestF tgt (constTermFun1 uu)) d) innerZero)
          (ruleTrans (congR pi O eTgt) pi_O_O)
  in ruleTrans (parBody_app ts uu d) outerZero
