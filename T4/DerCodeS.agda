{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerCodeS -- the SIZE-PREFIXED object coding of parallel-reduction
-- DERIVATIONS (Thierry's directive 2026-06-22): make the induction principle
-- EXPLICIT IN THE DATA by carrying the size as the outermost field, so the
-- course-of-values measure  dsize = Fst  is a FREE projection and the opaque
-- child-descent applies cleanly (no surjective pairing, no fold-unfold on the
-- node).  Each code is
--
--     p = Pair (size p) (Pair (dtag p) (payload p))
--
-- with  size  consistent with the children:
--
--     szDerZe        = Pair (natCode 1)            (Pair dgZe O)
--     szDerSu d      = Pair (s (dsize d))          (Pair dgSu d)
--     szDerAd d1 d2  = Pair (s (sigma (dsize d1) (dsize d2))) (Pair dgAd (Pair d1 d2))
--     szDerRO d      = Pair (s (dsize d))          (Pair dgRO d)
--     szDerRS d1 d2  = Pair (s (sigma (dsize d1) (dsize d2))) (Pair dgRS (Pair d1 d2))
--
-- Delivered: accessors (dsize / dtag / pArg / pL / pR), their Deriv equations
-- (axFst / axSnd only), the SIZE-CONSISTENCY equations, and the OPAQUE
-- child-descent  descSzL/R/U  (mirroring the green T4.SizedDescentOp.descOpaque,
-- under the size-consistency hypothesis that  wfRedSized  will establish).
-- Plus the meta shadow  DerM + codeDerS  (spec/guide only).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerCodeS where

open import T4.Base

open import T4.DerCode using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.LeqMono using ( leq_sigma_left ; leq_sigma_right )

open import BRA3.Church    using ( sigma ; sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchT78 using ( T78 )
open import BRA3.RuleInst2 using ( ruleInst2 )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )

------------------------------------------------------------------------
-- SECTION 0.  Accessors (all free Fst/Snd projections).

dsize : Term -> Term                       -- the size field  = Fst p
dsize p = ap1 Fst p

dbody : Term -> Term                       -- (dtag . payload)  = Snd p
dbody p = ap1 Snd p

dtag : Term -> Term                        -- derivation tag    = Fst (Snd p)
dtag p = ap1 Fst (dbody p)

pArg : Term -> Term                        -- unary child       = Snd (Snd p)
pArg p = ap1 Snd (dbody p)

pL : Term -> Term                          -- binary left       = Fst (Snd (Snd p))
pL p = ap1 Fst (pArg p)

pR : Term -> Term                          -- binary right      = Snd (Snd (Snd p))
pR p = ap1 Snd (pArg p)

------------------------------------------------------------------------
-- SECTION 1.  Constructors.

szDerZe : Term
szDerZe = ap2 Pair (natCode 1) (ap2 Pair dgZe O)

szDerSu : Term -> Term
szDerSu d = ap2 Pair (ap1 s (dsize d)) (ap2 Pair dgSu d)

szDerAd : Term -> Term -> Term
szDerAd d1 d2 =
  ap2 Pair (ap1 s (ap2 sigma (dsize d1) (dsize d2))) (ap2 Pair dgAd (ap2 Pair d1 d2))

szDerRO : Term -> Term
szDerRO d = ap2 Pair (ap1 s (dsize d)) (ap2 Pair dgRO d)

szDerRS : Term -> Term -> Term
szDerRS d1 d2 =
  ap2 Pair (ap1 s (ap2 sigma (dsize d1) (dsize d2))) (ap2 Pair dgRS (ap2 Pair d1 d2))

------------------------------------------------------------------------
-- SECTION 2.  Size equations (dsize = Fst, all axFst).

dsize_Ze : Deriv (eqF (dsize szDerZe) (natCode 1))
dsize_Ze = axFst (natCode 1) (ap2 Pair dgZe O)

dsize_Su : (d : Term) -> Deriv (eqF (dsize (szDerSu d)) (ap1 s (dsize d)))
dsize_Su d = axFst (ap1 s (dsize d)) (ap2 Pair dgSu d)

dsize_Ad : (d1 d2 : Term) ->
  Deriv (eqF (dsize (szDerAd d1 d2)) (ap1 s (ap2 sigma (dsize d1) (dsize d2))))
dsize_Ad d1 d2 =
  axFst (ap1 s (ap2 sigma (dsize d1) (dsize d2))) (ap2 Pair dgAd (ap2 Pair d1 d2))

dsize_RO : (d : Term) -> Deriv (eqF (dsize (szDerRO d)) (ap1 s (dsize d)))
dsize_RO d = axFst (ap1 s (dsize d)) (ap2 Pair dgRO d)

dsize_RS : (d1 d2 : Term) ->
  Deriv (eqF (dsize (szDerRS d1 d2)) (ap1 s (ap2 sigma (dsize d1) (dsize d2))))
dsize_RS d1 d2 =
  axFst (ap1 s (ap2 sigma (dsize d1) (dsize d2))) (ap2 Pair dgRS (ap2 Pair d1 d2))

------------------------------------------------------------------------
-- SECTION 3.  Tag equations  (dtag = Fst (Snd p)).

dbody_Su : (d : Term) -> Deriv (eqF (dbody (szDerSu d)) (ap2 Pair dgSu d))
dbody_Su d = axSnd (ap1 s (dsize d)) (ap2 Pair dgSu d)
dbody_Ad : (d1 d2 : Term) ->
  Deriv (eqF (dbody (szDerAd d1 d2)) (ap2 Pair dgAd (ap2 Pair d1 d2)))
dbody_Ad d1 d2 = axSnd (ap1 s (ap2 sigma (dsize d1) (dsize d2))) (ap2 Pair dgAd (ap2 Pair d1 d2))
dbody_RO : (d : Term) -> Deriv (eqF (dbody (szDerRO d)) (ap2 Pair dgRO d))
dbody_RO d = axSnd (ap1 s (dsize d)) (ap2 Pair dgRO d)
dbody_RS : (d1 d2 : Term) ->
  Deriv (eqF (dbody (szDerRS d1 d2)) (ap2 Pair dgRS (ap2 Pair d1 d2)))
dbody_RS d1 d2 = axSnd (ap1 s (ap2 sigma (dsize d1) (dsize d2))) (ap2 Pair dgRS (ap2 Pair d1 d2))

dtag_Ze : Deriv (eqF (dtag szDerZe) dgZe)
dtag_Ze = ruleTrans (cong1 Fst (axSnd (natCode 1) (ap2 Pair dgZe O))) (axFst dgZe O)
dtag_Su : (d : Term) -> Deriv (eqF (dtag (szDerSu d)) dgSu)
dtag_Su d = ruleTrans (cong1 Fst (dbody_Su d)) (axFst dgSu d)
dtag_Ad : (d1 d2 : Term) -> Deriv (eqF (dtag (szDerAd d1 d2)) dgAd)
dtag_Ad d1 d2 = ruleTrans (cong1 Fst (dbody_Ad d1 d2)) (axFst dgAd (ap2 Pair d1 d2))
dtag_RO : (d : Term) -> Deriv (eqF (dtag (szDerRO d)) dgRO)
dtag_RO d = ruleTrans (cong1 Fst (dbody_RO d)) (axFst dgRO d)
dtag_RS : (d1 d2 : Term) -> Deriv (eqF (dtag (szDerRS d1 d2)) dgRS)
dtag_RS d1 d2 = ruleTrans (cong1 Fst (dbody_RS d1 d2)) (axFst dgRS (ap2 Pair d1 d2))

------------------------------------------------------------------------
-- SECTION 4.  Child equations  (pArg = Snd (Snd p) ; pL / pR for binary).

pArg_Su : (d : Term) -> Deriv (eqF (pArg (szDerSu d)) d)
pArg_Su d = ruleTrans (cong1 Snd (dbody_Su d)) (axSnd dgSu d)
pArg_RO : (d : Term) -> Deriv (eqF (pArg (szDerRO d)) d)
pArg_RO d = ruleTrans (cong1 Snd (dbody_RO d)) (axSnd dgRO d)

pArg_Ad : (d1 d2 : Term) -> Deriv (eqF (pArg (szDerAd d1 d2)) (ap2 Pair d1 d2))
pArg_Ad d1 d2 = ruleTrans (cong1 Snd (dbody_Ad d1 d2)) (axSnd dgAd (ap2 Pair d1 d2))
pArg_RS : (d1 d2 : Term) -> Deriv (eqF (pArg (szDerRS d1 d2)) (ap2 Pair d1 d2))
pArg_RS d1 d2 = ruleTrans (cong1 Snd (dbody_RS d1 d2)) (axSnd dgRS (ap2 Pair d1 d2))

pL_Ad : (d1 d2 : Term) -> Deriv (eqF (pL (szDerAd d1 d2)) d1)
pL_Ad d1 d2 = ruleTrans (cong1 Fst (pArg_Ad d1 d2)) (axFst d1 d2)
pR_Ad : (d1 d2 : Term) -> Deriv (eqF (pR (szDerAd d1 d2)) d2)
pR_Ad d1 d2 = ruleTrans (cong1 Snd (pArg_Ad d1 d2)) (axSnd d1 d2)
pL_RS : (d1 d2 : Term) -> Deriv (eqF (pL (szDerRS d1 d2)) d1)
pL_RS d1 d2 = ruleTrans (cong1 Fst (pArg_RS d1 d2)) (axFst d1 d2)
pR_RS : (d1 d2 : Term) -> Deriv (eqF (pR (szDerRS d1 d2)) d2)
pR_RS d1 d2 = ruleTrans (cong1 Snd (pArg_RS d1 d2)) (axSnd d1 d2)

------------------------------------------------------------------------
-- SECTION 5.  OPAQUE child-descent under the size-consistency hypothesis
-- (verbatim T4.SizedDescentOp with dsize / pL / pR / pArg).  This is what
-- feeds SizedTree.covMeasure (mu = dsize) on an arbitrary code  p .

descSzL : (p : Term) ->
  Deriv (eqF (dsize p) (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p))))) ->
  Deriv (leq (ap1 s (dsize (pL p))) (dsize p))
descSzL p hyp =
  let l' = dsize (pL p) ; r' = dsize (pR p)
      leqS : Deriv (leq (ap1 s l') (ap1 s (ap2 sigma l' r')))
      leqS = mp (ruleInst2 0 l' 1 (ap2 sigma l' r') refl T78) (leq_sigma_left l' r')
  in ruleTrans (congR sub (ap1 s l') hyp) leqS

descSzR : (p : Term) ->
  Deriv (eqF (dsize p) (ap1 s (ap2 sigma (dsize (pL p)) (dsize (pR p))))) ->
  Deriv (leq (ap1 s (dsize (pR p))) (dsize p))
descSzR p hyp =
  let l' = dsize (pL p) ; r' = dsize (pR p)
      leqS : Deriv (leq (ap1 s r') (ap1 s (ap2 sigma l' r')))
      leqS = mp (ruleInst2 0 r' 1 (ap2 sigma l' r') refl T78) (leq_sigma_right l' r')
  in ruleTrans (congR sub (ap1 s r') hyp) leqS

descSzU : (p : Term) ->
  Deriv (eqF (dsize p) (ap1 s (dsize (pArg p)))) ->
  Deriv (leq (ap1 s (dsize (pArg p))) (dsize p))
descSzU p hyp =
  ruleTrans (congR sub (ap1 s (dsize (pArg p))) hyp) (sub_self (ap1 s (dsize (pArg p))))

------------------------------------------------------------------------
-- SECTION 6.  Built-node size-consistency (the hypothesis discharged on the
-- constructors -- wfRedSized will re-establish it for opaque codes).

cons_Su : (d : Term) ->
  Deriv (eqF (dsize (szDerSu d)) (ap1 s (dsize (pArg (szDerSu d)))))
cons_Su d =
  ruleTrans (dsize_Su d) (cong1 s (ruleSym (cong1 Fst (pArg_Su d))))

cons_RO : (d : Term) ->
  Deriv (eqF (dsize (szDerRO d)) (ap1 s (dsize (pArg (szDerRO d)))))
cons_RO d =
  ruleTrans (dsize_RO d) (cong1 s (ruleSym (cong1 Fst (pArg_RO d))))

cons_Ad : (d1 d2 : Term) ->
  Deriv (eqF (dsize (szDerAd d1 d2))
             (ap1 s (ap2 sigma (dsize (pL (szDerAd d1 d2))) (dsize (pR (szDerAd d1 d2))))))
cons_Ad d1 d2 =
  ruleTrans (dsize_Ad d1 d2)
    (cong1 s (ruleTrans (congL sigma (dsize d2) (ruleSym (cong1 Fst (pL_Ad d1 d2))))
                        (congR sigma (dsize (pL (szDerAd d1 d2)))
                          (ruleSym (cong1 Fst (pR_Ad d1 d2))))))

cons_RS : (d1 d2 : Term) ->
  Deriv (eqF (dsize (szDerRS d1 d2))
             (ap1 s (ap2 sigma (dsize (pL (szDerRS d1 d2))) (dsize (pR (szDerRS d1 d2))))))
cons_RS d1 d2 =
  ruleTrans (dsize_RS d1 d2)
    (cong1 s (ruleTrans (congL sigma (dsize d2) (ruleSym (cong1 Fst (pL_RS d1 d2))))
                        (congR sigma (dsize (pL (szDerRS d1 d2)))
                          (ruleSym (cong1 Fst (pR_RS d1 d2))))))

------------------------------------------------------------------------
-- SECTION 7.  Meta shadow (spec/guide only -- the COV theorems quantify over
-- arbitrary  p : Term , NOT over this shadow).

data DerMS : Set where
  msZe : DerMS
  msSu : DerMS -> DerMS
  msAd : DerMS -> DerMS -> DerMS
  msRO : DerMS -> DerMS
  msRS : DerMS -> DerMS -> DerMS

codeDerS : DerMS -> Term
codeDerS msZe         = szDerZe
codeDerS (msSu d)     = szDerSu (codeDerS d)
codeDerS (msAd d1 d2) = szDerAd (codeDerS d1) (codeDerS d2)
codeDerS (msRO d)     = szDerRO (codeDerS d)
codeDerS (msRS d1 d2) = szDerRS (codeDerS d1) (codeDerS d2)
