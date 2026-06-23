{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrConfl -- object multi-step parallel reduction RedsU = RedU*, the strip
-- lemma and confluence for the FULL closed-term p.r. calculus, transcribed
-- clause-for-clause from T4.DerConfl onto the object diamond  objDiamondU
-- (T4.PrDiamond).  Pure shadow combinatorics; the only reduction content is the
-- single diamond.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrConfl where

open import T4.Base

open import T4.PrTriShadow using ( DerM ; codeDer ; triMeta )
open import T4.PrDev  using ( devF )
open import T4.PrDiamond
  using ( RedU ; Join1U ; objDiamondU ; triLeg )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

------------------------------------------------------------------------
-- SECTION 1.  Multi-step object reduction  RedsU = RedU* .

data RedsU : Term -> Term -> Set where
  rsdoneU : {t : Term} -> RedsU t t
  rsmoreU : {t u v : Term} (p : DerM) -> RedU p t u -> RedsU u v -> RedsU t v

redsTransU : {t u v : Term} -> RedsU t u -> RedsU u v -> RedsU t v
redsTransU rsdoneU             ss2 = ss2
redsTransU (rsmoreU p rs1 ss)  ss2 = rsmoreU p rs1 (redsTransU ss ss2)

red1U : {p : DerM} {t u : Term} -> RedU p t u -> RedsU t u
red1U {p} r = rsmoreU p r rsdoneU

------------------------------------------------------------------------
-- SECTION 2.  Strip lemma.

stripU : {t u v : Term} {p : DerM} ->
  RedU p t u -> RedsU t v ->
  Sigma Term (\ w -> And (RedsU u w) (Sigma DerM (\ r -> RedU r v w)))
stripU rp rsdoneU =
  mkSigma _ (mkAnd rsdoneU (mkSigma _ rp))
stripU rp (rsmoreU q rq qs) =
  let d    = objDiamondU rp rq
      legU = andL (snd d)
      legM = andR (snd d)
      rec  = stripU (snd legM) qs
  in mkSigma (fst rec)
       (mkAnd (rsmoreU (fst legU) (snd legU) (andL (snd rec)))
              (andR (snd rec)))

------------------------------------------------------------------------
-- SECTION 3.  Confluence.

conflU : {t v1 v2 : Term} ->
  RedsU t v1 -> RedsU t v2 ->
  Sigma Term (\ w -> And (RedsU v1 w) (RedsU v2 w))
conflU rsdoneU qs = mkSigma _ (mkAnd qs rsdoneU)
conflU (rsmoreU p rp ps) qs =
  let sres = stripU rp qs
      rec  = conflU ps (andL (snd sres))
  in mkSigma (fst rec)
       (mkAnd (andL (snd rec))
              (rsmoreU (fst (andR (snd sres))) (snd (andR (snd sres))) (andR (snd rec))))

------------------------------------------------------------------------
-- SECTION 4.  ObjJoinU and the headlines.

ObjJoinU : Term -> Term -> Set
ObjJoinU b c = Sigma Term (\ w -> And (RedsU b w) (RedsU c w))

objCRU : {p q : DerM} {a b c : Term} ->
  RedU p a b -> RedU q a c -> ObjJoinU b c
objCRU {p} {q} {a} rp rq =
  mkSigma (ap1 devF a)
    (mkAnd (red1U (triLeg p rp)) (red1U (triLeg q rq)))

objConvJoinU : {a v1 v2 : Term} -> RedsU a v1 -> RedsU a v2 -> ObjJoinU v1 v2
objConvJoinU = conflU
