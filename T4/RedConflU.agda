{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RedConflU -- STEP 2 of the OPAQUE confluence: multi-step parallel
-- reduction  RedsU = RedU* over OPAQUE codes, the strip lemma, and confluence,
-- transcribed clause-for-clause from T4.DerConfl onto the opaque diamond
-- objDiamondU (T4.RedDiamondU), whose steps are genuine VALID one-step
-- reductions  RedU p a b  (wfRed p = O, srcF p = a, tgtF p = b).
--
--   stripU : a single valid step against a valid chain joins;
--   conflU : two valid chains from a common source join (Church-Rosser);
--   objConvJoinU = conflU  (the headline at chain level).
--
-- The reduction-step witnesses are now OPAQUE codes  p : Term  (not the meta
-- shadow DerM), so the entire trace lives at the object code level.  The only
-- reduction content is the one diamond  objDiamondU .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.RedConflU where

open import T4.Base

open import T4.DerDev using ( devF )
open import T4.RedDiamondU
  using ( RedU ; Join1U ; objDiamondU ; triLeg )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

------------------------------------------------------------------------
-- SECTION 1.  Multi-step opaque reduction  RedsU = RedU* .

data RedsU : Term -> Term -> Set where
  rsdoneU : {t : Term} -> RedsU t t
  rsmoreU : {t u v : Term} (p : Term) -> RedU p t u -> RedsU u v -> RedsU t v

redsTransU : {t u v : Term} -> RedsU t u -> RedsU u v -> RedsU t v
redsTransU rsdoneU             ss2 = ss2
redsTransU (rsmoreU p rs1 ss)  ss2 = rsmoreU p rs1 (redsTransU ss ss2)

red1U : {p t u : Term} -> RedU p t u -> RedsU t u
red1U {p} r = rsmoreU p r rsdoneU

------------------------------------------------------------------------
-- SECTION 2.  Strip lemma: a single opaque step against an opaque chain.

stripU : {t u v p : Term} ->
  RedU p t u -> RedsU t v ->
  Sigma Term (\ w -> And (RedsU u w) (Sigma Term (\ r -> RedU r v w)))
stripU rp rsdoneU =
  mkSigma _ (mkAnd rsdoneU (mkSigma _ rp))
stripU rp (rsmoreU q rq qs) =
  let d    = objDiamondU rp rq                  -- common reduct of u and q's target
      legU = andL (snd d)                        -- Sigma Term (RedU _ u w0)
      legM = andR (snd d)                        -- Sigma Term (RedU _ (q-tgt) w0)
      rec  = stripU (snd legM) qs
  in mkSigma (fst rec)
       (mkAnd (rsmoreU (fst legU) (snd legU) (andL (snd rec)))
              (andR (snd rec)))

------------------------------------------------------------------------
-- SECTION 3.  Confluence of  RedU* : two opaque chains from a common source join.

conflU : {t v1 v2 : Term} ->
  RedsU t v1 -> RedsU t v2 ->
  Sigma Term (\ w -> And (RedsU v1 w) (RedsU v2 w))
conflU rsdoneU qs = mkSigma _ (mkAnd qs rsdoneU)
conflU (rsmoreU p rp ps) qs =
  let sres = stripU rp qs                        -- And (RedsU u w0) (Sigma Term (RedU _ v2 w0))
      rec  = conflU ps (andL (snd sres))
  in mkSigma (fst rec)
       (mkAnd (andL (snd rec))
              (rsmoreU (fst (andR (snd sres))) (snd (andR (snd sres))) (andR (snd rec))))

------------------------------------------------------------------------
-- SECTION 4.  ObjJoinU and the headlines.

ObjJoinU : Term -> Term -> Set
ObjJoinU b c = Sigma Term (\ w -> And (RedsU b w) (RedsU c w))

-- objCRU : two single opaque steps out of a common source join (apex devF a).
objCRU : {p q : Term} {a b c : Term} ->
  RedU p a b -> RedU q a c -> ObjJoinU b c
objCRU {p} {q} {a} rp rq =
  mkSigma (ap1 devF a)
    (mkAnd (red1U (triLeg p rp)) (red1U (triLeg q rq)))

-- objConvJoinU : confluence of whole opaque reduction sequences.
objConvJoinU : {a v1 v2 : Term} -> RedsU a v1 -> RedsU a v2 -> ObjJoinU v1 v2
objConvJoinU = conflU
