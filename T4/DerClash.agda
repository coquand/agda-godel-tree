{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerClash -- STEP 4 (clash + convertibility headline), OBJECT level.
--
-- Head-stability and the 0 / s0 clash, on the object reduction RedsU
-- (T4.DerConfl), mirroring the meta T4.ObjCRClash but with object-Deriv
-- endpoints.  The meta proof inverts the inductive  Red  family; here RedsU
-- carries the derivation SHADOW (DerM), so we invert on the shadow + the
-- object srcF / tgtF head equations, threading the object source-equation
-- through the chain induction (the IH consumes  eqF u ze#  etc.).  Impossible
-- head tags explode via  succEqO_to_anything  ( s _ = O  =>  anything ) and, for
-- the two-successor tag clash ad#/su#, one  predecessor  cancellation.
--
-- HONEST SCOPE.  The headline produced here is the OBJECT inconsistency
-- transfer
--
--   convClashU : ConvU ze# (su# ze#) -> Deriv (eqF (ap1 s O) O)
--
-- "if 0 is object-convertible to s0 then BRA derives the false atom s0 = 0"
-- (whose negation BRA proves: ax_succ_nonzero).  This is Con(Eq) in schematic
-- form: ConvU is a META inductive over object codes.  A single fully-internal
-- object derivation of Con(Eq) (an object provability predicate for Eq,
-- quantified, refuted in BRA) additionally needs the reflection layer; an
-- object contradiction (Deriv P + Deriv (neg P)) does NOT by itself yield a
-- meta Empty, so we deliver the inconsistency-transfer, not a meta `Not`.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerClash where

open import T4.Base

open import T4.DerCode
  using ( DerM ; mZe ; mSu ; mAd ; mRO ; mRS ; codeDer
        ; derZe ; derSu ; derAd ; derRO ; derRS )
open import T4.DerSrc
  using ( srcF ; srcF_derZe ; srcF_derSu ; srcF_derAd ; srcF_derRO ; srcF_derRS )
open import T4.DerTgt using ( tgtF ; tgtF_derZe ; tgtF_derSu )
open import T4.TrsCodeObj
  using ( ze# ; su# ; ad# ; tagZe ; tagSu ; tagAd ; hd ; hd_ze ; hd_su ; hd_ad )
open import T4.DerTriShadow using ( RedU )
open import T4.DerConfl
  using ( RedsU ; rsdoneU ; rsmoreU ; redsTransU ; red1U ; ObjJoinU ; conflU )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

open import BRA3.Church  using ( predecessor ; T_p_S_v0 )
open import BRA3.ChurchT80 using ( succEqO_to_anything )

------------------------------------------------------------------------
-- SECTION 0.  Object explosion helpers.

-- from  s t = O  derive anything.
exF : (t : Term) {Q : Formula} -> Deriv (eqF (ap1 s t) O) -> Deriv Q
exF t e = mp (succEqO_to_anything t _) e

-- predecessor cancellation:  pred (s X) = X .
predS : (X : Term) -> Deriv (eqF (ap1 predecessor (ap1 s X)) X)
predS X = ruleInst 0 X T_p_S_v0

-- the two-successor tag clash  tagAd = tagSu  ( s (s O) = s O )  explodes:
-- cancel one predecessor to reach  s O = O .
exFAdSu : {Q : Formula} -> Deriv (eqF tagAd tagSu) -> Deriv Q
exFAdSu e =
  exF O (ruleTrans (ruleSym (predS (ap1 s O)))
                   (ruleTrans (cong1 predecessor e) (predS O)))

------------------------------------------------------------------------
-- SECTION 1.  Head-stability by shadow case analysis (object src/tgt heads).
--
-- headStabZe : if the source of  p  is ze# then so is its target (only the
-- reflexive  mZe  derivation has a ze#-headed source; every other shadow has a
-- su#- or ad#-headed source, refuted by the head tag).

headStabZe : (p : DerM) ->
  Deriv (eqF (ap1 srcF (codeDer p)) ze#) ->
  Deriv (eqF (ap1 tgtF (codeDer p)) ze#)
headStabZe mZe hyp = tgtF_derZe
headStabZe (mSu q) hyp =
  exF O (ruleTrans (ruleSym (hd_su (ap1 srcF (codeDer q))))
           (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derSu (codeDer q))) hyp)) hd_ze))
headStabZe (mAd q1 q2) hyp =
  exF (ap1 s O)
    (ruleTrans (ruleSym (hd_ad (ap1 srcF (codeDer q1)) (ap1 srcF (codeDer q2))))
       (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derAd (codeDer q1) (codeDer q2))) hyp))
                  hd_ze))
headStabZe (mRO q) hyp =
  exF (ap1 s O)
    (ruleTrans (ruleSym (hd_ad ze# (ap1 srcF (codeDer q))))
       (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derRO (codeDer q))) hyp)) hd_ze))
headStabZe (mRS q1 q2) hyp =
  exF (ap1 s O)
    (ruleTrans (ruleSym (hd_ad (su# (ap1 srcF (codeDer q1))) (ap1 srcF (codeDer q2))))
       (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derRS (codeDer q1) (codeDer q2))) hyp))
                  hd_ze))

-- headStabSu : if the source of  p  is su#-headed then its target is su#-headed
-- (only  mSu  has a su#-headed source).
headStabSu : (p : DerM) {t : Term} ->
  Deriv (eqF (ap1 srcF (codeDer p)) (su# t)) ->
  Sigma Term (\ t' -> Deriv (eqF (ap1 tgtF (codeDer p)) (su# t')))
headStabSu (mSu q) hyp = mkSigma (ap1 tgtF (codeDer q)) (tgtF_derSu (codeDer q))
headStabSu mZe hyp =
  mkSigma O
    (exF O (ruleSym
      (ruleTrans (ruleSym hd_ze)
         (ruleTrans (cong1 Fst (ruleTrans (ruleSym srcF_derZe) hyp)) (hd_su _)))))
headStabSu (mAd q1 q2) hyp =
  mkSigma O
    (exFAdSu
      (ruleTrans (ruleSym (hd_ad (ap1 srcF (codeDer q1)) (ap1 srcF (codeDer q2))))
         (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derAd (codeDer q1) (codeDer q2))) hyp))
                    (hd_su _))))
headStabSu (mRO q) hyp =
  mkSigma O
    (exFAdSu
      (ruleTrans (ruleSym (hd_ad ze# (ap1 srcF (codeDer q))))
         (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derRO (codeDer q))) hyp)) (hd_su _))))
headStabSu (mRS q1 q2) hyp =
  mkSigma O
    (exFAdSu
      (ruleTrans (ruleSym (hd_ad (su# (ap1 srcF (codeDer q1))) (ap1 srcF (codeDer q2))))
         (ruleTrans (cong1 Fst (ruleTrans (ruleSym (srcF_derRS (codeDer q1) (codeDer q2))) hyp))
                    (hd_su _))))

------------------------------------------------------------------------
-- SECTION 2.  Chain inversions, threading the object source-equation.

redsZeInvU : {s w : Term} -> RedsU s w -> Deriv (eqF s ze#) -> Deriv (eqF w ze#)
redsZeInvU rsdoneU es = es
redsZeInvU (rsmoreU p (mkAnd esrc etgt) rest) es =
  redsZeInvU rest
    (ruleTrans (ruleSym etgt) (headStabZe p (ruleTrans esrc es)))

redsSuInvU : {s w : Term} -> RedsU s w ->
  Sigma Term (\ t -> Deriv (eqF s (su# t))) ->
  Sigma Term (\ t' -> Deriv (eqF w (su# t')))
redsSuInvU rsdoneU h = h
redsSuInvU (rsmoreU p (mkAnd esrc etgt) rest) (mkSigma t es) =
  let hs : Sigma Term (\ t'' -> Deriv (eqF (ap1 tgtF (codeDer p)) (su# t'')))
      hs = headStabSu p (ruleTrans esrc es)
  in redsSuInvU rest (mkSigma (fst hs) (ruleTrans (ruleSym etgt) (snd hs)))

------------------------------------------------------------------------
-- SECTION 3.  THE CLASH:  a common reduct of ze# and su# ze# makes BRA prove
-- the false atom  s O = O .

objJoinClashU : ObjJoinU ze# (su# ze#) -> Deriv (eqF (ap1 s O) O)
objJoinClashU (mkSigma w (mkAnd r0 rS)) =
  let wZe : Deriv (eqF w ze#)
      wZe = redsZeInvU r0 (axRefl ze#)
      wSu : Sigma Term (\ t' -> Deriv (eqF w (su# t')))
      wSu = redsSuInvU rS (mkSigma ze# (axRefl (su# ze#)))
      zeSu : Deriv (eqF ze# (su# (fst wSu)))
      zeSu = ruleTrans (ruleSym wZe) (snd wSu)
  in ruleSym
       (ruleTrans (ruleSym hd_ze)
          (ruleTrans (cong1 Fst zeSu) (hd_su (fst wSu))))

------------------------------------------------------------------------
-- SECTION 4.  Object convertibility and the Con(Eq) headline (schematic).

data ConvU : Term -> Term -> Set where
  cstepU  : (p : DerM) {t u : Term} -> RedU p t u -> ConvU t u
  creflU  : {t : Term} -> ConvU t t
  csymU   : {t u : Term} -> ConvU t u -> ConvU u t
  ctransU : {t u v : Term} -> ConvU t u -> ConvU u v -> ConvU t v

joinSymU : {t u : Term} -> ObjJoinU t u -> ObjJoinU u t
joinSymU (mkSigma w p) = mkSigma w (mkAnd (andR p) (andL p))

joinTransU : {t u v : Term} -> ObjJoinU t u -> ObjJoinU u v -> ObjJoinU t v
joinTransU (mkSigma w1 p1) (mkSigma w2 p2) =
  let c = conflU (andR p1) (andL p2)
  in mkSigma (fst c)
       (mkAnd (redsTransU (andL p1) (andL (snd c)))
              (redsTransU (andR p2) (andR (snd c))))

convJoinU : {a b : Term} -> ConvU a b -> ObjJoinU a b
convJoinU (cstepU p r) = mkSigma _ (mkAnd (red1U r) rsdoneU)
convJoinU creflU       = mkSigma _ (mkAnd rsdoneU rsdoneU)
convJoinU (csymU c)            = joinSymU (convJoinU c)
convJoinU (ctransU c1 c2)      = joinTransU (convJoinU c1) (convJoinU c2)

-- Con(Eq), schematic object form: object-convertibility of 0 and s0 forces BRA
-- to prove the false atom  s O = O  (refuted by ax_succ_nonzero).
convClashU : ConvU ze# (su# ze#) -> Deriv (eqF (ap1 s O) O)
convClashU c = objJoinClashU (convJoinU c)
