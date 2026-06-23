{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrClash -- head-stability and the 0 / s0 clash for the FULL closed-term
-- p.r. calculus, on the object reduction RedsU (T4.PrConfl), mirroring
-- T4.DerClash.  The two normal forms tmO ("0") and tmAp1 cSuc tmO ("s0") differ
-- by head tag (0 vs 1); the s-congruence is the only step preserving an
-- s-headed source (detected by the carried fun cSuc), so a chain from s0 stays
-- s-headed and a chain from 0 stays 0 -- they cannot meet.
--
-- HONEST SCOPE (same as T4.DerClash).  The headline is the OBJECT inconsistency
-- transfer
--   convClashU : ConvU tmO (tmAp1 cSuc tmO) -> Deriv (eqF (ap1 s O) O)
-- "if 0 is object-convertible to s0 then BRA derives the false atom s0 = 0"
-- (refuted by ax_succ_nonzero).  This is Con(Eq) in SCHEMATIC form (ConvU is a
-- META inductive over object codes), for the full closed-term equational theory
-- of Fun1={s,o,u,C}, Fun2={v,R}.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrClash where

open import T4.Base

open import T4.PrTriShadow
  using ( DerM ; mRefl ; mAp1c ; mAp2c ; mO ; mU ; mV ; mC ; mRb ; mRs
        ; Fun1M ; f1S ; f1Zero ; f1Id ; f1Comp ; Fun2M ; f2Proj ; f2Rec
        ; codeF1 ; codeF2 ; codeDer )
open import T4.PrCodeObj
  using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cZero ; cId ; cComp ; cProj ; cRec
        ; tgSuc ; tgZero ; tgId ; tgComp ; tgProj ; tgRec ; hd_tmO )
open import T4.PrSrc
  using ( srcF ; srcF_reflO ; srcF_ap1c ; srcF_ap2c
        ; srcF_rO ; srcF_rU ; srcF_rV ; srcF_rC ; srcF_rRb ; srcF_rRs )
open import T4.PrTgt using ( tgtF ; tgtF_reflO ; tgtF_ap1c )
open import T4.PrTriPres using ( hdAp1 ; funAp1 ; hdAp2 ; funAp2 )
open import T4.PrDiamond using ( RedU )
open import T4.PrConfl
  using ( RedsU ; rsdoneU ; rsmoreU ; redsTransU ; red1U ; ObjJoinU ; conflU )

open import T4.ChurchRosserProto
  using ( Sigma ; mkSigma ; fst ; snd ; And ; mkAnd ; andL ; andR )

open import BRA3.Church   using ( predecessor ; T_p_S_v0 )
open import BRA3.ChurchT80 using ( succEqO_to_anything )

------------------------------------------------------------------------
-- SECTION 0.  Explosion helpers.

exF : (t : Term) {Q : Formula} -> Deriv (eqF (ap1 s t) O) -> Deriv Q
exF t e = mp (succEqO_to_anything t _) e

predS : (X : Term) -> Deriv (eqF (ap1 predecessor (ap1 s X)) X)
predS X = ruleInst 0 X T_p_S_v0

succInjN : (m k : Nat) -> Deriv (eqF (natCode (suc m)) (natCode (suc k))) ->
           Deriv (eqF (natCode m) (natCode k))
succInjN m k eq =
  ruleTrans (ruleSym (predS (natCode m)))
            (ruleTrans (cong1 predecessor eq) (predS (natCode k)))

sucCong : {m k : Nat} -> Eq m k -> Eq (suc m) (suc k)
sucCong refl = refl

-- natCode m = natCode k with m != k explodes.
natClashDown : {Q : Formula} (m k : Nat) -> ((Eq m k) -> Empty) ->
               Deriv (eqF (natCode m) (natCode k)) -> Deriv Q
natClashDown zero zero neq eq = emptyElim (neq refl)
natClashDown (suc m) zero neq eq = exF (natCode m) eq
natClashDown zero (suc k) neq eq = exF (natCode k) (ruleSym eq)
natClashDown (suc m) (suc k) neq eq =
  natClashDown m k (\ em -> neq (sucCong em)) (succInjN m k eq)

------------------------------------------------------------------------
-- SECTION 1.  Head-stability: only mRefl preserves a tmO source.

-- from a source equation  srcF p = tmAp1 f X  (or tmAp2 ...), the head tag.
headClash : {Q : Formula} (S : Term) (h : Nat) ->
  Deriv (eqF (ap1 Fst S) (natCode h)) -> ((Eq h 0) -> Empty) ->
  Deriv (eqF S tmO) -> Deriv Q
headClash S h hS h0 hyp =
  natClashDown h 0 h0 (ruleTrans (ruleSym hS) (ruleTrans (cong1 Fst hyp) hd_tmO))

headStabO : (p : DerM) ->
  Deriv (eqF (ap1 srcF (codeDer p)) tmO) ->
  Deriv (eqF (ap1 tgtF (codeDer p)) tmO)
headStabO mRefl hyp = tgtF_reflO
headStabO (mAp1c fm d) hyp =
  headClash (ap1 srcF (codeDer (mAp1c fm d))) 1
    (ruleTrans (cong1 Fst (srcF_ap1c (codeF1 fm) (codeDer d))) (hdAp1 (codeF1 fm) (ap1 srcF (codeDer d)))) (\ ()) hyp
headStabO (mAp2c fm d1 d2) hyp =
  headClash (ap1 srcF (codeDer (mAp2c fm d1 d2))) 2
    (ruleTrans (cong1 Fst (srcF_ap2c (codeF2 fm) (codeDer d1) (codeDer d2)))
       (hdAp2 (codeF2 fm) (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2)))) (\ ()) hyp
headStabO (mO d) hyp =
  headClash (ap1 srcF (codeDer (mO d))) 1
    (ruleTrans (cong1 Fst (srcF_rO (codeDer d))) (hdAp1 cZero (ap1 srcF (codeDer d)))) (\ ()) hyp
headStabO (mU d) hyp =
  headClash (ap1 srcF (codeDer (mU d))) 1
    (ruleTrans (cong1 Fst (srcF_rU (codeDer d))) (hdAp1 cId (ap1 srcF (codeDer d)))) (\ ()) hyp
headStabO (mV d1 d2) hyp =
  headClash (ap1 srcF (codeDer (mV d1 d2))) 2
    (ruleTrans (cong1 Fst (srcF_rV (codeDer d1) (codeDer d2)))
       (hdAp2 cProj (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2)))) (\ ()) hyp
headStabO (mC g h1 h2 d) hyp =
  headClash (ap1 srcF (codeDer (mC g h1 h2 d))) 1
    (ruleTrans (cong1 Fst (srcF_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d)))
       (hdAp1 (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (ap1 srcF (codeDer d)))) (\ ()) hyp
headStabO (mRb g h1 h2 d) hyp =
  headClash (ap1 srcF (codeDer (mRb g h1 h2 d))) 2
    (ruleTrans (cong1 Fst (srcF_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d)))
       (hdAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 srcF (codeDer d)) tmO)) (\ ()) hyp
headStabO (mRs g h1 h2 d1 d2) hyp =
  headClash (ap1 srcF (codeDer (mRs g h1 h2 d1 d2))) 2
    (ruleTrans (cong1 Fst (srcF_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2)))
       (hdAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 srcF (codeDer d1)) (tmAp1 cSuc (ap1 srcF (codeDer d2))))) (\ ()) hyp

------------------------------------------------------------------------
-- SECTION 2.  Head-stability: only mAp1c f1S preserves an s-headed source.

-- from  S = tmAp1 cSuc t , refute  S = tmAp1 <fun> X  with fun-head mf != 3.
funClash : {Q : Formula} (S f X : Term) (mf : Nat) ->
  Deriv (eqF S (tmAp1 f X)) -> Deriv (eqF (ap1 Fst f) (natCode mf)) -> ((Eq mf 3) -> Empty) ->
  {t : Term} -> Deriv (eqF S (tmAp1 cSuc t)) -> Deriv Q
funClash S f X mf shapeEq hf mf3 {t} hyp =
  let eqShapes : Deriv (eqF (tmAp1 f X) (tmAp1 cSuc t))
      eqShapes = ruleTrans (ruleSym shapeEq) hyp
  in natClashDown mf 3 mf3
       (ruleTrans (ruleSym (funAp1 f X mf hf))
          (ruleTrans (cong1 Fst (cong1 Fst (cong1 Snd eqShapes))) (funAp1 cSuc t 3 (axFst tgSuc O))))

-- ap2-headed sources: head 2 != 1.
hd2Clash : {Q : Formula} (S g a b : Term) ->
  Deriv (eqF S (tmAp2 g a b)) -> {t : Term} -> Deriv (eqF S (tmAp1 cSuc t)) -> Deriv Q
hd2Clash S g a b shapeEq {t} hyp =
  natClashDown 2 1 (\ ())
    (ruleTrans (ruleSym (ruleTrans (cong1 Fst shapeEq) (hdAp2 g a b)))
       (ruleTrans (cong1 Fst hyp) (hdAp1 cSuc t)))

headStabSuc : (p : DerM) {t : Term} ->
  Deriv (eqF (ap1 srcF (codeDer p)) (tmAp1 cSuc t)) ->
  Sigma Term (\ t' -> Deriv (eqF (ap1 tgtF (codeDer p)) (tmAp1 cSuc t')))
headStabSuc (mAp1c f1S d) hyp =
  mkSigma (ap1 tgtF (codeDer d)) (tgtF_ap1c cSuc (codeDer d))
headStabSuc mRefl {t} hyp =
  mkSigma O (natClashDown 0 1 (\ ())
    (ruleTrans (ruleSym (ruleTrans (cong1 Fst srcF_reflO) hd_tmO))
       (ruleTrans (cong1 Fst hyp) (hdAp1 cSuc t))))
headStabSuc (mAp1c f1Zero d) {t} hyp =
  mkSigma O (funClash (ap1 srcF (codeDer (mAp1c f1Zero d))) cZero (ap1 srcF (codeDer d)) 4
    (srcF_ap1c cZero (codeDer d)) (axFst tgZero O) (\ ()) {t} hyp)
headStabSuc (mAp1c f1Id d) {t} hyp =
  mkSigma O (funClash (ap1 srcF (codeDer (mAp1c f1Id d))) cId (ap1 srcF (codeDer d)) 5
    (srcF_ap1c cId (codeDer d)) (axFst tgId O) (\ ()) {t} hyp)
headStabSuc (mAp1c (f1Comp g h1 h2) d) {t} hyp =
  mkSigma O (funClash (ap1 srcF (codeDer (mAp1c (f1Comp g h1 h2) d)))
    (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (ap1 srcF (codeDer d)) 6
    (srcF_ap1c (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (codeDer d))
    (axFst tgComp (ap2 Pair (codeF2 g) (ap2 Pair (codeF1 h1) (codeF1 h2)))) (\ ()) {t} hyp)
headStabSuc (mAp2c fm d1 d2) {t} hyp =
  mkSigma O (hd2Clash (ap1 srcF (codeDer (mAp2c fm d1 d2))) (codeF2 fm) (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2))
    (srcF_ap2c (codeF2 fm) (codeDer d1) (codeDer d2)) {t} hyp)
headStabSuc (mO d) {t} hyp =
  mkSigma O (funClash (ap1 srcF (codeDer (mO d))) cZero (ap1 srcF (codeDer d)) 4
    (srcF_rO (codeDer d)) (axFst tgZero O) (\ ()) {t} hyp)
headStabSuc (mU d) {t} hyp =
  mkSigma O (funClash (ap1 srcF (codeDer (mU d))) cId (ap1 srcF (codeDer d)) 5
    (srcF_rU (codeDer d)) (axFst tgId O) (\ ()) {t} hyp)
headStabSuc (mV d1 d2) {t} hyp =
  mkSigma O (hd2Clash (ap1 srcF (codeDer (mV d1 d2))) cProj (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2))
    (srcF_rV (codeDer d1) (codeDer d2)) {t} hyp)
headStabSuc (mC g h1 h2 d) {t} hyp =
  mkSigma O (funClash (ap1 srcF (codeDer (mC g h1 h2 d)))
    (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (ap1 srcF (codeDer d)) 6
    (srcF_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d))
    (axFst tgComp (ap2 Pair (codeF2 g) (ap2 Pair (codeF1 h1) (codeF1 h2)))) (\ ()) {t} hyp)
headStabSuc (mRb g h1 h2 d) {t} hyp =
  mkSigma O (hd2Clash (ap1 srcF (codeDer (mRb g h1 h2 d))) (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 srcF (codeDer d)) tmO
    (srcF_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d)) {t} hyp)
headStabSuc (mRs g h1 h2 d1 d2) {t} hyp =
  mkSigma O (hd2Clash (ap1 srcF (codeDer (mRs g h1 h2 d1 d2))) (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
    (ap1 srcF (codeDer d1)) (tmAp1 cSuc (ap1 srcF (codeDer d2)))
    (srcF_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2)) {t} hyp)

------------------------------------------------------------------------
-- SECTION 3.  Chain inversions, threading the object source equation.

redsOInvU : {s w : Term} -> RedsU s w -> Deriv (eqF s tmO) -> Deriv (eqF w tmO)
redsOInvU rsdoneU es = es
redsOInvU (rsmoreU p (mkAnd esrc etgt) rest) es =
  redsOInvU rest (ruleTrans (ruleSym etgt) (headStabO p (ruleTrans esrc es)))

redsSucInvU : {s w : Term} -> RedsU s w ->
  Sigma Term (\ t -> Deriv (eqF s (tmAp1 cSuc t))) ->
  Sigma Term (\ t' -> Deriv (eqF w (tmAp1 cSuc t')))
redsSucInvU rsdoneU h = h
redsSucInvU (rsmoreU p (mkAnd esrc etgt) rest) (mkSigma t es) =
  let hs = headStabSuc p (ruleTrans esrc es)
  in redsSucInvU rest (mkSigma (fst hs) (ruleTrans (ruleSym etgt) (snd hs)))

------------------------------------------------------------------------
-- SECTION 4.  THE CLASH and the Con(Eq) headline (schematic).

objJoinClashU : ObjJoinU tmO (tmAp1 cSuc tmO) -> Deriv (eqF (ap1 s O) O)
objJoinClashU (mkSigma w (mkAnd r0 rS)) =
  let wO : Deriv (eqF w tmO)
      wO = redsOInvU r0 (axRefl tmO)
      wSuc : Sigma Term (\ t' -> Deriv (eqF w (tmAp1 cSuc t')))
      wSuc = redsSucInvU rS (mkSigma tmO (axRefl (tmAp1 cSuc tmO)))
      oSuc : Deriv (eqF tmO (tmAp1 cSuc (fst wSuc)))
      oSuc = ruleTrans (ruleSym wO) (snd wSuc)
  in ruleTrans (ruleSym (hdAp1 cSuc (fst wSuc)))
       (ruleTrans (cong1 Fst (ruleSym oSuc)) hd_tmO)

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
convJoinU (cstepU p r)  = mkSigma _ (mkAnd (red1U r) rsdoneU)
convJoinU creflU        = mkSigma _ (mkAnd rsdoneU rsdoneU)
convJoinU (csymU c)     = joinSymU (convJoinU c)
convJoinU (ctransU c1 c2) = joinTransU (convJoinU c1) (convJoinU c2)

-- Con(Eq), schematic object form: object-convertibility of 0 and s0 forces BRA
-- to prove the false atom  s O = O  (refuted by ax_succ_nonzero).
convClashU : ConvU tmO (tmAp1 cSuc tmO) -> Deriv (eqF (ap1 s O) O)
convClashU c = objJoinClashU (convJoinU c)
