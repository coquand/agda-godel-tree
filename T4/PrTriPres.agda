{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriPres -- the ENDPOINT-PRESERVATION (the triangle commutes), the heart
-- of internal Church-Rosser, generalising T4.DerTriPres:
--
--   src_tri : srcF (triF (codeDer d)) = tgtF (codeDer d)
--   tgt_tri : tgtF (triF (codeDer d)) = devF (srcF (codeDer d))
--
-- proved by one structural induction on the refined shadow d (T4.PrTriShadow),
-- via  triShadowU  (replace triF(codeDer d) by codeDer(triMeta d)) so each case
-- chains the srcF / tgtF / devF defining equations + IH.  The critical pairs
-- (ap1c o/u/C exposing redexes, ap2c-cRec Rb/Rs/Rcong) commute exactly because
-- the system is orthogonal -- e.g. the Rs residual matches devF_Rs verbatim.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTriPres where

open import T4.Base

open import T4.PrCodeObj
  using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cZero ; cId ; cComp ; cProj ; cRec
        ; tgAp1 ; tgAp2 ; tgSuc ; tgZero ; tgId ; tgComp ; tgProj ; tgRec )
open import T4.PrDerCode using ( ap1c ; ap2c )
open import T4.PrTri using ( triF )
open import T4.PrTriShadow
  using ( DerM ; mRefl ; mAp1c ; mAp2c ; mO ; mU ; mV ; mC ; mRb ; mRs
        ; Fun1M ; f1S ; f1Zero ; f1Id ; f1Comp ; Fun2M ; f2Proj ; f2Rec
        ; codeF1 ; codeF2 ; codeDer ; triMeta ; triShadowU )
open import T4.PrSrc
  using ( srcF ; srcF_reflO ; srcF_ap1c ; srcF_ap2c
        ; srcF_rO ; srcF_rU ; srcF_rV ; srcF_rC ; srcF_rRb ; srcF_rRs )
open import T4.PrTgt
  using ( tgtF ; tgtF_reflO ; tgtF_ap1c ; tgtF_ap2c
        ; tgtF_rO ; tgtF_rU ; tgtF_rV ; tgtF_rC ; tgtF_rRb ; tgtF_rRs )
open import T4.PrDev
  using ( devF ; devF_tmO ; devF_ap1_s ; devF_o ; devF_u ; devF_v
        ; devF_C ; devF_Rb ; devF_Rs )
open import T4.PrDevRcong using ( devF_R_cong )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  Congruence helpers on term arguments.

cTmAp1 : (f X X' : Term) -> Deriv (eqF X X') -> Deriv (eqF (tmAp1 f X) (tmAp1 f X'))
cTmAp1 f X X' eq = congR pi tgAp1 (congR pi f eq)

cTmAp2 : (g X1 X1' X2 X2' : Term) -> Deriv (eqF X1 X1') -> Deriv (eqF X2 X2') ->
         Deriv (eqF (tmAp2 g X1 X2) (tmAp2 g X1' X2'))
cTmAp2 g X1 X1' X2 X2' e1 e2 =
  congR pi tgAp2 (congR pi g (ruleTrans (congL pi X2 e1) (congR pi X1' e2)))

cTmAp2R : (g X1 X2 X2' : Term) -> Deriv (eqF X2 X2') ->
          Deriv (eqF (tmAp2 g X1 X2) (tmAp2 g X1 X2'))
cTmAp2R g X1 X2 X2' eq = cTmAp2 g X1 X1 X2 X2' (axRefl X1) eq

------------------------------------------------------------------------
-- SECTION 2.  Head-tag helpers for the b = srcF d2 of the Rcong else cases.

hdAp1 : (f X : Term) -> Deriv (eqF (ap1 Fst (tmAp1 f X)) (natCode 1))
hdAp1 f X = axFst tgAp1 (ap2 Pair f X)

funAp1 : (f X : Term) (mf : Nat) -> Deriv (eqF (ap1 Fst f) (natCode mf)) ->
         Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (tmAp1 f X)))) (natCode mf))
funAp1 f X mf hf =
  ruleTrans (cong1 Fst (ruleTrans (cong1 Fst (axSnd tgAp1 (ap2 Pair f X))) (axFst f X))) hf

hdAp2 : (g a b : Term) -> Deriv (eqF (ap1 Fst (tmAp2 g a b)) (natCode 2))
hdAp2 g a b = axFst tgAp2 (ap2 Pair g (ap2 Pair a b))

funAp2 : (g a b : Term) (mf : Nat) -> Deriv (eqF (ap1 Fst g) (natCode mf)) ->
         Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (tmAp2 g a b)))) (natCode mf))
funAp2 g a b mf hf =
  ruleTrans (cong1 Fst (ruleTrans (cong1 Fst (axSnd tgAp2 (ap2 Pair g (ap2 Pair a b))))
                                  (axFst g (ap2 Pair a b)))) hf

------------------------------------------------------------------------
-- SECTION 3.  The Rcong-else shared steps.

recElseSrc : (gM : Fun1M) (h1M h2M : Fun2M) (d1 d2 : DerM) ->
  Deriv (eqF (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))) ->
  Deriv (eqF (ap1 srcF (codeDer (triMeta d2))) (ap1 tgtF (codeDer d2))) ->
  Deriv (eqF (ap1 srcF (ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                              (codeDer (triMeta d1)) (codeDer (triMeta d2))))
             (ap1 tgtF (ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                              (codeDer d1) (codeDer d2))))
recElseSrc gM h1M h2M d1 d2 IH1 IH2 =
  ruleTrans (srcF_ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
              (codeDer (triMeta d1)) (codeDer (triMeta d2)))
    (ruleTrans (cTmAp2 (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                 (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))
                 (ap1 srcF (codeDer (triMeta d2))) (ap1 tgtF (codeDer d2)) IH1 IH2)
               (ruleSym (tgtF_ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                          (codeDer d1) (codeDer d2))))

recElseTgt : (gM : Fun1M) (h1M h2M : Fun2M) (d1 d2 : DerM) (mb mf : Nat) ->
  Deriv (eqF (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))) -> -- unused placeholder
  Deriv (eqF (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1)))) ->
  Deriv (eqF (ap1 tgtF (codeDer (triMeta d2))) (ap1 devF (ap1 srcF (codeDer d2)))) ->
  Deriv (eqF (ap1 Fst (ap1 srcF (codeDer d2))) (natCode mb)) -> ((Eq mb 0) -> Empty) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd (ap1 srcF (codeDer d2))))) (natCode mf)) -> ((Eq mf 3) -> Empty) ->
  Deriv (eqF (ap1 tgtF (ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                             (codeDer (triMeta d1)) (codeDer (triMeta d2))))
             (ap1 devF (ap1 srcF (ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                                       (codeDer d1) (codeDer d2)))))
recElseTgt gM h1M h2M d1 d2 mb mf _ IH1 IH2 hb mb0 hbf mf3 =
  ruleTrans (tgtF_ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
              (codeDer (triMeta d1)) (codeDer (triMeta d2)))
    (ruleTrans (cTmAp2 (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                 (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1)))
                 (ap1 tgtF (codeDer (triMeta d2))) (ap1 devF (ap1 srcF (codeDer d2))) IH1 IH2)
               (ruleSym (ruleTrans (cong1 devF (srcF_ap2c (cRec (codeF1 gM) (codeF2 h1M) (codeF2 h2M))
                                                  (codeDer d1) (codeDer d2)))
                          (devF_R_cong (codeF1 gM) (codeF2 h1M) (codeF2 h2M)
                            (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2)) mb mf hb mb0 hbf mf3))))

------------------------------------------------------------------------
-- SECTION 4.  src_triM : srcF (codeDer (triMeta d)) = tgtF (codeDer d) .

src_triM : (d : DerM) -> Deriv (eqF (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)))
src_triM mRefl = ruleTrans srcF_reflO (ruleSym tgtF_reflO)
src_triM (mAp1c f1S d) =
  ruleTrans (srcF_ap1c cSuc (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 cSuc (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d))
               (ruleSym (tgtF_ap1c cSuc (codeDer d))))
src_triM (mAp1c f1Zero d) =
  ruleTrans (srcF_rO (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 cZero (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d))
               (ruleSym (tgtF_ap1c cZero (codeDer d))))
src_triM (mAp1c f1Id d) =
  ruleTrans (srcF_rU (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 cId (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d))
               (ruleSym (tgtF_ap1c cId (codeDer d))))
src_triM (mAp1c (f1Comp g h1 h2) d) =
  ruleTrans (srcF_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 (cComp (codeF2 g) (codeF1 h1) (codeF1 h2))
                 (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d))
               (ruleSym (tgtF_ap1c (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (codeDer d))))
src_triM (mAp2c f2Proj d1 d2) =
  ruleTrans (srcF_rV (codeDer (triMeta d1)) (codeDer (triMeta d2)))
    (ruleTrans (cTmAp2 cProj (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))
                 (ap1 srcF (codeDer (triMeta d2))) (ap1 tgtF (codeDer d2)) (src_triM d1) (src_triM d2))
               (ruleSym (tgtF_ap2c cProj (codeDer d1) (codeDer d2))))
src_triM (mAp2c (f2Rec g h1 h2) d1 mRefl) =
  ruleTrans (srcF_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer (triMeta d1)))
    (ruleTrans (cTmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
                 (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1)) tmO tmO (src_triM d1) (axRefl tmO))
               (ruleSym (ruleTrans (tgtF_ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer d1) (codeDer mRefl))
                          (cTmAp2R (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
                            (ap1 tgtF (codeDer d1)) (ap1 tgtF (codeDer mRefl)) tmO tgtF_reflO))))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1S e)) =
  ruleTrans (srcF_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta e)))
    (ruleTrans (cTmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
                 (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))
                 (tmAp1 cSuc (ap1 srcF (codeDer (triMeta e)))) (tmAp1 cSuc (ap1 tgtF (codeDer e)))
                 (src_triM d1)
                 (cTmAp1 cSuc (ap1 srcF (codeDer (triMeta e))) (ap1 tgtF (codeDer e)) (src_triM e)))
               (ruleSym (ruleTrans (tgtF_ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer d1) (codeDer (mAp1c f1S e)))
                          (cTmAp2R (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
                            (ap1 tgtF (codeDer d1)) (ap1 tgtF (codeDer (mAp1c f1S e)))
                            (tmAp1 cSuc (ap1 tgtF (codeDer e))) (tgtF_ap1c cSuc (codeDer e))))))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Zero e)) = recElseSrc g h1 h2 d1 (mAp1c f1Zero e) (src_triM d1) (src_triM (mAp1c f1Zero e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Id e)) = recElseSrc g h1 h2 d1 (mAp1c f1Id e) (src_triM d1) (src_triM (mAp1c f1Id e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c (f1Comp a b c) e)) = recElseSrc g h1 h2 d1 (mAp1c (f1Comp a b c) e) (src_triM d1) (src_triM (mAp1c (f1Comp a b c) e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mAp2c fm e1 e2)) = recElseSrc g h1 h2 d1 (mAp2c fm e1 e2) (src_triM d1) (src_triM (mAp2c fm e1 e2))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mO e)) = recElseSrc g h1 h2 d1 (mO e) (src_triM d1) (src_triM (mO e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mU e)) = recElseSrc g h1 h2 d1 (mU e) (src_triM d1) (src_triM (mU e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mV e1 e2)) = recElseSrc g h1 h2 d1 (mV e1 e2) (src_triM d1) (src_triM (mV e1 e2))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mC a b c e)) = recElseSrc g h1 h2 d1 (mC a b c e) (src_triM d1) (src_triM (mC a b c e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mRb a b c e)) = recElseSrc g h1 h2 d1 (mRb a b c e) (src_triM d1) (src_triM (mRb a b c e))
src_triM (mAp2c (f2Rec g h1 h2) d1 (mRs a b c e1 e2)) = recElseSrc g h1 h2 d1 (mRs a b c e1 e2) (src_triM d1) (src_triM (mRs a b c e1 e2))
src_triM (mO d)     = ruleTrans srcF_reflO (ruleSym (tgtF_rO (codeDer d)))
src_triM (mU d)     = ruleTrans (src_triM d) (ruleSym (tgtF_rU (codeDer d)))
src_triM (mV d1 d2) = ruleTrans (src_triM d2) (ruleSym (tgtF_rV (codeDer d1) (codeDer d2)))
src_triM (mC g h1 h2 d) =
  ruleTrans (srcF_ap2c (codeF2 g) (ap1c (codeF1 h1) (codeDer (triMeta d))) (ap1c (codeF1 h2) (codeDer (triMeta d))))
    (ruleTrans (cTmAp2 (codeF2 g)
                 (ap1 srcF (ap1c (codeF1 h1) (codeDer (triMeta d)))) (tmAp1 (codeF1 h1) (ap1 tgtF (codeDer d)))
                 (ap1 srcF (ap1c (codeF1 h2) (codeDer (triMeta d)))) (tmAp1 (codeF1 h2) (ap1 tgtF (codeDer d)))
                 (ruleTrans (srcF_ap1c (codeF1 h1) (codeDer (triMeta d)))
                   (cTmAp1 (codeF1 h1) (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d)))
                 (ruleTrans (srcF_ap1c (codeF1 h2) (codeDer (triMeta d)))
                   (cTmAp1 (codeF1 h2) (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d))))
               (ruleSym (tgtF_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d))))
src_triM (mRb g h1 h2 d) =
  ruleTrans (srcF_ap1c (codeF1 g) (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 (codeF1 g) (ap1 srcF (codeDer (triMeta d))) (ap1 tgtF (codeDer d)) (src_triM d))
               (ruleSym (tgtF_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d))))
src_triM (mRs g h1 h2 d1 d2) =
  ruleTrans (srcF_ap2c (codeF2 h1)
              (ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
              (ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2))))
    (ruleTrans (cTmAp2 (codeF2 h1)
                 (ap1 srcF (ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2))))
                 (tmAp2 (codeF2 h2) (ap1 tgtF (codeDer d1)) (ap1 tgtF (codeDer d2)))
                 (ap1 srcF (ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2))))
                 (tmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 tgtF (codeDer d1)) (ap1 tgtF (codeDer d2)))
                 (ruleTrans (srcF_ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
                   (cTmAp2 (codeF2 h2) (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))
                     (ap1 srcF (codeDer (triMeta d2))) (ap1 tgtF (codeDer d2)) (src_triM d1) (src_triM d2)))
                 (ruleTrans (srcF_ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
                   (cTmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 srcF (codeDer (triMeta d1))) (ap1 tgtF (codeDer d1))
                     (ap1 srcF (codeDer (triMeta d2))) (ap1 tgtF (codeDer d2)) (src_triM d1) (src_triM d2))))
               (ruleSym (tgtF_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2))))

src_tri : (d : DerM) -> Deriv (eqF (ap1 srcF (ap1 triF (codeDer d))) (ap1 tgtF (codeDer d)))
src_tri d = ruleTrans (cong1 srcF (triShadowU d)) (src_triM d)

------------------------------------------------------------------------
-- SECTION 5.  head-fact builders for the Rcong-else tgt cases.

mkHb1 : (S f X : Term) -> Deriv (eqF S (tmAp1 f X)) -> Deriv (eqF (ap1 Fst S) (natCode 1))
mkHb1 S f X srcEq = ruleTrans (cong1 Fst srcEq) (hdAp1 f X)
mkHbf1 : (S f X : Term) (mf : Nat) -> Deriv (eqF S (tmAp1 f X)) -> Deriv (eqF (ap1 Fst f) (natCode mf)) ->
         Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd S))) (natCode mf))
mkHbf1 S f X mf srcEq hf = ruleTrans (cong1 Fst (cong1 Fst (cong1 Snd srcEq))) (funAp1 f X mf hf)
mkHb2 : (S g a b : Term) -> Deriv (eqF S (tmAp2 g a b)) -> Deriv (eqF (ap1 Fst S) (natCode 2))
mkHb2 S g a b srcEq = ruleTrans (cong1 Fst srcEq) (hdAp2 g a b)
mkHbf2 : (S g a b : Term) (mf : Nat) -> Deriv (eqF S (tmAp2 g a b)) -> Deriv (eqF (ap1 Fst g) (natCode mf)) ->
         Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd S))) (natCode mf))
mkHbf2 S g a b mf srcEq hf = ruleTrans (cong1 Fst (cong1 Fst (cong1 Snd srcEq))) (funAp2 g a b mf hf)

------------------------------------------------------------------------
-- SECTION 6.  tgt_triM : tgtF (codeDer (triMeta d)) = devF (srcF (codeDer d)) .

tgt_triM : (d : DerM) -> Deriv (eqF (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))))
tgt_triM mRefl = ruleTrans tgtF_reflO (ruleSym (ruleTrans (cong1 devF srcF_reflO) devF_tmO))
tgt_triM (mAp1c f1S d) =
  ruleTrans (tgtF_ap1c cSuc (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 cSuc (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))) (tgt_triM d))
               (ruleSym (ruleTrans (cong1 devF (srcF_ap1c cSuc (codeDer d))) (devF_ap1_s (ap1 srcF (codeDer d))))))
tgt_triM (mAp1c f1Zero d) =
  ruleTrans (tgtF_rO (codeDer (triMeta d)))
    (ruleSym (ruleTrans (cong1 devF (srcF_ap1c cZero (codeDer d))) (devF_o (ap1 srcF (codeDer d)))))
tgt_triM (mAp1c f1Id d) =
  ruleTrans (tgtF_rU (codeDer (triMeta d)))
    (ruleTrans (tgt_triM d)
               (ruleSym (ruleTrans (cong1 devF (srcF_ap1c cId (codeDer d))) (devF_u (ap1 srcF (codeDer d))))))
tgt_triM (mAp1c (f1Comp g h1 h2) d) =
  ruleTrans (tgtF_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer (triMeta d)))
    (ruleTrans (cTmAp2 (codeF2 g)
                 (tmAp1 (codeF1 h1) (ap1 tgtF (codeDer (triMeta d)))) (tmAp1 (codeF1 h1) (ap1 devF (ap1 srcF (codeDer d))))
                 (tmAp1 (codeF1 h2) (ap1 tgtF (codeDer (triMeta d)))) (tmAp1 (codeF1 h2) (ap1 devF (ap1 srcF (codeDer d))))
                 (cTmAp1 (codeF1 h1) (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))) (tgt_triM d))
                 (cTmAp1 (codeF1 h2) (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))) (tgt_triM d)))
               (ruleSym (ruleTrans (cong1 devF (srcF_ap1c (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (codeDer d)))
                          (devF_C (codeF2 g) (codeF1 h1) (codeF1 h2) (ap1 srcF (codeDer d))))))
tgt_triM (mAp2c f2Proj d1 d2) =
  ruleTrans (tgtF_rV (codeDer (triMeta d1)) (codeDer (triMeta d2)))
    (ruleTrans (tgt_triM d2)
               (ruleSym (ruleTrans (cong1 devF (srcF_ap2c cProj (codeDer d1) (codeDer d2)))
                          (devF_v (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2))))))
tgt_triM (mAp2c (f2Rec g h1 h2) d1 mRefl) =
  ruleTrans (tgtF_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer (triMeta d1)))
    (ruleTrans (cTmAp1 (codeF1 g) (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1))) (tgt_triM d1))
               (ruleSym (ruleTrans (cong1 devF (srcF_ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer d1) (codeDer mRefl)))
                          (ruleTrans (cong1 devF (cTmAp2R (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
                                                   (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer mRefl)) tmO srcF_reflO))
                                     (devF_Rb (codeF1 g) (codeF2 h1) (codeF2 h2) (ap1 srcF (codeDer d1)))))))
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1S e)) =
  ruleTrans (tgtF_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta e)))
    (ruleTrans (cTmAp2 (codeF2 h1)
                 (tmAp2 (codeF2 h2) (ap1 tgtF (codeDer (triMeta d1))) (ap1 tgtF (codeDer (triMeta e))))
                 (tmAp2 (codeF2 h2) (ap1 devF (ap1 srcF (codeDer d1))) (ap1 devF (ap1 srcF (codeDer e))))
                 (tmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 tgtF (codeDer (triMeta d1))) (ap1 tgtF (codeDer (triMeta e))))
                 (tmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 devF (ap1 srcF (codeDer d1))) (ap1 devF (ap1 srcF (codeDer e))))
                 (cTmAp2 (codeF2 h2) (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1)))
                   (ap1 tgtF (codeDer (triMeta e))) (ap1 devF (ap1 srcF (codeDer e))) (tgt_triM d1) (tgt_triM e))
                 (cTmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1)))
                   (ap1 tgtF (codeDer (triMeta e))) (ap1 devF (ap1 srcF (codeDer e))) (tgt_triM d1) (tgt_triM e)))
               (ruleSym (ruleTrans (cong1 devF (srcF_ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer d1) (codeDer (mAp1c f1S e))))
                          (ruleTrans (cong1 devF (cTmAp2R (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
                                                   (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer (mAp1c f1S e)))
                                                   (tmAp1 cSuc (ap1 srcF (codeDer e))) (srcF_ap1c cSuc (codeDer e))))
                                     (devF_Rs (codeF1 g) (codeF2 h1) (codeF2 h2) (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer e)))))))
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Zero e)) =
  recElseTgt g h1 h2 d1 (mAp1c f1Zero e) 1 4 (src_triM d1) (tgt_triM d1) (tgt_triM (mAp1c f1Zero e))
    (mkHb1 (ap1 srcF (codeDer (mAp1c f1Zero e))) cZero (ap1 srcF (codeDer e)) (srcF_ap1c cZero (codeDer e))) (\ ())
    (mkHbf1 (ap1 srcF (codeDer (mAp1c f1Zero e))) cZero (ap1 srcF (codeDer e)) 4 (srcF_ap1c cZero (codeDer e)) (axFst tgZero O)) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Id e)) =
  recElseTgt g h1 h2 d1 (mAp1c f1Id e) 1 5 (src_triM d1) (tgt_triM d1) (tgt_triM (mAp1c f1Id e))
    (mkHb1 (ap1 srcF (codeDer (mAp1c f1Id e))) cId (ap1 srcF (codeDer e)) (srcF_ap1c cId (codeDer e))) (\ ())
    (mkHbf1 (ap1 srcF (codeDer (mAp1c f1Id e))) cId (ap1 srcF (codeDer e)) 5 (srcF_ap1c cId (codeDer e)) (axFst tgId O)) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mAp1c (f1Comp a b c) e)) =
  recElseTgt g h1 h2 d1 (mAp1c (f1Comp a b c) e) 1 6 (src_triM d1) (tgt_triM d1) (tgt_triM (mAp1c (f1Comp a b c) e))
    (mkHb1 (ap1 srcF (codeDer (mAp1c (f1Comp a b c) e))) (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (ap1 srcF (codeDer e))
       (srcF_ap1c (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (codeDer e))) (\ ())
    (mkHbf1 (ap1 srcF (codeDer (mAp1c (f1Comp a b c) e))) (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (ap1 srcF (codeDer e)) 6
       (srcF_ap1c (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (codeDer e))
       (axFst tgComp (ap2 Pair (codeF2 a) (ap2 Pair (codeF1 b) (codeF1 c))))) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mAp2c f2Proj e1 e2)) =
  recElseTgt g h1 h2 d1 (mAp2c f2Proj e1 e2) 2 7 (src_triM d1) (tgt_triM d1) (tgt_triM (mAp2c f2Proj e1 e2))
    (mkHb2 (ap1 srcF (codeDer (mAp2c f2Proj e1 e2))) cProj (ap1 srcF (codeDer e1)) (ap1 srcF (codeDer e2))
       (srcF_ap2c cProj (codeDer e1) (codeDer e2))) (\ ())
    (mkHbf2 (ap1 srcF (codeDer (mAp2c f2Proj e1 e2))) cProj (ap1 srcF (codeDer e1)) (ap1 srcF (codeDer e2)) 7
       (srcF_ap2c cProj (codeDer e1) (codeDer e2)) (axFst tgProj O)) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mAp2c (f2Rec a b c) e1 e2)) =
  recElseTgt g h1 h2 d1 (mAp2c (f2Rec a b c) e1 e2) 2 8 (src_triM d1) (tgt_triM d1) (tgt_triM (mAp2c (f2Rec a b c) e1 e2))
    (mkHb2 (ap1 srcF (codeDer (mAp2c (f2Rec a b c) e1 e2))) (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (ap1 srcF (codeDer e1)) (ap1 srcF (codeDer e2))
       (srcF_ap2c (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (codeDer e1) (codeDer e2))) (\ ())
    (mkHbf2 (ap1 srcF (codeDer (mAp2c (f2Rec a b c) e1 e2))) (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (ap1 srcF (codeDer e1)) (ap1 srcF (codeDer e2)) 8
       (srcF_ap2c (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (codeDer e1) (codeDer e2))
       (axFst tgRec (ap2 Pair (codeF1 a) (ap2 Pair (codeF2 b) (codeF2 c))))) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mO e)) =
  recElseTgt g h1 h2 d1 (mO e) 1 4 (src_triM d1) (tgt_triM d1) (tgt_triM (mO e))
    (mkHb1 (ap1 srcF (codeDer (mO e))) cZero (ap1 srcF (codeDer e)) (srcF_rO (codeDer e))) (\ ())
    (mkHbf1 (ap1 srcF (codeDer (mO e))) cZero (ap1 srcF (codeDer e)) 4 (srcF_rO (codeDer e)) (axFst tgZero O)) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mU e)) =
  recElseTgt g h1 h2 d1 (mU e) 1 5 (src_triM d1) (tgt_triM d1) (tgt_triM (mU e))
    (mkHb1 (ap1 srcF (codeDer (mU e))) cId (ap1 srcF (codeDer e)) (srcF_rU (codeDer e))) (\ ())
    (mkHbf1 (ap1 srcF (codeDer (mU e))) cId (ap1 srcF (codeDer e)) 5 (srcF_rU (codeDer e)) (axFst tgId O)) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mV e1 e2)) =
  recElseTgt g h1 h2 d1 (mV e1 e2) 2 7 (src_triM d1) (tgt_triM d1) (tgt_triM (mV e1 e2))
    (mkHb2 (ap1 srcF (codeDer (mV e1 e2))) cProj (ap1 srcF (codeDer e1)) (ap1 srcF (codeDer e2)) (srcF_rV (codeDer e1) (codeDer e2))) (\ ())
    (mkHbf2 (ap1 srcF (codeDer (mV e1 e2))) cProj (ap1 srcF (codeDer e1)) (ap1 srcF (codeDer e2)) 7 (srcF_rV (codeDer e1) (codeDer e2)) (axFst tgProj O)) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mC a b c e)) =
  recElseTgt g h1 h2 d1 (mC a b c e) 1 6 (src_triM d1) (tgt_triM d1) (tgt_triM (mC a b c e))
    (mkHb1 (ap1 srcF (codeDer (mC a b c e))) (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (ap1 srcF (codeDer e))
       (srcF_rC (codeF2 a) (codeF1 b) (codeF1 c) (codeDer e))) (\ ())
    (mkHbf1 (ap1 srcF (codeDer (mC a b c e))) (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (ap1 srcF (codeDer e)) 6
       (srcF_rC (codeF2 a) (codeF1 b) (codeF1 c) (codeDer e))
       (axFst tgComp (ap2 Pair (codeF2 a) (ap2 Pair (codeF1 b) (codeF1 c))))) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mRb a b c e)) =
  recElseTgt g h1 h2 d1 (mRb a b c e) 2 8 (src_triM d1) (tgt_triM d1) (tgt_triM (mRb a b c e))
    (mkHb2 (ap1 srcF (codeDer (mRb a b c e))) (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (ap1 srcF (codeDer e)) tmO
       (srcF_rRb (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e))) (\ ())
    (mkHbf2 (ap1 srcF (codeDer (mRb a b c e))) (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (ap1 srcF (codeDer e)) tmO 8
       (srcF_rRb (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e))
       (axFst tgRec (ap2 Pair (codeF1 a) (ap2 Pair (codeF2 b) (codeF2 c))))) (\ ())
tgt_triM (mAp2c (f2Rec g h1 h2) d1 (mRs a b c e1 e2)) =
  recElseTgt g h1 h2 d1 (mRs a b c e1 e2) 2 8 (src_triM d1) (tgt_triM d1) (tgt_triM (mRs a b c e1 e2))
    (mkHb2 (ap1 srcF (codeDer (mRs a b c e1 e2))) (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (ap1 srcF (codeDer e1)) (tmAp1 cSuc (ap1 srcF (codeDer e2)))
       (srcF_rRs (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e1) (codeDer e2))) (\ ())
    (mkHbf2 (ap1 srcF (codeDer (mRs a b c e1 e2))) (cRec (codeF1 a) (codeF2 b) (codeF2 c)) (ap1 srcF (codeDer e1)) (tmAp1 cSuc (ap1 srcF (codeDer e2))) 8
       (srcF_rRs (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e1) (codeDer e2))
       (axFst tgRec (ap2 Pair (codeF1 a) (ap2 Pair (codeF2 b) (codeF2 c))))) (\ ())
tgt_triM (mO d) =
  ruleTrans tgtF_reflO (ruleSym (ruleTrans (cong1 devF (srcF_rO (codeDer d))) (devF_o (ap1 srcF (codeDer d)))))
tgt_triM (mU d) =
  ruleTrans (tgt_triM d) (ruleSym (ruleTrans (cong1 devF (srcF_rU (codeDer d))) (devF_u (ap1 srcF (codeDer d)))))
tgt_triM (mV d1 d2) =
  ruleTrans (tgt_triM d2) (ruleSym (ruleTrans (cong1 devF (srcF_rV (codeDer d1) (codeDer d2)))
                                     (devF_v (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2)))))
tgt_triM (mC g h1 h2 d) =
  ruleTrans (tgtF_ap2c (codeF2 g) (ap1c (codeF1 h1) (codeDer (triMeta d))) (ap1c (codeF1 h2) (codeDer (triMeta d))))
    (ruleTrans (cTmAp2 (codeF2 g)
                 (ap1 tgtF (ap1c (codeF1 h1) (codeDer (triMeta d)))) (tmAp1 (codeF1 h1) (ap1 devF (ap1 srcF (codeDer d))))
                 (ap1 tgtF (ap1c (codeF1 h2) (codeDer (triMeta d)))) (tmAp1 (codeF1 h2) (ap1 devF (ap1 srcF (codeDer d))))
                 (ruleTrans (tgtF_ap1c (codeF1 h1) (codeDer (triMeta d)))
                   (cTmAp1 (codeF1 h1) (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))) (tgt_triM d)))
                 (ruleTrans (tgtF_ap1c (codeF1 h2) (codeDer (triMeta d)))
                   (cTmAp1 (codeF1 h2) (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))) (tgt_triM d))))
               (ruleSym (ruleTrans (cong1 devF (srcF_rC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d)))
                          (devF_C (codeF2 g) (codeF1 h1) (codeF1 h2) (ap1 srcF (codeDer d))))))
tgt_triM (mRb g h1 h2 d) =
  ruleTrans (tgtF_ap1c (codeF1 g) (codeDer (triMeta d)))
    (ruleTrans (cTmAp1 (codeF1 g) (ap1 tgtF (codeDer (triMeta d))) (ap1 devF (ap1 srcF (codeDer d))) (tgt_triM d))
               (ruleSym (ruleTrans (cong1 devF (srcF_rRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d)))
                          (devF_Rb (codeF1 g) (codeF2 h1) (codeF2 h2) (ap1 srcF (codeDer d))))))
tgt_triM (mRs g h1 h2 d1 d2) =
  ruleTrans (tgtF_ap2c (codeF2 h1)
              (ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
              (ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2))))
    (ruleTrans (cTmAp2 (codeF2 h1)
                 (ap1 tgtF (ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2))))
                 (tmAp2 (codeF2 h2) (ap1 devF (ap1 srcF (codeDer d1))) (ap1 devF (ap1 srcF (codeDer d2))))
                 (ap1 tgtF (ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2))))
                 (tmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 devF (ap1 srcF (codeDer d1))) (ap1 devF (ap1 srcF (codeDer d2))))
                 (ruleTrans (tgtF_ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
                   (cTmAp2 (codeF2 h2) (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1)))
                     (ap1 tgtF (codeDer (triMeta d2))) (ap1 devF (ap1 srcF (codeDer d2))) (tgt_triM d1) (tgt_triM d2)))
                 (ruleTrans (tgtF_ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
                   (cTmAp2 (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 tgtF (codeDer (triMeta d1))) (ap1 devF (ap1 srcF (codeDer d1)))
                     (ap1 tgtF (codeDer (triMeta d2))) (ap1 devF (ap1 srcF (codeDer d2))) (tgt_triM d1) (tgt_triM d2))))
               (ruleSym (ruleTrans (cong1 devF (srcF_rRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2)))
                          (devF_Rs (codeF1 g) (codeF2 h1) (codeF2 h2) (ap1 srcF (codeDer d1)) (ap1 srcF (codeDer d2))))))

tgt_tri : (d : DerM) -> Deriv (eqF (ap1 tgtF (ap1 triF (codeDer d))) (ap1 devF (ap1 srcF (codeDer d))))
tgt_tri d = ruleTrans (cong1 tgtF (triShadowU d)) (tgt_triM d)
