{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CRGlueImpU -- object-imp versions of the conj3 child extractors and the
-- eqDecO reflection, for the bundled CR dispatch glue.
--
--   eqDecO_complete_imp : imp (a = b) (eqDecO a b = O)
--   eqDecO_sound_imp    : imp (eqDecO a b = O) (a = b)
--   childV_imp c : imp (conj3 c = O) (wfRed (triF c) = O)
--   childS_imp c : imp (conj3 c = O) (srcF (triF c) = tgtF c)
--   childT_imp c : imp (conj3 c = O) (tgtF (triF c) = devF (srcF c))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CRGlueImpU where

open import T4.Base
open import T4.Code using ( falseF )

open import T4.QCheckU using ( conj3 )
open import T4.EqDecO  using ( eqDecO )
open import T4.CRGlueU using ( conj3_unfold )
open import T4.WfRed   using ( wfRed )
open import T4.DerTri  using ( triF )
open import T4.DerSrc  using ( srcF )
open import T4.DerTgt  using ( tgtF )
open import T4.DerDev  using ( devF )
open import T4.SigmaZeroN using ( sigmaZeroL ; sigmaZeroR )

open import T4.NatEqReflect using ( natEqF_complete )
open import T4.Counting using ( negToImpFalse ; impFalseToNeg_imp )
open import T4.CtxKit using ( lift2 ; get2a ; ap2c ; trans2c )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impCongL ; impCongR )

open import BRA3.Church       using ( pi ; sigma ; isZero ; TisZeroZ ; TisZeroSucc ; T33 )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.NatEqRefl using ( natEqF_self_univ )
open import BRA3.Logic         using ( eqSymImp ; prependEqLeft )
open import BRA3.Contrapositive using ( compI ; liftP ; identP ; DNE )
open import T4.ParEnds using ( pi_O_O )
open import BRA3.PairAlgebra using ( Pair ; axFst ; axSnd )
open import T4.AdDispatchAux using ( FstO ; SndO )

------------------------------------------------------------------------
-- eqDecO reflection, imp-form.

eqDecO_complete_imp : (a b : Term) -> Deriv (imp (eqF a b) (eqF (eqDecO a b) O))
eqDecO_complete_imp a b =
  let H : Formula
      H = eqF a b
      natSO : Deriv (imp H (eqF (ap2 natEqF a b) (ap1 s O)))
      natSO = impEqTrans (ap2 natEqF a b) (ap2 natEqF b b) (ap1 s O)
                (impCongL natEqF a b b (identP H)) (impLift (natEqF_self_univ b))
      izCong : Deriv (imp H (eqF (ap1 isZero (ap2 natEqF a b)) (ap1 isZero (ap1 s O))))
      izCong = impCong1 isZero (ap2 natEqF a b) (ap1 s O) natSO
  in impEqTrans (ap1 isZero (ap2 natEqF a b)) (ap1 isZero (ap1 s O)) O
       izCong (impLift (ruleInst 0 O TisZeroSucc))

eqDecO_sound_imp : (a b : Term) -> Deriv (imp (eqF (eqDecO a b) O) (eqF a b))
eqDecO_sound_imp a b =
  let w : Term
      w = ap2 natEqF a b
      H : Formula
      H = eqF (ap1 isZero w) O
      nq : Formula
      nq = neg (eqF a b)
      f_natO : Deriv (imp H (imp nq (eqF w O)))
      f_natO = liftP H (natEqF_complete a b)
      congImp : Deriv (imp (eqF w O) (eqF (ap1 isZero w) (ap1 isZero O)))
      congImp = impCong1 isZero w O (identP (eqF w O))
      f_cong : Deriv (imp H (imp nq (eqF (ap1 isZero w) (ap1 isZero O))))
      f_cong = ap2c (lift2 H nq congImp) f_natO
      f_isZsO : Deriv (imp H (imp nq (eqF (ap1 isZero w) (ap1 s O))))
      f_isZsO = trans2c (ap1 isZero w) (ap1 isZero O) (ap1 s O) f_cong (lift2 H nq TisZeroZ)
      f_isZO : Deriv (imp H (imp nq (eqF (ap1 isZero w) O)))
      f_isZO = get2a H nq
      f_symZsO : Deriv (imp H (imp nq (eqF (ap1 s O) (ap1 isZero w))))
      f_symZsO = ap2c (lift2 H nq (eqSymImp (ap1 isZero w) (ap1 s O))) f_isZsO
      f_sOO : Deriv (imp H (imp nq (eqF (ap1 s O) O)))
      f_sOO = trans2c (ap1 s O) (ap1 isZero w) O f_symZsO f_isZO
      f_false : Deriv (imp H (imp nq falseF))
      f_false = ap2c (lift2 H nq (negToImpFalse (eqF (ap1 s O) O) ax_succ_nonzero)) f_sOO
  in compI (compI f_false (impFalseToNeg_imp nq)) (DNE (eqF a b))

------------------------------------------------------------------------
-- Child extractors, imp-form.

private
  -- imp (conj3 c = O) (sigma .. = O) : rewrite the head.
  toSigma : (c : Term) ->
    Deriv (imp (eqF (ap1 conj3 c) O)
               (eqF (ap2 sigma (ap1 wfRed (ap1 triF c))
                       (ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                                  (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))) O))
  toSigma c =
    prependEqLeft (ap2 sigma (ap1 wfRed (ap1 triF c))
                    (ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                               (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))))
                  (ap1 conj3 c) O (ruleSym (conj3_unfold c))

childV_imp : (c : Term) -> Deriv (imp (eqF (ap1 conj3 c) O) (eqF (ap1 wfRed (ap1 triF c)) O))
childV_imp c =
  compI (toSigma c)
    (sigmaZeroL (ap1 wfRed (ap1 triF c))
       (ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                  (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))))

childS_imp : (c : Term) ->
  Deriv (imp (eqF (ap1 conj3 c) O) (eqF (ap1 srcF (ap1 triF c)) (ap1 tgtF c)))
childS_imp c =
  let inner = ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                        (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))
      toInner : Deriv (imp (eqF (ap1 conj3 c) O) (eqF inner O))
      toInner = compI (toSigma c) (sigmaZeroR (ap1 wfRed (ap1 triF c)) inner)
      toSO : Deriv (imp (eqF (ap1 conj3 c) O) (eqF (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c)) O))
      toSO = compI toInner (sigmaZeroL (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                              (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))
  in compI toSO (eqDecO_sound_imp (ap1 srcF (ap1 triF c)) (ap1 tgtF c))

childT_imp : (c : Term) ->
  Deriv (imp (eqF (ap1 conj3 c) O) (eqF (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))
childT_imp c =
  let inner = ap2 sigma (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                        (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))
      toInner : Deriv (imp (eqF (ap1 conj3 c) O) (eqF inner O))
      toInner = compI (toSigma c) (sigmaZeroR (ap1 wfRed (ap1 triF c)) inner)
      toTO : Deriv (imp (eqF (ap1 conj3 c) O)
                        (eqF (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))) O))
      toTO = compI toInner (sigmaZeroR (eqDecO (ap1 srcF (ap1 triF c)) (ap1 tgtF c))
                              (eqDecO (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c))))
  in compI toTO (eqDecO_sound_imp (ap1 tgtF (ap1 triF c)) (ap1 devF (ap1 srcF c)))

------------------------------------------------------------------------
-- sigma both-zero, imp-form (nested).

sigmaBothO_imp : (a b : Term) ->
  Deriv (imp (eqF a O) (imp (eqF b O) (eqF (ap2 sigma a b) O)))
sigmaBothO_imp a b =
  let Ha : Formula
      Ha = eqF a O
      Hb : Formula
      Hb = eqF b O
      cong_a : Deriv (imp Ha (eqF (ap2 sigma a b) (ap2 sigma O b)))
      cong_a = impCongL sigma a O b (identP Ha)
      cong_b : Deriv (imp Hb (eqF (ap2 sigma O b) (ap2 sigma O O)))
      cong_b = impCongR sigma b O O (identP Hb)
      d1 : Deriv (imp Ha (imp Hb (eqF (ap2 sigma a b) (ap2 sigma O b))))
      d1 = compI cong_a (axK (eqF (ap2 sigma a b) (ap2 sigma O b)) Hb)
      d2 : Deriv (imp Ha (imp Hb (eqF (ap2 sigma O b) (ap2 sigma O O))))
      d2 = liftP Ha cong_b
      d3 : Deriv (imp Ha (imp Hb (eqF (ap2 sigma O O) O)))
      d3 = lift2 Ha Hb (T33 O)
  in trans2c (ap2 sigma a b) (ap2 sigma O b) O d1
       (trans2c (ap2 sigma O b) (ap2 sigma O O) O d2 d3)

------------------------------------------------------------------------
-- pi both-zero, imp-form (for binary wfRed validity:  pi O O = O via pi_O_O).

piBothO_imp : (a b : Term) ->
  Deriv (imp (eqF a O) (imp (eqF b O) (eqF (ap2 pi a b) O)))
piBothO_imp a b =
  let Ha : Formula
      Ha = eqF a O
      Hb : Formula
      Hb = eqF b O
      cong_a : Deriv (imp Ha (eqF (ap2 pi a b) (ap2 pi O b)))
      cong_a = impCongL pi a O b (identP Ha)
      cong_b : Deriv (imp Hb (eqF (ap2 pi O b) (ap2 pi O O)))
      cong_b = impCongR pi b O O (identP Hb)
      d1 : Deriv (imp Ha (imp Hb (eqF (ap2 pi a b) (ap2 pi O b))))
      d1 = compI cong_a (axK (eqF (ap2 pi a b) (ap2 pi O b)) Hb)
      d2 : Deriv (imp Ha (imp Hb (eqF (ap2 pi O b) (ap2 pi O O))))
      d2 = liftP Ha cong_b
      d3 : Deriv (imp Ha (imp Hb (eqF (ap2 pi O O) O)))
      d3 = lift2 Ha Hb pi_O_O
  in trans2c (ap2 pi a b) (ap2 pi O b) O d1
       (trans2c (ap2 pi O b) (ap2 pi O O) O d2 d3)

------------------------------------------------------------------------
-- pi zero projections, imp-form ( pi a b = O  =>  a = O  /  b = O ).

piZeroL_imp : (a b : Term) -> Deriv (imp (eqF (ap2 pi a b) O) (eqF a O))
piZeroL_imp a b =
  let h : Formula
      h = eqF (ap2 pi a b) O
  in impEqTrans a (ap1 Fst (ap2 pi a b)) O
       (impLift (ruleSym (axFst a b)))
       (impEqTrans (ap1 Fst (ap2 pi a b)) (ap1 Fst O) O
         (impCong1 Fst (ap2 pi a b) O (identP h))
         (impLift FstO))

piZeroR_imp : (a b : Term) -> Deriv (imp (eqF (ap2 pi a b) O) (eqF b O))
piZeroR_imp a b =
  let h : Formula
      h = eqF (ap2 pi a b) O
  in impEqTrans b (ap1 Snd (ap2 pi a b)) O
       (impLift (ruleSym (axSnd a b)))
       (impEqTrans (ap1 Snd (ap2 pi a b)) (ap1 Snd O) O
         (impCong1 Snd (ap2 pi a b) O (identP h))
         (impLift SndO))
