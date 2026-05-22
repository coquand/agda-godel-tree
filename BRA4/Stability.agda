{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Stability -- universal-in-Term stability for the cov_spec table.
--
-- The BRA4 analog of BRA3.SubT.Stability.stabilityP_subT_at .
--
-- For sbt's cov walker:
--
--   HistP_sbt bF sF spec K  = Snd (Snd (cov_spec bF sF spec K))
--   HPsbt    bF sF spec t K = Fst (iter Snd (HistP_sbt ... K) (sub K t))
--
-- The stability theorem:
--
--   stabilityP_sbt_at :
--     (bF : Fun1) (sF : Fun2) (spec t K : Term) ->
--     Deriv (imp (leq t K)
--                 (eqF (HPsbt bF sF spec t K) (HPsbt bF sF spec t t)))
--
-- Universal in spec, t, K : Term -- no Closed premise, no natCode hypothesis.
-- Proof:
--   (1) stabilityP_sbt_single_sF : single fuel-sF preservation, using
--       HistP_sbt_succ_extend (from CoVSpecUniv) + lookup_preserves (from
--       BRA3.LookupAPI).
--   (2) stabilityP_sbt_v012 : full induction on var 0 = K with var 1 = t,
--       var 2 = spec, via ruleIndNat 0 .
--   (3) stabilityP_sbt_at : universal form by ruleInst2 + freshness.

module BRA4.Stability where

open import BRA4.Base
open import BRA4.CoVSpec
open import BRA4.CoVSpecUniv

open import BRA3.Church           using ( pi ; sub )
open import BRA3.ChurchT117       using ( Fst )
open import BRA3.ChurchT116       using ( Snd )
open import BRA3.ChurchLeq        using ( leq ; T76 )
open import BRA3.ChurchT82        using ( T82 )
open import BRA3.ChurchSubSucc    using ( T_sub_O )
open import BRA3.ChurchStrictTrich using ( caseElimUnderTwo )
open import BRA3.CourseOfValues   using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; iter_base_univ )
open import BRA3.LookupAPI        using ( lookup_preserves )
open import BRA3.Logic            using
  ( prependEqLeft ; impTrans ; eqSymImp )
open import BRA3.Contrapositive   using ( bComb ; bCombTwo ; identP ; liftP )
import BRA3.RuleInst2
open BRA3.RuleInst2 using
  ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans
  ; maxN ; maxN-le-left ; maxN-le-right
  ; maxVarT ; substT_above_max ; ruleInst2 ; natEq-refl )

------------------------------------------------------------------------
-- HPsbt : the lookup-via-HistP_sbt helper.
--
--   HPsbt bF sF spec t K
--     = Fst (iter Snd (HistP_sbt bF sF spec K) (sub K t))

HPsbt : Fun1 -> Fun2 -> Term -> Term -> Term -> Term
HPsbt bF sF spec t K =
  ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec K) (ap2 sub K t))

------------------------------------------------------------------------
-- Under-hypothesis combinators.  Local copies; same pattern as
-- BRA3.SubT.Stability.

trans_under :
  {P : Formula} {a b c : Term} ->
  Deriv (imp P (eqF a b)) ->
  Deriv (imp P (eqF b c)) ->
  Deriv (imp P (eqF a c))
trans_under {P}{a}{b}{c} AB BC =
  let symAB : Deriv (imp P (eqF b a))
      symAB = impTrans AB (eqSymImp a b)
      l1 : Deriv (imp P (imp (eqF b a) (imp (eqF b c) (eqF a c))))
      l1 = liftP P (ax_eqTrans b a c)
      l2 : Deriv (imp P (imp (eqF b c) (eqF a c)))
      l2 = bComb l1 symAB
  in bComb l2 BC

trans_under2 :
  {P1 P2 : Formula} {a b c : Term} ->
  Deriv (imp P1 (imp P2 (eqF a b))) ->
  Deriv (imp P1 (imp P2 (eqF b c))) ->
  Deriv (imp P1 (imp P2 (eqF a c)))
trans_under2 {P1}{P2}{a}{b}{c} AB BC =
  let sym_lift : Deriv (imp P1 (imp P2 (imp (eqF a b) (eqF b a))))
      sym_lift = liftP P1 (liftP P2 (eqSymImp a b))
      symAB : Deriv (imp P1 (imp P2 (eqF b a)))
      symAB = bCombTwo sym_lift AB
      l1 : Deriv (imp P1 (imp P2 (imp (eqF b a) (imp (eqF b c) (eqF a c)))))
      l1 = liftP P1 (liftP P2 (ax_eqTrans b a c))
      l2 : Deriv (imp P1 (imp P2 (imp (eqF b c) (eqF a c))))
      l2 = bCombTwo l1 symAB
  in bCombTwo l2 BC

insertHyp1 :
  {P1 Pnew Q : Formula} ->
  Deriv (imp P1 Q) ->
  Deriv (imp P1 (imp Pnew Q))
insertHyp1 {P1}{Pnew}{Q} D = bComb (liftP P1 (axK Q Pnew)) D

congR_under :
  {P : Formula} (g : Fun2) (x : Term) {a b : Term} ->
  Deriv (imp P (eqF a b)) ->
  Deriv (imp P (eqF (ap2 g x a) (ap2 g x b)))
congR_under {P} g x {a}{b} pAB = impTrans pAB (ax_eqCongR g a b x)

congL_under :
  {P : Formula} (g : Fun2) (x : Term) {a b : Term} ->
  Deriv (imp P (eqF a b)) ->
  Deriv (imp P (eqF (ap2 g a x) (ap2 g b x)))
congL_under {P} g x {a}{b} pAB = impTrans pAB (ax_eqCongL g a b x)

cong1_under :
  {P : Formula} (f : Fun1) {a b : Term} ->
  Deriv (imp P (eqF a b)) ->
  Deriv (imp P (eqF (ap1 f a) (ap1 f b)))
cong1_under {P} f {a}{b} pAB = impTrans pAB (ax_eqCong1 f a b)

------------------------------------------------------------------------
-- Single fuel-sF stability.  Universal in spec, K, t.
--
--   leq t K  ==>  HPsbt bF sF spec t (s K) = HPsbt bF sF spec t K
--
-- Proof: rewrite HistP_sbt at (s K) via HistP_sbt_succ_extend; then apply
-- lookup_preserves (universal-in-H).

stabilityP_sbt_single_sF :
  (bF : Fun1) (sF : Fun2) (spec K t : Term) ->
  Deriv (imp (leq t K)
              (eqF (HPsbt bF sF spec t (ap1 s K))
                    (HPsbt bF sF spec t K)))
stabilityP_sbt_single_sF bF sF spec K t =
  let newVal : Term
      newVal = newVal_at bF sF spec K

      H_eq : Deriv (eqF (HistP_sbt bF sF spec (ap1 s K))
                          (ap2 pi newVal (HistP_sbt bF sF spec K)))
      H_eq = HistP_sbt_succ_extend bF sF spec K

      iter_eq :
        Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF spec (ap1 s K))
                                     (ap2 sub (ap1 s K) t))
                    (ap2 (iter Snd) (ap2 pi newVal (HistP_sbt bF sF spec K))
                                     (ap2 sub (ap1 s K) t)))
      iter_eq = congL (iter Snd) (ap2 sub (ap1 s K) t) H_eq

      fst_eq :
        Deriv (eqF (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec (ap1 s K))
                                             (ap2 sub (ap1 s K) t)))
                    (ap1 Fst (ap2 (iter Snd) (ap2 pi newVal (HistP_sbt bF sF spec K))
                                             (ap2 sub (ap1 s K) t))))
      fst_eq = cong1 Fst iter_eq

      preserves :
        Deriv (imp (leq t K)
                    (eqF (ap1 Fst (ap2 (iter Snd) (ap2 pi newVal (HistP_sbt bF sF spec K))
                                                     (ap2 sub (ap1 s K) t)))
                          (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec K)
                                                     (ap2 sub K t)))))
      preserves = lookup_preserves (HistP_sbt bF sF spec K) newVal K t

      transport :
        Deriv (imp (eqF (ap1 Fst (ap2 (iter Snd) (ap2 pi newVal (HistP_sbt bF sF spec K))
                                                    (ap2 sub (ap1 s K) t)))
                         (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec K)
                                                    (ap2 sub K t))))
                    (eqF (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec (ap1 s K))
                                                    (ap2 sub (ap1 s K) t)))
                         (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec K)
                                                    (ap2 sub K t)))))
      transport = prependEqLeft
                    (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec (ap1 s K))
                                               (ap2 sub (ap1 s K) t)))
                    (ap1 Fst (ap2 (iter Snd) (ap2 pi newVal (HistP_sbt bF sF spec K))
                                               (ap2 sub (ap1 s K) t)))
                    (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF spec K) (ap2 sub K t)))
                    fst_eq

  in impTrans preserves transport

------------------------------------------------------------------------
-- stabilityP_sbt_v012 : full universal stability with var 0 = K, var 1 = t,
-- var 2 = spec.  Proof structurally identical to BRA3.SubT.Stability.
-- stabilityP_subT_v012.

stabilityP_sbt_v012 :
  (bF : Fun1) (sF : Fun2) ->
  Deriv (imp (leq (var (suc zero)) (var zero))
              (eqF (HPsbt bF sF (var (suc (suc zero))) (var (suc zero)) (var zero))
                    (HPsbt bF sF (var (suc (suc zero))) (var (suc zero)) (var (suc zero)))))
stabilityP_sbt_v012 bF sF = ruleIndNat 0 {P = Pform} bFCase sFImp
  where
    specT : Term
    specT = var (suc (suc zero))

    tT : Term
    tT = var (suc zero)

    KT : Term
    KT = var zero

    Pform : Formula
    Pform = imp (leq tT KT)
                 (eqF (HPsbt bF sF specT tT KT)
                      (HPsbt bF sF specT tT tT))

    ----------------------------------------------------------------
    -- Base case at  var 0 := O .

    Hyp_bF : Formula
    Hyp_bF = leq tT O

    LHS_bF : Term
    LHS_bF = HPsbt bF sF specT tT O

    RHS_bF : Term
    RHS_bF = HPsbt bF sF specT tT tT

    -- Unconditional:  HPsbt ... O = Fst (HistP_sbt ... O).
    L_to_FstHistO : Deriv (eqF LHS_bF (ap1 Fst (HistP_sbt bF sF specT O)))
    L_to_FstHistO =
      let subOv1 : Deriv (eqF (ap2 sub O tT) O)
          subOv1 = ruleInst 0 tT T76

          inner1 :
            Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT O) (ap2 sub O tT))
                        (ap2 (iter Snd) (HistP_sbt bF sF specT O) O))
          inner1 = congR (iter Snd) (HistP_sbt bF sF specT O) subOv1

          inner2 : Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT O) O)
                                (HistP_sbt bF sF specT O))
          inner2 = iter_base_univ Snd (HistP_sbt bF sF specT O)

          combined :
            Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT O) (ap2 sub O tT))
                        (HistP_sbt bF sF specT O))
          combined = ruleTrans inner1 inner2
      in cong1 Fst combined

    R_to_FstHistT : Deriv (eqF RHS_bF (ap1 Fst (HistP_sbt bF sF specT tT)))
    R_to_FstHistT =
      let subTT : Deriv (eqF (ap2 sub tT tT) O)
          subTT = sub_self tT

          inner1 :
            Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT tT) (ap2 sub tT tT))
                        (ap2 (iter Snd) (HistP_sbt bF sF specT tT) O))
          inner1 = congR (iter Snd) (HistP_sbt bF sF specT tT) subTT

          inner2 :
            Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT tT) O)
                        (HistP_sbt bF sF specT tT))
          inner2 = iter_base_univ Snd (HistP_sbt bF sF specT tT)

          combined :
            Deriv (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT tT) (ap2 sub tT tT))
                        (HistP_sbt bF sF specT tT))
          combined = ruleTrans inner1 inner2
      in cong1 Fst combined

    -- Under Hyp_bF: var 1 (= t) = O.
    t_eq_O : Deriv (imp Hyp_bF (eqF tT O))
    t_eq_O =
      let tso : Deriv (eqF (ap2 sub tT O) tT)
          tso = T_sub_O tT

          axE :
            Deriv (imp (eqF (ap2 sub tT O) tT)
                        (imp (eqF (ap2 sub tT O) O)
                              (eqF tT O)))
          axE = ax_eqTrans (ap2 sub tT O) tT O
      in mp axE tso

    -- Under Hyp_bF: HistP_sbt at tT = HistP_sbt at O.
    -- More precisely: Fst (HistP_sbt ... tT) = Fst (HistP_sbt ... O).
    mid_imp :
      Deriv (imp Hyp_bF
                  (eqF (ap1 Fst (HistP_sbt bF sF specT tT))
                        (ap1 Fst (HistP_sbt bF sF specT O))))
    mid_imp =
      let cov_cong :
            Deriv (imp Hyp_bF
                        (eqF (ap2 (cov_spec bF sF) specT tT)
                              (ap2 (cov_spec bF sF) specT O)))
          cov_cong = congR_under (cov_spec bF sF) specT t_eq_O

          snd_cong :
            Deriv (imp Hyp_bF
                        (eqF (ap1 Snd (ap2 (cov_spec bF sF) specT tT))
                              (ap1 Snd (ap2 (cov_spec bF sF) specT O))))
          snd_cong = cong1_under Snd cov_cong

          snd2_cong :
            Deriv (imp Hyp_bF (eqF (HistP_sbt bF sF specT tT)
                                       (HistP_sbt bF sF specT O)))
          snd2_cong = cong1_under Snd snd_cong
      in cong1_under Fst snd2_cong

    bFCase : Deriv (imp Hyp_bF (eqF LHS_bF RHS_bF))
    bFCase =
      let lhs_imp :
            Deriv (imp Hyp_bF (eqF LHS_bF (ap1 Fst (HistP_sbt bF sF specT O))))
          lhs_imp = liftP Hyp_bF L_to_FstHistO

          mid_sym :
            Deriv (imp Hyp_bF
                        (eqF (ap1 Fst (HistP_sbt bF sF specT O))
                              (ap1 Fst (HistP_sbt bF sF specT tT))))
          mid_sym = impTrans mid_imp
                      (eqSymImp (ap1 Fst (HistP_sbt bF sF specT tT))
                                (ap1 Fst (HistP_sbt bF sF specT O)))

          rhs_imp :
            Deriv (imp Hyp_bF (eqF (ap1 Fst (HistP_sbt bF sF specT tT)) RHS_bF))
          rhs_imp = liftP Hyp_bF (ruleSym R_to_FstHistT)

          sF1 :
            Deriv (imp Hyp_bF (eqF LHS_bF (ap1 Fst (HistP_sbt bF sF specT tT))))
          sF1 = trans_under lhs_imp mid_sym
      in trans_under sF1 rhs_imp

    ----------------------------------------------------------------
    -- Step case at var 0 := s var 0.

    Hyp_sF : Formula
    Hyp_sF = leq tT (ap1 s KT)

    Rf : Formula
    Rf = eqF (HPsbt bF sF specT tT (ap1 s KT))
              (HPsbt bF sF specT tT tT)

    X_case : Formula
    X_case = leq tT KT

    Y_case : Formula
    Y_case = eqF tT (ap1 s KT)

    T82_swapped :
      Deriv (imp Hyp_sF (imp (neg X_case) Y_case))
    T82_swapped = ruleInst2 zero tT (suc zero) KT refl T82

    negX_Y_under :
      Deriv (imp Pform (imp Hyp_sF (imp (neg X_case) Y_case)))
    negX_Y_under = liftP Pform T82_swapped

    ----------------------------------------------------------------
    -- X case: leq t K.  Apply IH (= identP Pform) and single_sF.

    X_R_under :
      Deriv (imp Pform (imp Hyp_sF (imp X_case Rf)))
    X_R_under =
      let ihPform :
            Deriv (imp Pform
                        (imp X_case (eqF (HPsbt bF sF specT tT KT)
                                           (HPsbt bF sF specT tT tT))))
          ihPform = identP Pform

          sss :
            Deriv (imp X_case (eqF (HPsbt bF sF specT tT (ap1 s KT))
                                     (HPsbt bF sF specT tT KT)))
          sss = stabilityP_sbt_single_sF bF sF specT KT tT

          sssPform :
            Deriv (imp Pform
                        (imp X_case (eqF (HPsbt bF sF specT tT (ap1 s KT))
                                           (HPsbt bF sF specT tT KT))))
          sssPform = liftP Pform sss

          combined :
            Deriv (imp Pform
                        (imp X_case (eqF (HPsbt bF sF specT tT (ap1 s KT))
                                           (HPsbt bF sF specT tT tT))))
          combined = trans_under2 sssPform ihPform
      in insertHyp1 combined

    ----------------------------------------------------------------
    -- Y case: t = s K.  Both sides of Rf are equal under substitution.

    Y_R_under :
      Deriv (imp Pform (imp Hyp_sF (imp Y_case Rf)))
    Y_R_under =
      let H_target : Term
          H_target = ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                               (ap2 sub (ap1 s KT) (ap1 s KT)))

          LHS_Y : Term
          LHS_Y = HPsbt bF sF specT tT (ap1 s KT)

          RHS_Y : Term
          RHS_Y = HPsbt bF sF specT tT tT

          sub_arg_R :
            Deriv (imp Y_case
                        (eqF (ap2 sub (ap1 s KT) tT)
                              (ap2 sub (ap1 s KT) (ap1 s KT))))
          sub_arg_R = ax_eqCongR sub tT (ap1 s KT) (ap1 s KT)

          iter_arg_R :
            Deriv (imp Y_case
                        (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                               (ap2 sub (ap1 s KT) tT))
                              (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                               (ap2 sub (ap1 s KT) (ap1 s KT)))))
          iter_arg_R = congR_under (iter Snd) (HistP_sbt bF sF specT (ap1 s KT)) sub_arg_R

          lhs_to_target : Deriv (imp Y_case (eqF LHS_Y H_target))
          lhs_to_target = cong1_under Fst iter_arg_R

          cov_arg :
            Deriv (imp Y_case
                        (eqF (ap2 (cov_spec bF sF) specT tT)
                              (ap2 (cov_spec bF sF) specT (ap1 s KT))))
          cov_arg = ax_eqCongR (cov_spec bF sF) tT (ap1 s KT) specT

          snd_cov :
            Deriv (imp Y_case (eqF (ap1 Snd (ap2 (cov_spec bF sF) specT tT))
                                     (ap1 Snd (ap2 (cov_spec bF sF) specT (ap1 s KT)))))
          snd_cov = cong1_under Snd cov_arg

          hist_arg :
            Deriv (imp Y_case (eqF (HistP_sbt bF sF specT tT)
                                     (HistP_sbt bF sF specT (ap1 s KT))))
          hist_arg = cong1_under Snd snd_cov

          iter_arg_L :
            Deriv (imp Y_case
                        (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT tT)
                                               (ap2 sub tT tT))
                              (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                               (ap2 sub tT tT))))
          iter_arg_L = congL_under (iter Snd) (ap2 sub tT tT) hist_arg

          T1_to_T2 :
            Deriv (imp Y_case
                        (eqF RHS_Y
                              (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                                          (ap2 sub tT tT)))))
          T1_to_T2 = cong1_under Fst iter_arg_L

          sub_arg_L :
            Deriv (imp Y_case
                        (eqF (ap2 sub tT tT) (ap2 sub (ap1 s KT) tT)))
          sub_arg_L = ax_eqCongL sub tT (ap1 s KT) tT

          iter_sF2 :
            Deriv (imp Y_case
                        (eqF (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                               (ap2 sub tT tT))
                              (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                               (ap2 sub (ap1 s KT) tT))))
          iter_sF2 = congR_under (iter Snd) (HistP_sbt bF sF specT (ap1 s KT)) sub_arg_L

          T2_to_T3 :
            Deriv (imp Y_case
                        (eqF (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                                        (ap2 sub tT tT)))
                              (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                                        (ap2 sub (ap1 s KT) tT)))))
          T2_to_T3 = cong1_under Fst iter_sF2

          T3_to_T4 :
            Deriv (imp Y_case
                        (eqF (ap1 Fst (ap2 (iter Snd) (HistP_sbt bF sF specT (ap1 s KT))
                                                        (ap2 sub (ap1 s KT) tT)))
                              H_target))
          T3_to_T4 = cong1_under Fst iter_arg_R

          rhs_to_target : Deriv (imp Y_case (eqF RHS_Y H_target))
          rhs_to_target = trans_under T1_to_T2 (trans_under T2_to_T3 T3_to_T4)

          rhs_to_target_sym :
            Deriv (imp Y_case (eqF H_target RHS_Y))
          rhs_to_target_sym =
            impTrans rhs_to_target (eqSymImp RHS_Y H_target)

          Y_inner : Deriv (imp Y_case (eqF LHS_Y RHS_Y))
          Y_inner = trans_under lhs_to_target rhs_to_target_sym
      in liftP Pform (liftP Hyp_sF Y_inner)

    sFImp : Deriv (imp Pform (substF 0 (ap1 s (var zero)) Pform))
    sFImp =
      caseElimUnderTwo {P1 = Pform} {P2 = Hyp_sF}
        {X = X_case} {Y = Y_case} {Rf = Rf}
        negX_Y_under X_R_under Y_R_under

------------------------------------------------------------------------
-- Universal stability:  for ANY  spec, t, K ,
--   Deriv (imp (leq t K) (eqF (HPsbt bF sF spec t K) (HPsbt bF sF spec t t)))
--
-- Proof via the c-renaming trick: rename var 2 to FRESH var c, do
-- ruleInst2 to substitute (var 0, var 1) with (K, t), then ruleInst c -> spec.

private
  freshKTS : Term -> Term -> Term -> Nat
  freshKTS K t spec =
    suc (suc (maxN (maxVarT K) (maxN (maxVarT t) (maxVarT spec))))

  freshKTS_above_K : (K t spec : Term) -> NatLe (maxVarT K) (freshKTS K t spec)
  freshKTS_above_K K t spec =
    let leA : NatLe (maxVarT K) (maxN (maxVarT K) (maxN (maxVarT t) (maxVarT spec)))
        leA = maxN-le-left (maxVarT K) (maxN (maxVarT t) (maxVarT spec))
    in le-suc-right (le-suc-right leA)

  freshKTS_above_t : (K t spec : Term) -> NatLe (maxVarT t) (freshKTS K t spec)
  freshKTS_above_t K t spec =
    let leA : NatLe (maxVarT t) (maxN (maxVarT t) (maxVarT spec))
        leA = maxN-le-left (maxVarT t) (maxVarT spec)
        leB : NatLe (maxN (maxVarT t) (maxVarT spec))
                     (maxN (maxVarT K) (maxN (maxVarT t) (maxVarT spec)))
        leB = maxN-le-right (maxVarT K) (maxN (maxVarT t) (maxVarT spec))
        leC : NatLe (maxVarT t) (maxN (maxVarT K) (maxN (maxVarT t) (maxVarT spec)))
        leC = le-trans leA leB
    in le-suc-right (le-suc-right leC)

stabilityP_sbt_at :
  (bF : Fun1) (sF : Fun2) (spec t K : Term) ->
  Deriv (imp (leq t K) (eqF (HPsbt bF sF spec t K) (HPsbt bF sF spec t t)))
stabilityP_sbt_at bF sF spec t K =
  let c : Nat
      c = freshKTS K t spec

      sF1 = ruleInst (suc (suc zero)) (var c) (stabilityP_sbt_v012 bF sF)

      sF2 = ruleInst2 zero K (suc zero) t refl sF1

      sF3 = ruleInst c spec sF2

      bridge_K : Eq (substT c spec K) K
      bridge_K = substT_above_max c K spec (freshKTS_above_K K t spec)

      bridge_t : Eq (substT c spec t) t
      bridge_t = substT_above_max c t spec (freshKTS_above_t K t spec)

      bridge_vc : Eq (substT c spec (var c)) spec
      bridge_vc = eqCong (\ b -> boolCase b spec (var c)) (natEq-refl c)

      sFA = eqSubst (\ x -> Deriv
                (imp (leq (substT c spec t) x)
                      (eqF (HPsbt bF sF (substT c spec (var c)) (substT c spec t) x)
                            (HPsbt bF sF (substT c spec (var c)) (substT c spec t) (substT c spec t)))))
                bridge_K sF3

      sFB = eqSubst (\ x -> Deriv
                (imp (leq x K)
                      (eqF (HPsbt bF sF (substT c spec (var c)) x K)
                            (HPsbt bF sF (substT c spec (var c)) x x))))
                bridge_t sFA

      sFC = eqSubst (\ x -> Deriv
                (imp (leq t K)
                      (eqF (HPsbt bF sF x t K) (HPsbt bF sF x t t))))
                bridge_vc sFB
  in sFC
