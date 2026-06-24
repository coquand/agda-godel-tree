{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrDevByHead -- SCHEMATIC-IN-FUN devF equations: devF (tmAp1 f t) and
-- devF (tmAp2 g a b) dispatched on the HEAD tag of the carried fun  Fst f /
-- Fst g  (rather than f / g being a concrete combinator).  These generalise
-- T4.PrDev.devF_o/u/s/C/v/Rb/Rs/R_cong to an arbitrary fun term, which is what
-- the opaque triangle needs: devF is applied to srcF p = tmAp1 (funP p) (..)
-- where funP p is a projection of p (a term, not a known combinator).  No
-- opaque harness -- the input is the BUILT tmAp1/tmAp2 code.
--
--   Fst f = 4 (o)  => devF (tmAp1 f t) = tmO
--   Fst f = 5 (u)  => devF (tmAp1 f t) = devF t
--   Fst f = 3 (s)  => devF (tmAp1 f t) = tmAp1 cSuc (devF t)
--   Fst f = 6 (C)  => devF (tmAp1 f t) = tmAp2 (gF f)(tmAp1 (h1F f)(devF t))(tmAp1 (h2F f)(devF t))
--   Fst g = 7 (v)  => devF (tmAp2 g a b) = devF b
--   Fst g = 8 (R)  => devF (tmAp2 g a tmO)        = tmAp1 (gF g)(devF a)            (Rb)
--   Fst g = 8 (R)  => devF (tmAp2 g a (tmAp1 cSuc n)) = ...                          (Rs)
--   Fst g = 8 (R), b not tmO/not s-headed => devF (tmAp2 g a b) = tmAp2 (cRec ..)(devF a)(devF b)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrDevByHead where

open import T4.Base

open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; cSuc ; cRec ; tgO ; tgAp1 ; tgSuc )
open import T4.PrDev

open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )
open import T4.ForkImp using ( fork_false_to_snd_imp ; natEqSkip_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )
open import BRA3.Contrapositive using ( identP )

open import BRA3.Church       using ( pi )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Fun-code component projections.

gF : Term -> Term
gF f = ap1 Fst (ap1 Snd f)
h1F : Term -> Term
h1F f = ap1 Fst (ap1 Snd (ap1 Snd f))
h2F : Term -> Term
h2F f = ap1 Snd (ap1 Snd (ap1 Snd f))

private
  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k p = decideNatNeq m k p

------------------------------------------------------------------------
-- SECTION 1.  ap1 cases (dispatch on Fst f).

devF_ap1_o_h : (f t : Term) -> Deriv (eqF (ap1 Fst f) (natCode 4)) ->
  Deriv (eqF (ap1 devF (tmAp1 f t)) tmO)
devF_ap1_o_h f t hf =
  let open Ap1 f t
      hF = headF_at f t (natCode 4) hf
      fires = fork_true_to_fst br_o ap1_lvl1 (testF 4) input_pkg (idxTest_fire headF 4 input_pkg hF)
  in ruleTrans to_ap1Cell (ruleTrans fires (tmOF_val input_pkg))

devF_ap1_u_h : (f t : Term) -> Deriv (eqF (ap1 Fst f) (natCode 5)) ->
  Deriv (eqF (ap1 devF (tmAp1 f t)) (ap1 devF t))
devF_ap1_u_h f t hf =
  let open Ap1 f t
      hF = headF_at f t (natCode 5) hf
      fires =
        ruleTrans (fork_false_to_snd br_o ap1_lvl1 (testF 4) input_pkg (idxTest_skip headF 5 4 input_pkg (wn 5 4 (\ ())) hF))
                  (fork_true_to_fst br_u ap1_lvl2 (testF 5) input_pkg (idxTest_fire headF 5 input_pkg hF))
  in ruleTrans to_ap1Cell (ruleTrans fires recT)

devF_ap1_s_h : (f t : Term) -> Deriv (eqF (ap1 Fst f) (natCode 3)) ->
  Deriv (eqF (ap1 devF (tmAp1 f t)) (tmAp1 cSuc (ap1 devF t)))
devF_ap1_s_h f t hf =
  let open Ap1 f t
      hF = headF_at f t (natCode 3) hf
      fires =
        ruleTrans (fork_false_to_snd br_o ap1_lvl1 (testF 4) input_pkg (idxTest_skip headF 3 4 input_pkg (wn 3 4 (\ ())) hF))
          (ruleTrans (fork_false_to_snd br_u ap1_lvl2 (testF 5) input_pkg (idxTest_skip headF 3 5 input_pkg (wn 3 5 (\ ())) hF))
                     (fork_true_to_fst br_s ap1_lvl3 (testF 3) input_pkg (idxTest_fire headF 3 input_pkg hF)))
      val = mkAp1_val cSucF devT input_pkg cSuc (ap1 devF t) (cSucF_val input_pkg) recT
  in ruleTrans to_ap1Cell (ruleTrans fires val)

devF_ap1_C_h : (f t : Term) -> Deriv (eqF (ap1 Fst f) (natCode 6)) ->
  Deriv (eqF (ap1 devF (tmAp1 f t))
             (tmAp2 (gF f) (tmAp1 (h1F f) (ap1 devF t)) (tmAp1 (h2F f) (ap1 devF t))))
devF_ap1_C_h f t hf =
  let open Ap1 f t
      hF = headF_at f t (natCode 6) hf
      fBun_eq : Deriv (eqF (ap1 fBun input_pkg) (ap1 Snd f))
      fBun_eq = ruleTrans (compose1U_eq Snd apFun input_pkg) (cong1 Snd apFun_eq)
      bG0_eq : Deriv (eqF (ap1 bG0 input_pkg) (gF f))
      bG0_eq = ruleTrans (compose1U_eq Fst fBun input_pkg) (cong1 Fst fBun_eq)
      fInner_eq : Deriv (eqF (ap1 (compose1U Snd fBun) input_pkg) (ap1 Snd (ap1 Snd f)))
      fInner_eq = ruleTrans (compose1U_eq Snd fBun input_pkg) (cong1 Snd fBun_eq)
      bH1_eq : Deriv (eqF (ap1 bH1 input_pkg) (h1F f))
      bH1_eq = ruleTrans (compose1U_eq Fst (compose1U Snd fBun) input_pkg) (cong1 Fst fInner_eq)
      bH2_eq : Deriv (eqF (ap1 bH2 input_pkg) (h2F f))
      bH2_eq = ruleTrans (compose1U_eq Snd (compose1U Snd fBun) input_pkg) (cong1 Snd fInner_eq)
      fires =
        ruleTrans (fork_false_to_snd br_o ap1_lvl1 (testF 4) input_pkg (idxTest_skip headF 6 4 input_pkg (wn 6 4 (\ ())) hF))
          (ruleTrans (fork_false_to_snd br_u ap1_lvl2 (testF 5) input_pkg (idxTest_skip headF 6 5 input_pkg (wn 6 5 (\ ())) hF))
            (ruleTrans (fork_false_to_snd br_s ap1_lvl3 (testF 3) input_pkg (idxTest_skip headF 6 3 input_pkg (wn 6 3 (\ ())) hF))
                       (fork_true_to_fst br_C br_ap1cong (testF 6) input_pkg (idxTest_fire headF 6 input_pkg hF))))
      armH1 = mkAp1_val bH1 devT input_pkg (h1F f) (ap1 devF t) bH1_eq recT
      armH2 = mkAp1_val bH2 devT input_pkg (h2F f) (ap1 devF t) bH2_eq recT
      val = mkAp2_val bG0 (mkAp1 bH1 devT) (mkAp1 bH2 devT) input_pkg
              (gF f) (tmAp1 (h1F f) (ap1 devF t)) (tmAp1 (h2F f) (ap1 devF t)) bG0_eq armH1 armH2
  in ruleTrans to_ap1Cell (ruleTrans fires val)

------------------------------------------------------------------------
-- SECTION 2.  ap2 v case (dispatch on Fst g).

devF_ap2_v_h : (g a b : Term) -> Deriv (eqF (ap1 Fst g) (natCode 7)) ->
  Deriv (eqF (ap1 devF (tmAp2 g a b)) (ap1 devF b))
devF_ap2_v_h g a b hg =
  let open Ap2 g a b
      hG = headG_eq (natCode 7) hg
      fires = fork_true_to_fst br_v ap2_lvl1 (testG 7) input_pkg (idxTest_fire headF 7 input_pkg hG)
  in ruleTrans to_ap2Cell (ruleTrans fires recB)

------------------------------------------------------------------------
-- SECTION 3.  ap2 R cases (Fst g = 8, then dispatch on the second arg).

-- shared R plumbing for an arbitrary R-fun g.
private
  module RH (g a b : Term) (hg : Deriv (eqF (ap1 Fst g) (natCode 8))) where
    open Ap2 g a b public
    hG : Deriv (eqF (ap1 headF input_pkg) (natCode 8))
    hG = headG_eq (natCode 8) hg
    gBun_eq : Deriv (eqF (ap1 fBun input_pkg) (ap1 Snd g))
    gBun_eq = ruleTrans (compose1U_eq Snd apFun input_pkg) (cong1 Snd apFun_eq)
    bG0_eq : Deriv (eqF (ap1 bG0 input_pkg) (gF g))
    bG0_eq = ruleTrans (compose1U_eq Fst fBun input_pkg) (cong1 Fst gBun_eq)
    gInner_eq : Deriv (eqF (ap1 (compose1U Snd fBun) input_pkg) (ap1 Snd (ap1 Snd g)))
    gInner_eq = ruleTrans (compose1U_eq Snd fBun input_pkg) (cong1 Snd gBun_eq)
    bH1_eq : Deriv (eqF (ap1 bH1 input_pkg) (h1F g))
    bH1_eq = ruleTrans (compose1U_eq Fst (compose1U Snd fBun) input_pkg) (cong1 Fst gInner_eq)
    bH2_eq : Deriv (eqF (ap1 bH2 input_pkg) (h2F g))
    bH2_eq = ruleTrans (compose1U_eq Snd (compose1U Snd fBun) input_pkg) (cong1 Snd gInner_eq)
    to_R_disp : Deriv (eqF (ap1 ap2Cell input_pkg) (ap1 R_disp input_pkg))
    to_R_disp =
      ruleTrans (fork_false_to_snd br_v ap2_lvl1 (testG 7) input_pkg (idxTest_skip headF 8 7 input_pkg (wn 8 7 (\ ())) hG))
                (fork_true_to_fst R_disp br_ap2cong (testG 8) input_pkg (idxTest_fire headF 8 input_pkg hG))

devF_ap2_Rb_h : (g a : Term) -> Deriv (eqF (ap1 Fst g) (natCode 8)) ->
  Deriv (eqF (ap1 devF (tmAp2 g a tmO)) (tmAp1 (gF g) (ap1 devF a)))
devF_ap2_Rb_h g a hg =
  let open RH g a tmO hg
      hB : Deriv (eqF (ap1 headB input_pkg) (natCode 0))
      hB = ruleTrans (compose1U_eq Fst apB input_pkg) (ruleTrans (cong1 Fst apB_eq) (axFst tgO O))
      fires = fork_true_to_fst br_Rb R_lvl2 (testB 0) input_pkg (idxTest_fire headB 0 input_pkg hB)
      val = mkAp1_val bG0 devA input_pkg (gF g) (ap1 devF a) bG0_eq recA
  in ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val))

devF_ap2_Rs_h : (g a n : Term) -> Deriv (eqF (ap1 Fst g) (natCode 8)) ->
  Deriv (eqF (ap1 devF (tmAp2 g a (tmAp1 cSuc n)))
             (tmAp2 (h1F g) (tmAp2 (h2F g) (ap1 devF a) (ap1 devF n))
                            (tmAp2 (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF n))))
devF_ap2_Rs_h g a n hg =
  let open RH g a (tmAp1 cSuc n) hg
      hB : Deriv (eqF (ap1 headB input_pkg) (natCode 1))
      hB = ruleTrans (compose1U_eq Fst apB input_pkg) (ruleTrans (cong1 Fst apB_eq) (axFst tgAp1 (ap2 Pair cSuc n)))
      bSnd_eq : Deriv (eqF (ap1 bSnd input_pkg) (ap2 Pair cSuc n))
      bSnd_eq = ruleTrans (compose1U_eq Snd apB input_pkg) (ruleTrans (cong1 Snd apB_eq) (axSnd tgAp1 (ap2 Pair cSuc n)))
      bFun_eq : Deriv (eqF (ap1 (compose1U Fst bSnd) input_pkg) cSuc)
      bFun_eq = ruleTrans (compose1U_eq Fst bSnd input_pkg) (ruleTrans (cong1 Fst bSnd_eq) (axFst cSuc n))
      hBF : Deriv (eqF (ap1 headBFun input_pkg) (natCode 3))
      hBF = ruleTrans (compose1U_eq Fst (compose1U Fst bSnd) input_pkg) (ruleTrans (cong1 Fst bFun_eq) (axFst tgSuc O))
      fires =
        ruleTrans (fork_false_to_snd br_Rb R_lvl2 (testB 0) input_pkg (idxTest_skip headB 1 0 input_pkg (wn 1 0 (\ ())) hB))
                  (fork_true_to_fst br_Rs br_Rcong (testBF 3) input_pkg (idxTest_fire headBFun 3 input_pkg hBF))
      recB' : Deriv (eqF (ap1 devB input_pkg) (tmAp1 cSuc (ap1 devF n)))
      recB' = ruleTrans recB (devF_ap1_s n)
      devN_eq : Deriv (eqF (ap1 devN input_pkg) (ap1 devF n))
      devN_eq = ruleTrans (compose1U_eq Snd (compose1U Snd devB) input_pkg)
                  (ruleTrans (cong1 Snd (ruleTrans (compose1U_eq Snd devB input_pkg) (cong1 Snd recB')))
                    (ruleTrans (cong1 Snd (axSnd tgAp1 (ap2 Pair cSuc (ap1 devF n)))) (axSnd cSuc (ap1 devF n))))
      arm2 = mkAp2_val bH2 devA devN input_pkg (h2F g) (ap1 devF a) (ap1 devF n) bH2_eq recA devN_eq
      recFun = mkRec_val bG0 bH1 bH2 input_pkg (gF g) (h1F g) (h2F g) bG0_eq bH1_eq bH2_eq
      arm3 = mkAp2_val (mkRec bG0 bH1 bH2) devA devN input_pkg (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF n) recFun recA devN_eq
      val = mkAp2_val bH1 (mkAp2 bH2 devA devN) (mkAp2 (mkRec bG0 bH1 bH2) devA devN) input_pkg
              (h1F g) (tmAp2 (h2F g) (ap1 devF a) (ap1 devF n)) (tmAp2 (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF n)) bH1_eq arm2 arm3
  in ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val))

devF_ap2_Rcong_h : (g a b : Term) -> Deriv (eqF (ap1 Fst g) (natCode 8)) ->
  (mb mf : Nat) -> Deriv (eqF (ap1 Fst b) (natCode mb)) -> ((Eq mb 0) -> Empty) ->
  Deriv (eqF (ap1 Fst (ap1 Fst (ap1 Snd b))) (natCode mf)) -> ((Eq mf 3) -> Empty) ->
  Deriv (eqF (ap1 devF (tmAp2 g a b)) (tmAp2 (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF b)))
devF_ap2_Rcong_h g a b hg mb mf hb mb0 hbf mf3 =
  let open RH g a b hg
      headB_v : Deriv (eqF (ap1 headB input_pkg) (natCode mb))
      headB_v = ruleTrans (compose1U_eq Fst apB input_pkg) (ruleTrans (cong1 Fst apB_eq) hb)
      fstSndB : Deriv (eqF (ap1 (compose1U Fst bSnd) input_pkg) (ap1 Fst (ap1 Snd b)))
      fstSndB = ruleTrans (compose1U_eq Fst bSnd input_pkg)
                  (cong1 Fst (ruleTrans (compose1U_eq Snd apB input_pkg) (cong1 Snd apB_eq)))
      headBFun_v : Deriv (eqF (ap1 headBFun input_pkg) (natCode mf))
      headBFun_v = ruleTrans (compose1U_eq Fst (compose1U Fst bSnd) input_pkg) (ruleTrans (cong1 Fst fstSndB) hbf)
      fires =
        ruleTrans (fork_false_to_snd br_Rb R_lvl2 (testB 0) input_pkg (idxTest_skip headB mb 0 input_pkg (wn mb 0 mb0) headB_v))
                  (fork_false_to_snd br_Rs br_Rcong (testBF 3) input_pkg (idxTest_skip headBFun mf 3 input_pkg (wn mf 3 mf3) headBFun_v))
      recFun = mkRec_val bG0 bH1 bH2 input_pkg (gF g) (h1F g) (h2F g) bG0_eq bH1_eq bH2_eq
      val = mkAp2_val (mkRec bG0 bH1 bH2) devA devB input_pkg (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF b) recFun recA recB
  in ruleTrans to_ap2Cell (ruleTrans to_R_disp (ruleTrans fires val))

-- IMP-FORM:  the head-2 condition  Fst(Fst(Snd b)) = natCode mf  threaded as the
-- antecedent (g concrete via reconstruction so hg/hb are bare; only the inner-fun
-- head mf is ctx-only in the glue).  Used by the ap2c cRec Rcong sub-glue.
devF_ap2_Rcong_imp : (g a b : Term) -> Deriv (eqF (ap1 Fst g) (natCode 8)) ->
  (mb mf : Nat) -> Deriv (eqF (ap1 Fst b) (natCode mb)) -> ((Eq mb 0) -> Empty) -> ((Eq mf 3) -> Empty) ->
  Deriv (imp (eqF (ap1 Fst (ap1 Fst (ap1 Snd b))) (natCode mf))
             (eqF (ap1 devF (tmAp2 g a b)) (tmAp2 (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF b))))
devF_ap2_Rcong_imp g a b hg mb mf hb mb0 mf3 =
  let open RH g a b hg
      Hbf : Formula
      Hbf = eqF (ap1 Fst (ap1 Fst (ap1 Snd b))) (natCode mf)
      res : Term
      res = tmAp2 (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF b)
      headB_v : Deriv (eqF (ap1 headB input_pkg) (natCode mb))
      headB_v = ruleTrans (compose1U_eq Fst apB input_pkg) (ruleTrans (cong1 Fst apB_eq) hb)
      fstSndB : Deriv (eqF (ap1 (compose1U Fst bSnd) input_pkg) (ap1 Fst (ap1 Snd b)))
      fstSndB = ruleTrans (compose1U_eq Fst bSnd input_pkg)
                  (cong1 Fst (ruleTrans (compose1U_eq Snd apB input_pkg) (cong1 Snd apB_eq)))
      headBFun_v_imp : Deriv (imp Hbf (eqF (ap1 headBFun input_pkg) (natCode mf)))
      headBFun_v_imp = impEqTrans (ap1 headBFun input_pkg) (ap1 Fst (ap1 Fst (ap1 Snd b))) (natCode mf)
                         (impLift (ruleTrans (compose1U_eq Fst (compose1U Fst bSnd) input_pkg) (cong1 Fst fstSndB)))
                         (identP Hbf)
      firstFork : Deriv (eqF (ap1 R_disp input_pkg) (ap1 R_lvl2 input_pkg))
      firstFork = fork_false_to_snd br_Rb R_lvl2 (testB 0) input_pkg (idxTest_skip headB mb 0 input_pkg (wn mb 0 mb0) headB_v)
      secondFork : Deriv (imp Hbf (eqF (ap1 R_lvl2 input_pkg) (ap1 br_Rcong input_pkg)))
      secondFork = fork_false_to_snd_imp Hbf br_Rs br_Rcong (testBF 3) input_pkg
                     (natEqSkip_imp Hbf headBFun mf 3 input_pkg (wn mf 3 mf3) headBFun_v_imp)
      fires_imp : Deriv (imp Hbf (eqF (ap1 R_disp input_pkg) (ap1 br_Rcong input_pkg)))
      fires_imp = impEqTrans (ap1 R_disp input_pkg) (ap1 R_lvl2 input_pkg) (ap1 br_Rcong input_pkg)
                    (impLift firstFork) secondFork
      recFun = mkRec_val bG0 bH1 bH2 input_pkg (gF g) (h1F g) (h2F g) bG0_eq bH1_eq bH2_eq
      val : Deriv (eqF (ap1 br_Rcong input_pkg) res)
      val = mkAp2_val (mkRec bG0 bH1 bH2) devA devB input_pkg (cRec (gF g) (h1F g) (h2F g)) (ap1 devF a) (ap1 devF b) recFun recA recB
  in impEqTrans (ap1 devF (tmAp2 g a b)) (ap1 R_disp input_pkg) res
       (impLift (ruleTrans to_ap2Cell to_R_disp))
       (impEqTrans (ap1 R_disp input_pkg) (ap1 br_Rcong input_pkg) res fires_imp (impLift val))
