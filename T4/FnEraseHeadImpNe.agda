{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnEraseHeadImpNe -- the erase-projection bridges (T4.FnEraseProj) in
-- IMP-FORM with the child-non-O premise ALSO carried as an antecedent
-- imp H (neg (X = O)), which is what the ap2 Rcong dispatch needs: the recursion
-- child  mMb sk  is only known /= O via context (never bare, unlike the outer sk).
--
-- Crucially LIGHTWEIGHT: the Rcong dispatch only reads erase X's HEAD tag and
-- FUN-CODE, never the recovered child, so we unfold  erase X  only as far as the
-- cell  mkAp1/mkAp2 mc_f ... (opkg X) = tmAp1/tmAp2 (mc_f (opkg X)) (<child slot>)
-- (leaving the child slot symbolic).  Only the free harness unfold (opUnfold_imp),
-- the cheap op_tag_imp / mc_f_imp accessors (from op_newK_imp / op_rc_imp), and the
-- mkAp definitional unfold are needed -- no dev-accessor / lookup / descent bounds.
--
--   erasedHeadNe0_ap1_imp / _ap2_imp : imp H (neg (Fst (erase X) = natCode 0))
--   erasedBfunh_ap1_imp   / _ap2_imp : imp H (bfunhF (tmAp2 g a (erase X)) = Fst (mFun X))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnEraseHeadImpNe where

open import T4.Base

open import T4.OpaqueHarnessImp using ( module HimpBase )
open import T4.ParsObj using ( stepOf ; test1 )
open import T4.ProgParse using ( get_tag )
open import T4.FoldRec using ( get_newK ; lookupAt )
open import T4.LenR using ( get_rc )
open import T4.PrDev using ( mkAp1_val ; mkAp2_val )
open import T4.PrCodeObj using ( tmAp1 ; tmAp2 ; tgAp1 ; tgAp2 ; hd_tmAp1 ; hd_tmAp2 ; ar_tmAp2 )
open import T4.FnErase using ( erase ; eraseAp1Cell ; eraseAp2Cell )
open import T4.FnMcontract using ( mc_f ; mc_bun ; mc_msIdx ; mc_maIdx ; mc_mbIdx )
open import T4.FnMark using ( mFun )
open import T4.FnTerm using ( bfunhF ; bfunF ; bF ; bF_ap2 ; bfunhF_ap2 )

open import BRA3.Equational using ( axRefl )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq )
open import BRA3.SubT.V2NatNeq using ( decideNatNeq )
open import BRA3.Classical using ( axContrapos )
open import BRA3.Logic using ( eqSymImp )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impCongR )
open import T4.ImpEq using ( impMp )
open import T4.ForkImp
  using ( natEqFire_imp ; natEqSkip_imp ; natEqSkipNeg_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.DescSndImp using ( neSucc )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.Dispatch using ( constN )
open import T4.CtxKit using ( lift2 ; get2a ; get2b ; ap2c ; trans2c )

open HimpBase Z (stepOf eraseAp1Cell eraseAp2Cell)

------------------------------------------------------------------------
-- SECTION 0.  a value = s u  is /= O  (imp-form).

private
  neValSucc : (t uu : Term) -> Deriv (imp (eqF t (ap1 s uu)) (neg (eqF t O)))
  neValSucc t uu =
    let A : Formula
        A = eqF t (ap1 s uu)
        P : Formula
        P = eqF t O
        suEqT : Deriv (imp A (imp P (eqF (ap1 s uu) t)))
        suEqT = ap2c (lift2 A P (eqSymImp t (ap1 s uu))) (get2a A P)
        g1 : Deriv (imp A (imp P (eqF (ap1 s uu) O)))
        g1 = trans2c (ap1 s uu) t O suEqT (get2b A P)
    in impMp {A} (impMp {A} (impLift {A} (axContrapos P (eqF (ap1 s uu) O))) g1)
              (impLift {A} (neSucc uu))

------------------------------------------------------------------------
-- SECTION 1.  cheap imp-ne accessors (from the harness op_newK_imp / op_rc_imp).

private
  op_tag_imp : (d : Term) -> Deriv (imp (neg (eqF d O)) (eqF (ap1 get_tag (opkg d)) (ap1 Fst d)))
  op_tag_imp d =
    impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst (ap1 get_newK (opkg d))) (ap1 Fst d)
      (impLift (compose1U_eq Fst get_newK (opkg d)))
      (impCong1 Fst (ap1 get_newK (opkg d)) d (op_newK_imp d))

  mc_bun_imp : (d : Term) ->
    Deriv (imp (neg (eqF d O)) (eqF (ap1 mc_bun (opkg d)) (ap1 Snd (ap1 Snd d))))
  mc_bun_imp d =
    impEqTrans (ap1 mc_bun (opkg d)) (ap1 Snd (ap1 get_rc (opkg d))) (ap1 Snd (ap1 Snd d))
      (impLift (compose1U_eq Snd get_rc (opkg d)))
      (impCong1 Snd (ap1 get_rc (opkg d)) (ap1 Snd d) (op_rc_imp d))

  mc_f_imp : (d : Term) -> Deriv (imp (neg (eqF d O)) (eqF (ap1 mc_f (opkg d)) (mFun d)))
  mc_f_imp d =
    impEqTrans (ap1 mc_f (opkg d)) (ap1 Fst (ap1 mc_bun (opkg d))) (mFun d)
      (impLift (compose1U_eq Fst mc_bun (opkg d)))
      (impCong1 Fst (ap1 mc_bun (opkg d)) (ap1 Snd (ap1 Snd d)) (mc_bun_imp d))

  viaNe : {H : Formula} {X : Formula} (d : Term) ->
    Deriv (imp H (neg (eqF d O))) -> Deriv (imp (neg (eqF d O)) X) -> Deriv (imp H X)
  viaNe d neI f = compI neI f

------------------------------------------------------------------------
-- SECTION 2.  cell unfolds (child slot left symbolic).

private
  eraseCellAp1 : (H : Formula) (d : Term) ->
    Deriv (imp H (neg (eqF d O))) -> Deriv (imp H (eqF (ap1 Fst d) (natCode 1))) ->
    Deriv (imp H (eqF (ap1 erase d)
                      (tmAp1 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_msIdx) (opkg d)))))
  eraseCellAp1 H d neI h1I =
    let tagI : Deriv (imp H (eqF (ap1 get_tag (opkg d)) (natCode 1)))
        tagI = impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 1) (viaNe d neI (op_tag_imp d)) h1I
        firesI : Deriv (imp H (eqF (ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d))
                                   (ap1 eraseAp1Cell (opkg d))))
        firesI = fork_true_to_fst_imp H eraseAp1Cell eraseAp2Cell test1 (opkg d)
                   (natEqFire_imp H get_tag 1 (opkg d) tagI)
        cellval : Deriv (eqF (ap1 eraseAp1Cell (opkg d))
                             (tmAp1 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_msIdx) (opkg d))))
        cellval = mkAp1_val mc_f (lookupAt mc_msIdx) (opkg d)
                    (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_msIdx) (opkg d))
                    (axRefl (ap1 mc_f (opkg d))) (axRefl (ap1 (lookupAt mc_msIdx) (opkg d)))
    in impEqTrans (ap1 erase d) (ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d))
         (tmAp1 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_msIdx) (opkg d)))
         (viaNe d neI (opUnfold_imp d))
         (impEqTrans (ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d))
            (ap1 eraseAp1Cell (opkg d))
            (tmAp1 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_msIdx) (opkg d)))
            firesI (impLift cellval))

  eraseCellAp2 : (H : Formula) (d : Term) ->
    Deriv (imp H (neg (eqF d O))) -> Deriv (imp H (eqF (ap1 Fst d) (natCode 2))) ->
    Deriv (imp H (eqF (ap1 erase d)
                      (tmAp2 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d))
                             (ap1 (lookupAt mc_mbIdx) (opkg d)))))
  eraseCellAp2 H d neI h2I =
    let tagI : Deriv (imp H (eqF (ap1 get_tag (opkg d)) (natCode 2)))
        tagI = impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2) (viaNe d neI (op_tag_imp d)) h2I
        firesI : Deriv (imp H (eqF (ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d))
                                   (ap1 eraseAp2Cell (opkg d))))
        firesI = fork_false_to_snd_imp H eraseAp1Cell eraseAp2Cell test1 (opkg d)
                   (natEqSkip_imp H get_tag 2 1 (opkg d) (decideNatNeq 2 1 (\ ())) tagI)
        cellval : Deriv (eqF (ap1 eraseAp2Cell (opkg d))
                             (tmAp2 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d))
                                    (ap1 (lookupAt mc_mbIdx) (opkg d))))
        cellval = mkAp2_val mc_f (lookupAt mc_maIdx) (lookupAt mc_mbIdx) (opkg d)
                    (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d)) (ap1 (lookupAt mc_mbIdx) (opkg d))
                    (axRefl (ap1 mc_f (opkg d))) (axRefl (ap1 (lookupAt mc_maIdx) (opkg d)))
                    (axRefl (ap1 (lookupAt mc_mbIdx) (opkg d)))
    in impEqTrans (ap1 erase d) (ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d))
         (tmAp2 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d)) (ap1 (lookupAt mc_mbIdx) (opkg d)))
         (viaNe d neI (opUnfold_imp d))
         (impEqTrans (ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d))
            (ap1 eraseAp2Cell (opkg d))
            (tmAp2 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d)) (ap1 (lookupAt mc_mbIdx) (opkg d)))
            firesI (impLift cellval))

  -- bfunhF of an outer node whose b-arg is an INNER ap2 node reads the inner fun.
  b2funh : (g a fb X Y : Term) ->
    Deriv (eqF (ap1 bfunhF (tmAp2 g a (tmAp2 fb X Y))) (ap1 Fst fb))
  b2funh g a fb X Y =
    let node = tmAp2 g a (tmAp2 fb X Y)
        bfunFval : Deriv (eqF (ap1 bfunF node) fb)
        bfunFval = ruleTrans (compose1U_eq Fst (compose1U Snd bF) node)
                     (ruleTrans
                       (cong1 Fst (ruleTrans (compose1U_eq Snd bF node)
                                     (ruleTrans (cong1 Snd (bF_ap2 g a (tmAp2 fb X Y)))
                                                (ar_tmAp2 fb X Y))))
                       (axFst fb (ap2 Pair X Y)))
    in ruleTrans (compose1U_eq Fst bfunF node) (cong1 Fst bfunFval)

  -- congruence in the b-slot of an outer tmAp2 node, imp-form.
  bInI : (H : Formula) (g a : Term) {b b' : Term} -> Deriv (imp H (eqF b b')) ->
    Deriv (imp H (eqF (tmAp2 g a b) (tmAp2 g a b')))
  bInI H g a {b} {b'} e =
    impCongR Pair (ap2 Pair g (ap2 Pair a b)) (ap2 Pair g (ap2 Pair a b')) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a b') g
        (impCongR Pair b b' a e))

------------------------------------------------------------------------
-- SECTION 3.  the two Rcong facts, per shape.

erasedHeadNe0_ap1_imp : (H : Formula) (d : Term) ->
  Deriv (imp H (neg (eqF d O))) -> Deriv (imp H (eqF (ap1 Fst d) (natCode 1))) ->
  Deriv (imp H (neg (eqF (ap1 Fst (ap1 erase d)) (natCode 0))))
erasedHeadNe0_ap1_imp H d neI h1I =
  let child : Term
      child = ap1 (lookupAt mc_msIdx) (opkg d)
      headI : Deriv (imp H (eqF (ap1 Fst (ap1 erase d)) (ap1 s O)))
      headI = impEqTrans (ap1 Fst (ap1 erase d))
                (ap1 Fst (tmAp1 (ap1 mc_f (opkg d)) child)) (ap1 s O)
                (impCong1 Fst (ap1 erase d) (tmAp1 (ap1 mc_f (opkg d)) child)
                   (eraseCellAp1 H d neI h1I))
                (impLift (hd_tmAp1 (ap1 mc_f (opkg d)) child))
  in compI headI (neValSucc (ap1 Fst (ap1 erase d)) O)

erasedHeadNe0_ap2_imp : (H : Formula) (d : Term) ->
  Deriv (imp H (neg (eqF d O))) -> Deriv (imp H (eqF (ap1 Fst d) (natCode 2))) ->
  Deriv (imp H (neg (eqF (ap1 Fst (ap1 erase d)) (natCode 0))))
erasedHeadNe0_ap2_imp H d neI h2I =
  let cA : Term
      cA = ap1 (lookupAt mc_maIdx) (opkg d)
      cB : Term
      cB = ap1 (lookupAt mc_mbIdx) (opkg d)
      headI : Deriv (imp H (eqF (ap1 Fst (ap1 erase d)) (ap1 s (ap1 s O))))
      headI = impEqTrans (ap1 Fst (ap1 erase d))
                (ap1 Fst (tmAp2 (ap1 mc_f (opkg d)) cA cB)) (ap1 s (ap1 s O))
                (impCong1 Fst (ap1 erase d) (tmAp2 (ap1 mc_f (opkg d)) cA cB)
                   (eraseCellAp2 H d neI h2I))
                (impLift (hd_tmAp2 (ap1 mc_f (opkg d)) cA cB))
  in compI headI (neValSucc (ap1 Fst (ap1 erase d)) (ap1 s O))

erasedBfunh_ap1_imp : (H : Formula) (d g a : Term) ->
  Deriv (imp H (neg (eqF d O))) -> Deriv (imp H (eqF (ap1 Fst d) (natCode 1))) ->
  Deriv (imp H (eqF (ap1 bfunhF (tmAp2 g a (ap1 erase d))) (ap1 Fst (mFun d))))
erasedBfunh_ap1_imp H d g a neI h1I =
  let child : Term
      child = ap1 (lookupAt mc_msIdx) (opkg d)
  in impEqTrans (ap1 bfunhF (tmAp2 g a (ap1 erase d)))
       (ap1 bfunhF (tmAp2 g a (tmAp1 (ap1 mc_f (opkg d)) child))) (ap1 Fst (mFun d))
       (impCong1 bfunhF (tmAp2 g a (ap1 erase d)) (tmAp2 g a (tmAp1 (ap1 mc_f (opkg d)) child))
          (bInI H g a (eraseCellAp1 H d neI h1I)))
       (impEqTrans (ap1 bfunhF (tmAp2 g a (tmAp1 (ap1 mc_f (opkg d)) child)))
          (ap1 Fst (ap1 mc_f (opkg d))) (ap1 Fst (mFun d))
          (impLift (bfunhF_ap2 g a (ap1 mc_f (opkg d)) child))
          (impCong1 Fst (ap1 mc_f (opkg d)) (mFun d) (viaNe d neI (mc_f_imp d))))

erasedBfunh_ap2_imp : (H : Formula) (d g a : Term) ->
  Deriv (imp H (neg (eqF d O))) -> Deriv (imp H (eqF (ap1 Fst d) (natCode 2))) ->
  Deriv (imp H (eqF (ap1 bfunhF (tmAp2 g a (ap1 erase d))) (ap1 Fst (mFun d))))
erasedBfunh_ap2_imp H d g a neI h2I =
  let cA : Term
      cA = ap1 (lookupAt mc_maIdx) (opkg d)
      cB : Term
      cB = ap1 (lookupAt mc_mbIdx) (opkg d)
  in impEqTrans (ap1 bfunhF (tmAp2 g a (ap1 erase d)))
       (ap1 bfunhF (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB))) (ap1 Fst (mFun d))
       (impCong1 bfunhF (tmAp2 g a (ap1 erase d)) (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB))
          (bInI H g a (eraseCellAp2 H d neI h2I)))
       (impEqTrans (ap1 bfunhF (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB)))
          (ap1 Fst (ap1 mc_f (opkg d))) (ap1 Fst (mFun d))
          (impLift (b2funh g a (ap1 mc_f (opkg d)) cA cB))
          (impCong1 Fst (ap1 mc_f (opkg d)) (mFun d) (viaNe d neI (mc_f_imp d))))

------------------------------------------------------------------------
-- SECTION 4.  OBJECT-implication forms (for lift+ap into a leaf context).

open import T4.PrLeafReflOImp using ( ne_from_head1 )
open import BRA3.Logic using ( prependEqLeft )

-- neg-equality transport:  a = b , neg (b = k)  =>  neg (a = k) .
negEqTransport : (a b : Term) (k : Nat) ->
  Deriv (imp (eqF a b) (imp (neg (eqF b (natCode k))) (neg (eqF a (natCode k)))))
negEqTransport a b k =
  let A : Formula
      A = eqF a b
      Bk : Formula
      Bk = eqF a (natCode k)
      prepMap : Deriv (imp A (imp Bk (eqF b (natCode k))))
      prepMap = trans2c b a (natCode k)
                  (ap2c (lift2 A Bk (eqSymImp a b)) (get2a A Bk))
                  (get2b A Bk)
  in impMp {A} (impLift {A} (axContrapos (eqF a (natCode k)) (eqF b (natCode k)))) prepMap

-- ap1-shape object bridges (ne derived from the head-1 fact itself).
erasedHeadNe0_ap1_obj : (d : Term) ->
  Deriv (imp (eqF (ap1 Fst d) (natCode 1)) (neg (eqF (ap1 Fst (ap1 erase d)) (natCode 0))))
erasedHeadNe0_ap1_obj d =
  erasedHeadNe0_ap1_imp (eqF (ap1 Fst d) (natCode 1)) d (ne_from_head1 d)
    (identP (eqF (ap1 Fst d) (natCode 1)))
  where open import BRA3.Contrapositive using ( identP )

erasedBfunh_ap1_obj : (d g a : Term) ->
  Deriv (imp (eqF (ap1 Fst d) (natCode 1))
             (eqF (ap1 bfunhF (tmAp2 g a (ap1 erase d))) (ap1 Fst (mFun d))))
erasedBfunh_ap1_obj d g a =
  erasedBfunh_ap1_imp (eqF (ap1 Fst d) (natCode 1)) d g a (ne_from_head1 d)
    (identP (eqF (ap1 Fst d) (natCode 1)))
  where open import BRA3.Contrapositive using ( identP )

------------------------------------------------------------------------
-- SECTION 5.  ap2 neg-shape object bridges.  erase forks ONLY on head = 1, so
-- neg (Fst d = 1) suffices to reach the ap2 cell (no need for Fst d = 2).  Built
-- directly in the 2-context [neg (d = O), neg (Fst d = 1)].

private
  GNE : Term -> Formula
  GNE d = neg (eqF d O)
  GNH : Term -> Formula
  GNH d = neg (eqF (ap1 Fst d) (natCode 1))

  -- erase d = tmAp2 (mc_f (opkg d)) (maSlot) (mbSlot) , in [GNE d, GNH d].
  eraseCell2 : (d : Term) ->
    Deriv (imp (GNE d) (imp (GNH d)
             (eqF (ap1 erase d)
                  (tmAp2 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d))
                         (ap1 (lookupAt mc_mbIdx) (opkg d))))))
  eraseCell2 d =
    let gne = GNE d
        gnh = GNH d
        stepF : Term
        stepF = ap1 (stepOf eraseAp1Cell eraseAp2Cell) (opkg d)
        cellRHS : Term
        cellRHS = tmAp2 (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d))
                        (ap1 (lookupAt mc_mbIdx) (opkg d))
        opTag2 : Deriv (imp gne (imp gnh (eqF (ap1 get_tag (opkg d)) (ap1 Fst d))))
        opTag2 = ap2c (lift2 gne gnh (op_tag_imp d)) (get2a gne gnh)
        negGetTag1 : Deriv (imp gne (imp gnh (neg (eqF (ap1 get_tag (opkg d)) (natCode 1)))))
        negGetTag1 =
          ap2c (ap2c (lift2 gne gnh (negEqTransport (ap1 get_tag (opkg d)) (ap1 Fst d) 1)) opTag2)
               (get2b gne gnh)
        unfold2 : Deriv (imp gne (imp gnh (eqF (ap1 erase d) stepF)))
        unfold2 = ap2c (lift2 gne gnh (opUnfold_imp d)) (get2a gne gnh)
        negGT1 : Formula
        negGT1 = neg (eqF (ap1 get_tag (opkg d)) (natCode 1))
        testFO : Formula
        testFO = eqF (ap1 (C natEqF get_tag (constN 1)) (opkg d)) O
        testO2 : Deriv (imp gne (imp gnh testFO))
        testO2 = ap2c (lift2 gne gnh
                        (natEqSkipNeg_imp negGT1 get_tag 1 (opkg d) (identP negGT1)))
                      negGetTag1
        skipFork2 : Deriv (imp gne (imp gnh (eqF stepF (ap1 eraseAp2Cell (opkg d)))))
        skipFork2 = ap2c (lift2 gne gnh
                          (fork_false_to_snd_imp testFO
                             eraseAp1Cell eraseAp2Cell test1 (opkg d) (identP testFO)))
                        testO2
        cellval : Deriv (eqF (ap1 eraseAp2Cell (opkg d)) cellRHS)
        cellval = mkAp2_val mc_f (lookupAt mc_maIdx) (lookupAt mc_mbIdx) (opkg d)
                    (ap1 mc_f (opkg d)) (ap1 (lookupAt mc_maIdx) (opkg d)) (ap1 (lookupAt mc_mbIdx) (opkg d))
                    (axRefl (ap1 mc_f (opkg d))) (axRefl (ap1 (lookupAt mc_maIdx) (opkg d)))
                    (axRefl (ap1 (lookupAt mc_mbIdx) (opkg d)))
    in trans2c (ap1 erase d) stepF cellRHS unfold2
         (trans2c stepF (ap1 eraseAp2Cell (opkg d)) cellRHS skipFork2 (lift2 gne gnh cellval))

  c2Fst : (d : Term) {a b : Term} ->
    Deriv (imp (GNE d) (imp (GNH d) (eqF a b))) ->
    Deriv (imp (GNE d) (imp (GNH d) (eqF (ap1 Fst a) (ap1 Fst b))))
  c2Fst d {a} {b} e = ap2c (lift2 (GNE d) (GNH d) (ax_eqCong1 Fst a b)) e

erasedHeadNe0_ap2_neg_obj : (d : Term) ->
  Deriv (imp (neg (eqF d O)) (imp (neg (eqF (ap1 Fst d) (natCode 1)))
             (neg (eqF (ap1 Fst (ap1 erase d)) (natCode 0)))))
erasedHeadNe0_ap2_neg_obj d =
  let cA = ap1 (lookupAt mc_maIdx) (opkg d)
      cB = ap1 (lookupAt mc_mbIdx) (opkg d)
      headI : Deriv (imp (GNE d) (imp (GNH d) (eqF (ap1 Fst (ap1 erase d)) (ap1 s (ap1 s O)))))
      headI = trans2c (ap1 Fst (ap1 erase d)) (ap1 Fst (tmAp2 (ap1 mc_f (opkg d)) cA cB)) (ap1 s (ap1 s O))
                (c2Fst d (eraseCell2 d))
                (lift2 (GNE d) (GNH d) (hd_tmAp2 (ap1 mc_f (opkg d)) cA cB))
  in ap2c (lift2 (GNE d) (GNH d) (neValSucc (ap1 Fst (ap1 erase d)) (ap1 s O))) headI

erasedBfunh_ap2_neg_obj : (d g a : Term) ->
  Deriv (imp (neg (eqF d O)) (imp (neg (eqF (ap1 Fst d) (natCode 1)))
             (eqF (ap1 bfunhF (tmAp2 g a (ap1 erase d))) (ap1 Fst (mFun d)))))
erasedBfunh_ap2_neg_obj d g a =
  let cA = ap1 (lookupAt mc_maIdx) (opkg d)
      cB = ap1 (lookupAt mc_mbIdx) (opkg d)
      gne = GNE d
      gnh = GNH d
      bslot : Deriv (imp gne (imp gnh
                (eqF (tmAp2 g a (ap1 erase d)) (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB)))))
      bslot = ap2c (lift2 gne gnh
                (ax_eqCongR Pair (ap2 Pair g (ap2 Pair a (ap1 erase d)))
                                 (ap2 Pair g (ap2 Pair a (tmAp2 (ap1 mc_f (opkg d)) cA cB))) tgAp2))
                (ap2c (lift2 gne gnh
                   (ax_eqCongR Pair (ap2 Pair a (ap1 erase d))
                                    (ap2 Pair a (tmAp2 (ap1 mc_f (opkg d)) cA cB)) g))
                   (ap2c (lift2 gne gnh
                      (ax_eqCongR Pair (ap1 erase d) (tmAp2 (ap1 mc_f (opkg d)) cA cB) a))
                      (eraseCell2 d)))
      bcong : Deriv (imp gne (imp gnh
                (eqF (ap1 bfunhF (tmAp2 g a (ap1 erase d)))
                     (ap1 bfunhF (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB))))))
      bcong = ap2c (lift2 gne gnh
                (ax_eqCong1 bfunhF (tmAp2 g a (ap1 erase d))
                            (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB)))) bslot
      mcfEq : Deriv (imp gne (imp gnh (eqF (ap1 Fst (ap1 mc_f (opkg d))) (ap1 Fst (mFun d)))))
      mcfEq = ap2c (lift2 gne gnh (ax_eqCong1 Fst (ap1 mc_f (opkg d)) (mFun d)))
                (ap2c (lift2 gne gnh (mc_f_imp d)) (get2a gne gnh))
  in trans2c (ap1 bfunhF (tmAp2 g a (ap1 erase d)))
       (ap1 bfunhF (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB))) (ap1 Fst (mFun d))
       bcong
       (trans2c (ap1 bfunhF (tmAp2 g a (tmAp2 (ap1 mc_f (opkg d)) cA cB)))
          (ap1 Fst (ap1 mc_f (opkg d))) (ap1 Fst (mFun d))
          (lift2 gne gnh (b2funh g a (ap1 mc_f (opkg d)) cA cB))
          mcfEq)
