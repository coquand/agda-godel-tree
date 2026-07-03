{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnResidualOpaque2Imp -- IMP-FORM (context-carrying) opaque residual
-- equations for the ap2 (tag = 2) node, the binary-node analog of
-- T4.FnResidualOpaqueImp, in the reordered ctx the inner funhead caseElim
-- delivers: funhead OUTERMOST, then flag, then tag.  Shape facts are carried as
-- imp-form ANTECEDENTS threaded through the residual fork cascade via
-- T4.ForkImp; the tag-independent cell value (fireVal) is impLift'd.
--
--   residual_op_ap2_flN_v_ctx3f (funhead 7 = v)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnResidualOpaque2Imp where

open import T4.Base

open import T4.OpaqueHarness using ( module HBase )
open import T4.ParsObj using ( stepOf ; test1 )
open import T4.ProgParse using ( get_tag )
open import T4.FnMark using ( mAp1 ; mAp2 ; flN ; flC ; mFun ; mMa ; mMb )
open import T4.FnMcontract using ( mc_fl )
open import T4.FnResidual
  using ( residual ; residualAp1Cell ; residualAp2Cell ; rAp2_flN ; rAp2_flC
        ; rR_flN ; rR_flC ; b_v_N ; b_v_C ; b_cong2 ; b_Rcong ; b_Rfire ; b_Rb ; b_Rs
        ; rB ; tst ; fork ; funhead ; mbhead ; mbfunhead )
open import T4.FnResidualOpaque
  using ( residual_unfold ; op_tag ; mc_fl_op ; funhead_op )
open import T4.FnResidualOpaque2 using ( fireVal ; congNVal ; rB_op ; mbhead_op ; bRbVal )

open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )
open import T4.ForkImp
  using ( natEqFire_imp ; natEqSkip_imp ; natEqSkipNeg_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )
open import BRA3.Logic     using ( prependEqLeft )
open import BRA3.Classical using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.CtxKit
  using ( lift3 ; get3a ; get3b ; get3c ; ap3c ; trans3c
        ; lift4 ; get4a ; get4b ; get4c ; get4d ; ap4c ; trans4c )

private
  nq : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  nq m k p = decideNatNeq m k p

open HBase Z (stepOf residualAp1Cell residualAp2Cell)

private
  -- imp H (funhead (opkg d) = natCode k)  from  imp H (Fst (mFun d) = natCode k).
  fhImp : (H : Formula) (d : Term) (k : Nat) -> Deriv (neg (eqF d O)) ->
    Deriv (imp H (eqF (ap1 Fst (mFun d)) (natCode k))) ->
    Deriv (imp H (eqF (ap1 funhead (opkg d)) (natCode k)))
  fhImp H d k ne hk =
    impEqTrans (ap1 funhead (opkg d)) (ap1 Fst (mFun d)) (natCode k)
      (impLift {H} (funhead_op d ne)) hk

  -- imp H (mbhead (opkg d) = natCode k)  from  imp H (Fst (mMb d) = natCode k).
  mbhImp : (H : Formula) (d : Term) (k : Nat) -> Deriv (neg (eqF d O)) ->
    Deriv (imp H (eqF (ap1 Fst (mMb d)) (natCode k))) ->
    Deriv (imp H (eqF (ap1 mbhead (opkg d)) (natCode k)))
  mbhImp H d k ne hk =
    impEqTrans (ap1 mbhead (opkg d)) (ap1 Fst (mMb d)) (natCode k)
      (impLift {H} (mbhead_op d ne)) hk

  -- neg-form funhead transport: neg (Fst (mFun d) = k) => neg (funhead (opkg d) = k).
  fhNegImp : (H : Formula) (d : Term) (k : Nat) -> Deriv (neg (eqF d O)) ->
    Deriv (imp H (neg (eqF (ap1 Fst (mFun d)) (natCode k)))) ->
    Deriv (imp H (neg (eqF (ap1 funhead (opkg d)) (natCode k))))
  fhNegImp H d k ne nk =
    compI nk
      (mp (axContrapos (eqF (ap1 funhead (opkg d)) (natCode k))
                       (eqF (ap1 Fst (mFun d)) (natCode k)))
          (prependEqLeft (ap1 Fst (mFun d)) (ap1 funhead (opkg d)) (natCode k)
             (ruleSym (funhead_op d ne))))

------------------------------------------------------------------------
-- ap2 flN v, order [funhead(=7), flag, tag].  Tag SKIPS to the ap2 cell, flag
-- fork FALSE to rAp2_flN, funhead fork FIRES 7 to b_v_N -> the flC-marked mask.

residual_op_ap2_flN_v_ctx3f : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (imp (eqF (ap1 Fst (mFun d)) (natCode 7))
        (imp (eqF (ap1 Fst (ap1 Snd d)) flN)
        (imp (eqF (ap1 Fst d) (natCode 2))
             (eqF (ap1 residual d)
                  (mAp2 flC (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d)))))))
residual_op_ap2_flN_v_ctx3f d ne =
  let Ga : Formula                                     -- funhead 7
      Ga = eqF (ap1 Fst (mFun d)) (natCode 7)
      Gb : Formula                                     -- flag flN
      Gb = eqF (ap1 Fst (ap1 Snd d)) flN
      Gc : Formula                                     -- tag 2
      Gc = eqF (ap1 Fst d) (natCode 2)
      rhsRes : Term
      rhsRes = mAp2 flC (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))
      sTag : Deriv (imp Gc (eqF (ap1 residual d) (ap1 residualAp2Cell (opkg d))))
      sTag = impEqTrans (ap1 residual d)
               (ap1 (stepOf residualAp1Cell residualAp2Cell) (opkg d))
               (ap1 residualAp2Cell (opkg d))
               (impLift {Gc} (residual_unfold d ne))
               (fork_false_to_snd_imp Gc residualAp1Cell residualAp2Cell test1 (opkg d)
                  (natEqSkip_imp Gc get_tag 2 1 (opkg d) (nq 2 1 (\ ()))
                     (impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2)
                        (impLift {Gc} (op_tag d ne)) (identP Gc))))
      sFlag : Deriv (imp Gb (eqF (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flN (opkg d))))
      sFlag = fork_false_to_snd_imp Gb rAp2_flC rAp2_flN mc_fl (opkg d)
                (impEqTrans (ap1 mc_fl (opkg d)) (ap1 Fst (ap1 Snd d)) O
                   (impLift {Gb} (mc_fl_op d ne)) (identP Gb))
      sFunh : Deriv (imp Ga (eqF (ap1 rAp2_flN (opkg d)) (ap1 b_v_N (opkg d))))
      sFunh = fork_true_to_fst_imp Ga b_v_N (fork rR_flN b_cong2 (tst funhead 8))
                (tst funhead 7) (opkg d)
                (natEqFire_imp Ga funhead 7 (opkg d) (fhImp Ga d 7 ne (identP Ga)))
  in trans3c (ap1 residual d) (ap1 residualAp2Cell (opkg d)) rhsRes
       (ap3c (lift3 Ga Gb Gc sTag) (get3c Ga Gb Gc))
       (trans3c (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flN (opkg d)) rhsRes
          (ap3c (lift3 Ga Gb Gc sFlag) (get3b Ga Gb Gc))
          (trans3c (ap1 rAp2_flN (opkg d)) (ap1 b_v_N (opkg d)) rhsRes
             (ap3c (lift3 Ga Gb Gc sFunh) (get3a Ga Gb Gc))
             (lift3 Ga Gb Gc (fireVal d ne))))

------------------------------------------------------------------------
-- ap2 flN cong, NEG-form, order [neg8, neg7, flag, tag].  The two funhead
-- negations are OUTERMOST (funhead caseElim else-branch); node stays flN and
-- residual folds to the mAp2 flN (mFun d)(res ma)(res mb) congruence (b_cong2).

residual_op_ap2_flN_cong_neg_ctx4f : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (imp (neg (eqF (ap1 Fst (mFun d)) (natCode 8)))
        (imp (neg (eqF (ap1 Fst (mFun d)) (natCode 7)))
        (imp (eqF (ap1 Fst (ap1 Snd d)) flN)
        (imp (eqF (ap1 Fst d) (natCode 2))
             (eqF (ap1 residual d)
                  (mAp2 flN (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))))))))
residual_op_ap2_flN_cong_neg_ctx4f d ne =
  let Ga : Formula                                     -- neg8
      Ga = neg (eqF (ap1 Fst (mFun d)) (natCode 8))
      Gb : Formula                                     -- neg7
      Gb = neg (eqF (ap1 Fst (mFun d)) (natCode 7))
      Gc : Formula                                     -- flag flN
      Gc = eqF (ap1 Fst (ap1 Snd d)) flN
      Gd : Formula                                     -- tag 2
      Gd = eqF (ap1 Fst d) (natCode 2)
      m8N : Fun1
      m8N = fork rR_flN b_cong2 (tst funhead 8)
      rhsRes : Term
      rhsRes = mAp2 flN (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))
      sTag : Deriv (imp Gd (eqF (ap1 residual d) (ap1 residualAp2Cell (opkg d))))
      sTag = impEqTrans (ap1 residual d)
               (ap1 (stepOf residualAp1Cell residualAp2Cell) (opkg d))
               (ap1 residualAp2Cell (opkg d))
               (impLift {Gd} (residual_unfold d ne))
               (fork_false_to_snd_imp Gd residualAp1Cell residualAp2Cell test1 (opkg d)
                  (natEqSkip_imp Gd get_tag 2 1 (opkg d) (nq 2 1 (\ ()))
                     (impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2)
                        (impLift {Gd} (op_tag d ne)) (identP Gd))))
      sFlag : Deriv (imp Gc (eqF (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flN (opkg d))))
      sFlag = fork_false_to_snd_imp Gc rAp2_flC rAp2_flN mc_fl (opkg d)
                (impEqTrans (ap1 mc_fl (opkg d)) (ap1 Fst (ap1 Snd d)) O
                   (impLift {Gc} (mc_fl_op d ne)) (identP Gc))
      s7 : Deriv (imp Gb (eqF (ap1 rAp2_flN (opkg d)) (ap1 m8N (opkg d))))
      s7 = fork_false_to_snd_imp Gb b_v_N m8N (tst funhead 7) (opkg d)
             (natEqSkipNeg_imp Gb funhead 7 (opkg d) (fhNegImp Gb d 7 ne (identP Gb)))
      s8 : Deriv (imp Ga (eqF (ap1 m8N (opkg d)) (ap1 b_cong2 (opkg d))))
      s8 = fork_false_to_snd_imp Ga rR_flN b_cong2 (tst funhead 8) (opkg d)
             (natEqSkipNeg_imp Ga funhead 8 (opkg d) (fhNegImp Ga d 8 ne (identP Ga)))
  in trans4c (ap1 residual d) (ap1 residualAp2Cell (opkg d)) rhsRes
       (ap4c (lift4 Ga Gb Gc Gd sTag) (get4d Ga Gb Gc Gd))
       (trans4c (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flN (opkg d)) rhsRes
          (ap4c (lift4 Ga Gb Gc Gd sFlag) (get4c Ga Gb Gc Gd))
          (trans4c (ap1 rAp2_flN (opkg d)) (ap1 b_cong2 (opkg d)) rhsRes
             (trans4c (ap1 rAp2_flN (opkg d)) (ap1 m8N (opkg d)) (ap1 b_cong2 (opkg d))
                (ap4c (lift4 Ga Gb Gc Gd s7) (get4b Ga Gb Gc Gd))
                (ap4c (lift4 Ga Gb Gc Gd s8) (get4a Ga Gb Gc Gd)))
             (lift4 Ga Gb Gc Gd (congNVal d ne))))

------------------------------------------------------------------------
-- SECTION flC.  The flC-branch chains: flag flC is DERIVED in the leaf (not a
-- caseElim antecedent), so these are bare imp-CHAINS applied via ap-c.  The flag
-- fork FIRES (fork_true, mc_fl = flC = s O) to rAp2_flC.

-- ap2 flC v (funhead 7):  residual d = residual (mMb d)  (b_v_C = rB).
residual_op_ap2_flC_v_chain : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (imp (eqF (ap1 Fst d) (natCode 2))
        (imp (eqF (ap1 Fst (ap1 Snd d)) flC)
        (imp (eqF (ap1 Fst (mFun d)) (natCode 7))
             (eqF (ap1 residual d) (ap1 residual (mMb d))))))
residual_op_ap2_flC_v_chain d ne =
  let Ga : Formula                                     -- tag 2
      Ga = eqF (ap1 Fst d) (natCode 2)
      Gb : Formula                                     -- flC flag
      Gb = eqF (ap1 Fst (ap1 Snd d)) flC
      Gc : Formula                                     -- funhead 7
      Gc = eqF (ap1 Fst (mFun d)) (natCode 7)
      m8C : Fun1
      m8C = fork rR_flC b_Rcong (tst funhead 8)
      sTag : Deriv (imp Ga (eqF (ap1 residual d) (ap1 residualAp2Cell (opkg d))))
      sTag = impEqTrans (ap1 residual d)
               (ap1 (stepOf residualAp1Cell residualAp2Cell) (opkg d))
               (ap1 residualAp2Cell (opkg d))
               (impLift {Ga} (residual_unfold d ne))
               (fork_false_to_snd_imp Ga residualAp1Cell residualAp2Cell test1 (opkg d)
                  (natEqSkip_imp Ga get_tag 2 1 (opkg d) (nq 2 1 (\ ()))
                     (impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2)
                        (impLift {Ga} (op_tag d ne)) (identP Ga))))
      sFlag : Deriv (imp Gb (eqF (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flC (opkg d))))
      sFlag = fork_true_to_fst_imp Gb rAp2_flC rAp2_flN mc_fl (opkg d)
                (impEqTrans (ap1 mc_fl (opkg d)) (ap1 Fst (ap1 Snd d)) (ap1 s O)
                   (impLift {Gb} (mc_fl_op d ne)) (identP Gb))
      sFunh : Deriv (imp Gc (eqF (ap1 rAp2_flC (opkg d)) (ap1 b_v_C (opkg d))))
      sFunh = fork_true_to_fst_imp Gc b_v_C m8C (tst funhead 7) (opkg d)
                (natEqFire_imp Gc funhead 7 (opkg d) (fhImp Gc d 7 ne (identP Gc)))
  in trans3c (ap1 residual d) (ap1 residualAp2Cell (opkg d)) (ap1 residual (mMb d))
       (ap3c (lift3 Ga Gb Gc sTag) (get3a Ga Gb Gc))
       (trans3c (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flC (opkg d)) (ap1 residual (mMb d))
          (ap3c (lift3 Ga Gb Gc sFlag) (get3b Ga Gb Gc))
          (trans3c (ap1 rAp2_flC (opkg d)) (ap1 b_v_C (opkg d)) (ap1 residual (mMb d))
             (ap3c (lift3 Ga Gb Gc sFunh) (get3c Ga Gb Gc))
             (lift3 Ga Gb Gc (rB_op d ne))))

-- ap2 flC cong (funhead notin {7,8}):  residual d = mAp2 flN (mFun d)(res ma)(res mb)
-- (b_Rcong = b_cong2 cell, congNVal).  Chain order [tag, flC, neg7, neg8].
residual_op_ap2_flC_cong_neg_chain : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (imp (eqF (ap1 Fst d) (natCode 2))
        (imp (eqF (ap1 Fst (ap1 Snd d)) flC)
        (imp (neg (eqF (ap1 Fst (mFun d)) (natCode 7)))
        (imp (neg (eqF (ap1 Fst (mFun d)) (natCode 8)))
             (eqF (ap1 residual d)
                  (mAp2 flN (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))))))))
residual_op_ap2_flC_cong_neg_chain d ne =
  let Ga : Formula                                     -- tag 2
      Ga = eqF (ap1 Fst d) (natCode 2)
      Gb : Formula                                     -- flC flag
      Gb = eqF (ap1 Fst (ap1 Snd d)) flC
      Gc : Formula                                     -- neg7
      Gc = neg (eqF (ap1 Fst (mFun d)) (natCode 7))
      Gd : Formula                                     -- neg8
      Gd = neg (eqF (ap1 Fst (mFun d)) (natCode 8))
      m8C : Fun1
      m8C = fork rR_flC b_Rcong (tst funhead 8)
      rhsRes : Term
      rhsRes = mAp2 flN (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))
      sTag : Deriv (imp Ga (eqF (ap1 residual d) (ap1 residualAp2Cell (opkg d))))
      sTag = impEqTrans (ap1 residual d)
               (ap1 (stepOf residualAp1Cell residualAp2Cell) (opkg d))
               (ap1 residualAp2Cell (opkg d))
               (impLift {Ga} (residual_unfold d ne))
               (fork_false_to_snd_imp Ga residualAp1Cell residualAp2Cell test1 (opkg d)
                  (natEqSkip_imp Ga get_tag 2 1 (opkg d) (nq 2 1 (\ ()))
                     (impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2)
                        (impLift {Ga} (op_tag d ne)) (identP Ga))))
      sFlag : Deriv (imp Gb (eqF (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flC (opkg d))))
      sFlag = fork_true_to_fst_imp Gb rAp2_flC rAp2_flN mc_fl (opkg d)
                (impEqTrans (ap1 mc_fl (opkg d)) (ap1 Fst (ap1 Snd d)) (ap1 s O)
                   (impLift {Gb} (mc_fl_op d ne)) (identP Gb))
      s7 : Deriv (imp Gc (eqF (ap1 rAp2_flC (opkg d)) (ap1 m8C (opkg d))))
      s7 = fork_false_to_snd_imp Gc b_v_C m8C (tst funhead 7) (opkg d)
             (natEqSkipNeg_imp Gc funhead 7 (opkg d) (fhNegImp Gc d 7 ne (identP Gc)))
      s8 : Deriv (imp Gd (eqF (ap1 m8C (opkg d)) (ap1 b_Rcong (opkg d))))
      s8 = fork_false_to_snd_imp Gd rR_flC b_Rcong (tst funhead 8) (opkg d)
             (natEqSkipNeg_imp Gd funhead 8 (opkg d) (fhNegImp Gd d 8 ne (identP Gd)))
  in trans4c (ap1 residual d) (ap1 residualAp2Cell (opkg d)) rhsRes
       (ap4c (lift4 Ga Gb Gc Gd sTag) (get4a Ga Gb Gc Gd))
       (trans4c (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flC (opkg d)) rhsRes
          (ap4c (lift4 Ga Gb Gc Gd sFlag) (get4b Ga Gb Gc Gd))
          (trans4c (ap1 rAp2_flC (opkg d)) (ap1 b_Rcong (opkg d)) rhsRes
             (trans4c (ap1 rAp2_flC (opkg d)) (ap1 m8C (opkg d)) (ap1 b_Rcong (opkg d))
                (ap4c (lift4 Ga Gb Gc Gd s7) (get4c Ga Gb Gc Gd))
                (ap4c (lift4 Ga Gb Gc Gd s8) (get4d Ga Gb Gc Gd)))
             (lift4 Ga Gb Gc Gd (congNVal d ne))))

------------------------------------------------------------------------
-- SECTION R.  the Rb chains (fun-head 8, mb-head 0), order threading the
-- extra mb-head antecedent.  The flN residual RHS is the SAME flC-marked mask
-- as v (mAp2 flC (mFun d)(res ma)(res mb)); the flC residual folds to the Rb
-- projection mAp1 flN (Fst(Snd(mFun d)))(res ma) (bRbVal).

-- flN Rb, order [funhead(=8), mbhead(=0), flag, tag].
residual_op_ap2_flN_Rb_ctx4f : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (imp (eqF (ap1 Fst (mFun d)) (natCode 8))
        (imp (eqF (ap1 Fst (mMb d)) (natCode 0))
        (imp (eqF (ap1 Fst (ap1 Snd d)) flN)
        (imp (eqF (ap1 Fst d) (natCode 2))
             (eqF (ap1 residual d)
                  (mAp2 flC (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))))))))
residual_op_ap2_flN_Rb_ctx4f d ne =
  let Ga : Formula                                     -- funhead 8
      Ga = eqF (ap1 Fst (mFun d)) (natCode 8)
      Gb : Formula                                     -- mbhead 0
      Gb = eqF (ap1 Fst (mMb d)) (natCode 0)
      Gc : Formula                                     -- flag flN
      Gc = eqF (ap1 Fst (ap1 Snd d)) flN
      Gd : Formula                                     -- tag 2
      Gd = eqF (ap1 Fst d) (natCode 2)
      m8N : Fun1
      m8N = fork rR_flN b_cong2 (tst funhead 8)
      rRfk : Fun1
      rRfk = fork b_Rfire b_cong2 (tst mbfunhead 3)
      rhsRes : Term
      rhsRes = mAp2 flC (mFun d) (ap1 residual (mMa d)) (ap1 residual (mMb d))
      sTag : Deriv (imp Gd (eqF (ap1 residual d) (ap1 residualAp2Cell (opkg d))))
      sTag = impEqTrans (ap1 residual d)
               (ap1 (stepOf residualAp1Cell residualAp2Cell) (opkg d))
               (ap1 residualAp2Cell (opkg d))
               (impLift {Gd} (residual_unfold d ne))
               (fork_false_to_snd_imp Gd residualAp1Cell residualAp2Cell test1 (opkg d)
                  (natEqSkip_imp Gd get_tag 2 1 (opkg d) (nq 2 1 (\ ()))
                     (impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2)
                        (impLift {Gd} (op_tag d ne)) (identP Gd))))
      sFlag : Deriv (imp Gc (eqF (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flN (opkg d))))
      sFlag = fork_false_to_snd_imp Gc rAp2_flC rAp2_flN mc_fl (opkg d)
                (impEqTrans (ap1 mc_fl (opkg d)) (ap1 Fst (ap1 Snd d)) O
                   (impLift {Gc} (mc_fl_op d ne)) (identP Gc))
      s7 : Deriv (imp Ga (eqF (ap1 rAp2_flN (opkg d)) (ap1 m8N (opkg d))))
      s7 = fork_false_to_snd_imp Ga b_v_N m8N (tst funhead 7) (opkg d)
             (natEqSkip_imp Ga funhead 8 7 (opkg d) (nq 8 7 (\ ())) (fhImp Ga d 8 ne (identP Ga)))
      s8 : Deriv (imp Ga (eqF (ap1 m8N (opkg d)) (ap1 rR_flN (opkg d))))
      s8 = fork_true_to_fst_imp Ga rR_flN b_cong2 (tst funhead 8) (opkg d)
             (natEqFire_imp Ga funhead 8 (opkg d) (fhImp Ga d 8 ne (identP Ga)))
      smb0 : Deriv (imp Gb (eqF (ap1 rR_flN (opkg d)) (ap1 b_v_N (opkg d))))
      smb0 = fork_true_to_fst_imp Gb b_Rfire rRfk (tst mbhead 0) (opkg d)
               (natEqFire_imp Gb mbhead 0 (opkg d) (mbhImp Gb d 0 ne (identP Gb)))
  in trans4c (ap1 residual d) (ap1 residualAp2Cell (opkg d)) rhsRes
       (ap4c (lift4 Ga Gb Gc Gd sTag) (get4d Ga Gb Gc Gd))
       (trans4c (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flN (opkg d)) rhsRes
          (ap4c (lift4 Ga Gb Gc Gd sFlag) (get4c Ga Gb Gc Gd))
          (trans4c (ap1 rAp2_flN (opkg d)) (ap1 rR_flN (opkg d)) rhsRes
             (trans4c (ap1 rAp2_flN (opkg d)) (ap1 m8N (opkg d)) (ap1 rR_flN (opkg d))
                (ap4c (lift4 Ga Gb Gc Gd s7) (get4a Ga Gb Gc Gd))
                (ap4c (lift4 Ga Gb Gc Gd s8) (get4a Ga Gb Gc Gd)))
             (trans4c (ap1 rR_flN (opkg d)) (ap1 b_v_N (opkg d)) rhsRes
                (ap4c (lift4 Ga Gb Gc Gd smb0) (get4b Ga Gb Gc Gd))
                (lift4 Ga Gb Gc Gd (fireVal d ne)))))

-- flC Rb, order [tag, flC, funhead(=8), mbhead(=0)] -> mAp1 flN g0 (res ma).
residual_op_ap2_flC_Rb_chain : (d : Term) -> Deriv (neg (eqF d O)) ->
  Deriv (imp (eqF (ap1 Fst d) (natCode 2))
        (imp (eqF (ap1 Fst (ap1 Snd d)) flC)
        (imp (eqF (ap1 Fst (mFun d)) (natCode 8))
        (imp (eqF (ap1 Fst (mMb d)) (natCode 0))
             (eqF (ap1 residual d)
                  (mAp1 flN (ap1 Fst (ap1 Snd (mFun d))) (ap1 residual (mMa d))))))))
residual_op_ap2_flC_Rb_chain d ne =
  let Ga : Formula                                     -- tag 2
      Ga = eqF (ap1 Fst d) (natCode 2)
      Gb : Formula                                     -- flC flag
      Gb = eqF (ap1 Fst (ap1 Snd d)) flC
      Gc : Formula                                     -- funhead 8
      Gc = eqF (ap1 Fst (mFun d)) (natCode 8)
      Gd : Formula                                     -- mbhead 0
      Gd = eqF (ap1 Fst (mMb d)) (natCode 0)
      m8C : Fun1
      m8C = fork rR_flC b_Rcong (tst funhead 8)
      rRfk : Fun1
      rRfk = fork b_Rs b_Rcong (tst mbfunhead 3)
      rhsRes : Term
      rhsRes = mAp1 flN (ap1 Fst (ap1 Snd (mFun d))) (ap1 residual (mMa d))
      sTag : Deriv (imp Ga (eqF (ap1 residual d) (ap1 residualAp2Cell (opkg d))))
      sTag = impEqTrans (ap1 residual d)
               (ap1 (stepOf residualAp1Cell residualAp2Cell) (opkg d))
               (ap1 residualAp2Cell (opkg d))
               (impLift {Ga} (residual_unfold d ne))
               (fork_false_to_snd_imp Ga residualAp1Cell residualAp2Cell test1 (opkg d)
                  (natEqSkip_imp Ga get_tag 2 1 (opkg d) (nq 2 1 (\ ()))
                     (impEqTrans (ap1 get_tag (opkg d)) (ap1 Fst d) (natCode 2)
                        (impLift {Ga} (op_tag d ne)) (identP Ga))))
      sFlag : Deriv (imp Gb (eqF (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flC (opkg d))))
      sFlag = fork_true_to_fst_imp Gb rAp2_flC rAp2_flN mc_fl (opkg d)
                (impEqTrans (ap1 mc_fl (opkg d)) (ap1 Fst (ap1 Snd d)) (ap1 s O)
                   (impLift {Gb} (mc_fl_op d ne)) (identP Gb))
      s7 : Deriv (imp Gc (eqF (ap1 rAp2_flC (opkg d)) (ap1 m8C (opkg d))))
      s7 = fork_false_to_snd_imp Gc b_v_C m8C (tst funhead 7) (opkg d)
             (natEqSkip_imp Gc funhead 8 7 (opkg d) (nq 8 7 (\ ())) (fhImp Gc d 8 ne (identP Gc)))
      s8 : Deriv (imp Gc (eqF (ap1 m8C (opkg d)) (ap1 rR_flC (opkg d))))
      s8 = fork_true_to_fst_imp Gc rR_flC b_Rcong (tst funhead 8) (opkg d)
             (natEqFire_imp Gc funhead 8 (opkg d) (fhImp Gc d 8 ne (identP Gc)))
      smb0 : Deriv (imp Gd (eqF (ap1 rR_flC (opkg d)) (ap1 b_Rb (opkg d))))
      smb0 = fork_true_to_fst_imp Gd b_Rb rRfk (tst mbhead 0) (opkg d)
               (natEqFire_imp Gd mbhead 0 (opkg d) (mbhImp Gd d 0 ne (identP Gd)))
  in trans4c (ap1 residual d) (ap1 residualAp2Cell (opkg d)) rhsRes
       (ap4c (lift4 Ga Gb Gc Gd sTag) (get4a Ga Gb Gc Gd))
       (trans4c (ap1 residualAp2Cell (opkg d)) (ap1 rAp2_flC (opkg d)) rhsRes
          (ap4c (lift4 Ga Gb Gc Gd sFlag) (get4b Ga Gb Gc Gd))
          (trans4c (ap1 rAp2_flC (opkg d)) (ap1 rR_flC (opkg d)) rhsRes
             (trans4c (ap1 rAp2_flC (opkg d)) (ap1 m8C (opkg d)) (ap1 rR_flC (opkg d))
                (ap4c (lift4 Ga Gb Gc Gd s7) (get4c Ga Gb Gc Gd))
                (ap4c (lift4 Ga Gb Gc Gd s8) (get4c Ga Gb Gc Gd)))
             (trans4c (ap1 rR_flC (opkg d)) (ap1 b_Rb (opkg d)) rhsRes
                (ap4c (lift4 Ga Gb Gc Gd smb0) (get4d Ga Gb Gc Gd))
                (lift4 Ga Gb Gc Gd (bRbVal d ne)))))
