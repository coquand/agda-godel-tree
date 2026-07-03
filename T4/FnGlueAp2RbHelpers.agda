{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnGlueAp2RbHelpers -- IMP-FORM (context-carrying) twins of the ap2-Rb
-- redex-test / contract / mcontract equations, the fun-head-8 (R base case)
-- analogs of the ap2-v twins in T4.FnRedexContractImp2 / T4.FnMcontractImp2.
-- The recursion arg is the LITERAL tmO (the mbhead-0 base case), so the
-- redex/contract cascades fire  funhF 7 skip -> funhF 8 fire -> bhF 0 fire ; the
-- funhead-8 fact hk (Fst g = natCode 8) is carried as an ANTECEDENT  imp H (...) ;
-- the bhF-0 fire and the co_Rb cell value are tag-independent (impLift).
--
--   redex_ap2_Rb_imp     : imp H (Fst g = 8) -> imp H (redexHere (tmAp2 g a tmO) = natCode 1)
--   contract_Rb_imp      : imp H (Fst g = 8) -> imp H (contract (tmAp2 g a tmO) = tmAp1 (Fst (Snd g)) a)
--   mcontract_ap2_Rb_imp : imp H (Fst g = 8) -> imp H (mcontract mb = tmO) ->
--        imp H (mcontract (mAp2 flC g ma mb) = tmAp1 (Fst (Snd g)) (mcontract ma))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnGlueAp2RbHelpers where

open import T4.Base

open import T4.PrCodeObj using ( tmO ; tmAp1 ; tmAp2 ; tgAp2 ; hd_tmO ; hd_tmAp2 )
open import T4.PrDev using ( idxTest_fire ; mkAp1_val )
open import T4.DerSrc using ( fork_true_to_fst )
open import T4.FnMark using ( mAp2 ; flC )
open import T4.FnMcontract using ( mcontract )
open import T4.FnTerm
  using ( redexHere ; funhF ; bhF ; funhF_ap2 ; bhF_ap2 ; funF ; funF_ap2
        ; trueB ; falseB ; rRest ; rRest1 ; ap1res ; ap2res ; ap2rest1 ; restTop ; tst )
open import T4.FnContract
  using ( contract ; gP ; aP ; aP_ap2
        ; co_ap1res ; co_restTop ; co_ap2res ; co_v ; co_ap2rest1
        ; co_rRest ; co_rRest1 ; co_Rb )
open import T4.FnMcontractImp2 using ( mcontract_ap2_redex_imp )

open import BRA3.PairAlgebra using ( I ; compose1U ; compose1U_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )
open import T4.PrDev using ( idxTest_skip )
open import T4.DerSrc using ( fork_false_to_snd )
open import T4.ForkImp
  using ( natEqFire_imp ; natEqSkip_imp ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 ; impCongR )

private
  nq : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  nq m k p = decideNatNeq m k p

  -- opaque gP on an ap2 node (rebuild of the private FnGlueRHelpers.gP_op2).
  gP_op2 : (f a b : Term) -> Deriv (eqF (ap1 gP (tmAp2 f a b)) (ap1 Fst (ap1 Snd f)))
  gP_op2 f a b =
    ruleTrans (compose1U_eq Fst (compose1U Snd funF) (tmAp2 f a b))
      (cong1 Fst
        (ruleTrans (compose1U_eq Snd funF (tmAp2 f a b)) (cong1 Snd (funF_ap2 f a b))))

------------------------------------------------------------------------
-- redex-test:  redexHere (tmAp2 g a tmO) = natCode 1 , under H.

redex_ap2_Rb_imp : (H : Formula) (g a : Term) ->
  Deriv (imp H (eqF (ap1 Fst g) (natCode 8))) ->
  Deriv (imp H (eqF (ap1 redexHere (tmAp2 g a tmO)) (natCode 1)))
redex_ap2_Rb_imp H g a hkI =
  let input = tmAp2 g a tmO
      v8I : Deriv (imp H (eqF (ap1 funhF input) (natCode 8)))
      v8I = impEqTrans (ap1 funhF input) (ap1 Fst g) (natCode 8)
              (impLift {H} (funhF_ap2 g a tmO)) hkI
      vbh0 : Deriv (eqF (ap1 bhF input) (natCode 0))
      vbh0 = ruleTrans (bhF_ap2 g a tmO) hd_tmO
      headPart : Deriv (eqF (ap1 redexHere input) (ap1 ap2res input))
      headPart = ruleTrans (fork_false_to_snd ap1res restTop (tst Fst 1) input
                              (idxTest_skip Fst 2 1 input (nq 2 1 (\ ())) (hd_tmAp2 g a tmO)))
                           (fork_true_to_fst ap2res falseB (tst Fst 2) input
                              (idxTest_fire Fst 2 input (hd_tmAp2 g a tmO)))
  in impEqTrans (ap1 redexHere input) (ap1 ap2res input) (natCode 1)
       (impLift {H} headPart)
       (impEqTrans (ap1 ap2res input) (ap1 ap2rest1 input) (natCode 1)
          (fork_false_to_snd_imp H trueB ap2rest1 (tst funhF 7) input
             (natEqSkip_imp H funhF 8 7 input (nq 8 7 (\ ())) v8I))
          (impEqTrans (ap1 ap2rest1 input) (ap1 rRest input) (natCode 1)
             (fork_true_to_fst_imp H rRest falseB (tst funhF 8) input
                (natEqFire_imp H funhF 8 input v8I))
             (impEqTrans (ap1 rRest input) (ap1 trueB input) (natCode 1)
                (impLift {H} (fork_true_to_fst trueB rRest1 (tst bhF 0) input
                                (idxTest_fire bhF 0 input vbh0)))
                (impLift {H} (constN_eq 1 input)))))

------------------------------------------------------------------------
-- contract:  contract (tmAp2 g a tmO) = tmAp1 (Fst (Snd g)) a , under H.

contract_Rb_imp : (H : Formula) (g a : Term) ->
  Deriv (imp H (eqF (ap1 Fst g) (natCode 8))) ->
  Deriv (imp H (eqF (ap1 contract (tmAp2 g a tmO)) (tmAp1 (ap1 Fst (ap1 Snd g)) a)))
contract_Rb_imp H g a hkI =
  let input = tmAp2 g a tmO
      v8I : Deriv (imp H (eqF (ap1 funhF input) (natCode 8)))
      v8I = impEqTrans (ap1 funhF input) (ap1 Fst g) (natCode 8)
              (impLift {H} (funhF_ap2 g a tmO)) hkI
      vbh0 : Deriv (eqF (ap1 bhF input) (natCode 0))
      vbh0 = ruleTrans (bhF_ap2 g a tmO) hd_tmO
      valRb : Deriv (eqF (ap1 co_Rb input) (tmAp1 (ap1 Fst (ap1 Snd g)) a))
      valRb = mkAp1_val gP aP input (ap1 Fst (ap1 Snd g)) a (gP_op2 g a tmO) (aP_ap2 g a tmO)
      headPart : Deriv (eqF (ap1 contract input) (ap1 co_ap2res input))
      headPart = ruleTrans (fork_false_to_snd co_ap1res co_restTop (tst Fst 1) input
                              (idxTest_skip Fst 2 1 input (nq 2 1 (\ ())) (hd_tmAp2 g a tmO)))
                           (fork_true_to_fst co_ap2res I (tst Fst 2) input
                              (idxTest_fire Fst 2 input (hd_tmAp2 g a tmO)))
  in impEqTrans (ap1 contract input) (ap1 co_ap2res input) (tmAp1 (ap1 Fst (ap1 Snd g)) a)
       (impLift {H} headPart)
       (impEqTrans (ap1 co_ap2res input) (ap1 co_ap2rest1 input) (tmAp1 (ap1 Fst (ap1 Snd g)) a)
          (fork_false_to_snd_imp H co_v co_ap2rest1 (tst funhF 7) input
             (natEqSkip_imp H funhF 8 7 input (nq 8 7 (\ ())) v8I))
          (impEqTrans (ap1 co_ap2rest1 input) (ap1 co_rRest input) (tmAp1 (ap1 Fst (ap1 Snd g)) a)
             (fork_true_to_fst_imp H co_rRest I (tst funhF 8) input
                (natEqFire_imp H funhF 8 input v8I))
             (impEqTrans (ap1 co_rRest input) (ap1 co_Rb input) (tmAp1 (ap1 Fst (ap1 Snd g)) a)
                (impLift {H} (fork_true_to_fst co_Rb co_rRest1 (tst bhF 0) input
                                (idxTest_fire bhF 0 input vbh0)))
                (impLift {H} valRb))))

------------------------------------------------------------------------
-- mcontract of the flagged Rb node (mb collapses to tmO), under H.

private
  -- congruence on the 3rd tmAp2 argument, under H.
  tmAp2c3_imp : (H : Formula) (g A B B' : Term) ->
    Deriv (imp H (eqF B B')) ->
    Deriv (imp H (eqF (tmAp2 g A B) (tmAp2 g A B')))
  tmAp2c3_imp H g A B B' e =
    impCongR Pair (ap2 Pair g (ap2 Pair A B)) (ap2 Pair g (ap2 Pair A B')) tgAp2
      (impCongR Pair (ap2 Pair A B) (ap2 Pair A B') g
        (impCongR Pair B B' A e))

mcontract_ap2_Rb_imp : (H : Formula) (g ma mb : Term) ->
  Deriv (imp H (eqF (ap1 Fst g) (natCode 8))) ->
  Deriv (imp H (eqF (ap1 mcontract mb) tmO)) ->
  Deriv (imp H (eqF (ap1 mcontract (mAp2 flC g ma mb))
                    (tmAp1 (ap1 Fst (ap1 Snd g)) (ap1 mcontract ma))))
mcontract_ap2_Rb_imp H g ma mb hkI hbI =
  let A = ap1 mcontract ma
      B = ap1 mcontract mb
      nodeEqI : Deriv (imp H (eqF (tmAp2 g A B) (tmAp2 g A tmO)))
      nodeEqI = tmAp2c3_imp H g A B tmO hbI
      hredI : Deriv (imp H (eqF (ap1 redexHere (tmAp2 g A B)) (natCode 1)))
      hredI = impEqTrans (ap1 redexHere (tmAp2 g A B)) (ap1 redexHere (tmAp2 g A tmO)) (natCode 1)
                (impCong1 redexHere (tmAp2 g A B) (tmAp2 g A tmO) nodeEqI)
                (redex_ap2_Rb_imp H g A hkI)
  in impEqTrans (ap1 mcontract (mAp2 flC g ma mb))
       (ap1 contract (tmAp2 g A B)) (tmAp1 (ap1 Fst (ap1 Snd g)) A)
       (mcontract_ap2_redex_imp H g ma mb hredI)
       (impEqTrans (ap1 contract (tmAp2 g A B)) (ap1 contract (tmAp2 g A tmO))
          (tmAp1 (ap1 Fst (ap1 Snd g)) A)
          (impCong1 contract (tmAp2 g A B) (tmAp2 g A tmO) nodeEqI)
          (contract_Rb_imp H g A hkI))
