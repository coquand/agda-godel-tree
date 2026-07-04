{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnGlueAp2RcongHelpers -- IMP-FORM, NEG-antecedent twin of the ap2 R-CONGRUENCE
-- redex-test  T4.FnTerm.redex_ap2_Rcong: the erased R-node  tmAp2 g a b  is NOT a
-- redex (redexHere = O) when the fun-head is 8 but the erased recursion arg b is
-- NEITHER base-headed (Fst b /= 0, i.e. not Rb) NOR s-headed (bfunhF /= 3, i.e.
-- not Rs).  Unlike the bare version this carries the two "not Rb / not Rs"
-- conditions as NEGATIONS threaded under H (no concrete head values), which is
-- what the object dispatch's mb-caseElim else-branch delivers.
--
--   redex_ap2_Rcong_neg_imp :
--     imp H (Fst g = 8) -> imp H (neg (Fst b = 0)) ->
--     imp H (neg (bfunhF (tmAp2 g a b) = 3)) ->
--     imp H (redexHere (tmAp2 g a b) = O)
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnGlueAp2RcongHelpers where

open import T4.Base

open import T4.PrCodeObj using ( tmAp2 ; hd_tmAp2 )
open import T4.PrDev using ( idxTest_fire ; idxTest_skip )
open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )
open import T4.FnTerm
  using ( funhF ; funhF_ap2 ; bhF ; bhF_ap2 ; bfunhF ; trueB ; falseB ; rRest ; rRest1
        ; ap1res ; ap2res ; ap2rest1 ; restTop ; tst ; redexHere )

open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )
open import T4.ForkImp
  using ( natEqFire_imp ; natEqSkip_imp ; natEqSkipNeg_imp
        ; fork_true_to_fst_imp ; fork_false_to_snd_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans )
open import BRA3.Logic     using ( prependEqLeft )
open import BRA3.Classical using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; identP )

private
  nq : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  nq m k p = decideNatNeq m k p

  -- neg (Fst b = 0)  =>  neg (bhF (tmAp2 g a b) = 0) , under H.
  negBh_imp : (H : Formula) (g a b : Term) ->
    Deriv (imp H (neg (eqF (ap1 Fst b) (natCode 0)))) ->
    Deriv (imp H (neg (eqF (ap1 bhF (tmAp2 g a b)) (natCode 0))))
  negBh_imp H g a b nb =
    compI nb
      (mp (axContrapos (eqF (ap1 bhF (tmAp2 g a b)) (natCode 0)) (eqF (ap1 Fst b) (natCode 0)))
          (prependEqLeft (ap1 Fst b) (ap1 bhF (tmAp2 g a b)) (natCode 0)
             (ruleSym (bhF_ap2 g a b))))

redex_ap2_Rcong_neg_imp : (H : Formula) (g a b : Term) ->
  Deriv (imp H (eqF (ap1 Fst g) (natCode 8))) ->
  Deriv (imp H (neg (eqF (ap1 Fst b) (natCode 0)))) ->
  Deriv (imp H (neg (eqF (ap1 bfunhF (tmAp2 g a b)) (natCode 3)))) ->
  Deriv (imp H (eqF (ap1 redexHere (tmAp2 g a b)) O))
redex_ap2_Rcong_neg_imp H g a b hkI nbh0 nbf3 =
  let input = tmAp2 g a b
      v8I : Deriv (imp H (eqF (ap1 funhF input) (natCode 8)))
      v8I = impEqTrans (ap1 funhF input) (ap1 Fst g) (natCode 8)
              (impLift {H} (funhF_ap2 g a b)) hkI
      headPart : Deriv (eqF (ap1 redexHere input) (ap1 ap2res input))
      headPart = ruleTrans (fork_false_to_snd ap1res restTop (tst Fst 1) input
                              (idxTest_skip Fst 2 1 input (nq 2 1 (\ ())) (hd_tmAp2 g a b)))
                           (fork_true_to_fst ap2res falseB (tst Fst 2) input
                              (idxTest_fire Fst 2 input (hd_tmAp2 g a b)))
  in impEqTrans (ap1 redexHere input) (ap1 ap2res input) O
       (impLift {H} headPart)
       (impEqTrans (ap1 ap2res input) (ap1 ap2rest1 input) O
          (fork_false_to_snd_imp H trueB ap2rest1 (tst funhF 7) input
             (natEqSkip_imp H funhF 8 7 input (nq 8 7 (\ ())) v8I))
          (impEqTrans (ap1 ap2rest1 input) (ap1 rRest input) O
             (fork_true_to_fst_imp H rRest falseB (tst funhF 8) input
                (natEqFire_imp H funhF 8 input v8I))
             (impEqTrans (ap1 rRest input) (ap1 rRest1 input) O
                (fork_false_to_snd_imp H trueB rRest1 (tst bhF 0) input
                   (natEqSkipNeg_imp H bhF 0 input (negBh_imp H g a b nbh0)))
                (impEqTrans (ap1 rRest1 input) (ap1 falseB input) O
                   (fork_false_to_snd_imp H trueB falseB (tst bfunhF 3) input
                      (natEqSkipNeg_imp H bfunhF 3 input nbf3))
                   (impLift {H} (constN_eq 0 input))))))

------------------------------------------------------------------------
-- ctx-3 OBJECT form (for lift+ap into a leaf context): the three antecedents
-- [Fst g = 8, neg (Fst b = 0), neg (bfunhF (tmAp2 g a b) = 3)] nested.

open import T4.CtxKit using ( lift3 ; get3a ; get3b ; get3c ; ap3c ; trans3c )

redex_ap2_Rcong_neg_ctx3 : (g a b : Term) ->
  Deriv (imp (eqF (ap1 Fst g) (natCode 8))
        (imp (neg (eqF (ap1 Fst b) (natCode 0)))
        (imp (neg (eqF (ap1 bfunhF (tmAp2 g a b)) (natCode 3)))
             (eqF (ap1 redexHere (tmAp2 g a b)) O))))
redex_ap2_Rcong_neg_ctx3 g a b =
  let input = tmAp2 g a b
      Ga : Formula
      Ga = eqF (ap1 Fst g) (natCode 8)
      Gb : Formula
      Gb = neg (eqF (ap1 Fst b) (natCode 0))
      Gc : Formula
      Gc = neg (eqF (ap1 bfunhF input) (natCode 3))
      v8I : Deriv (imp Ga (eqF (ap1 funhF input) (natCode 8)))
      v8I = impEqTrans (ap1 funhF input) (ap1 Fst g) (natCode 8)
              (impLift {Ga} (funhF_ap2 g a b)) (identP Ga)
      headPart : Deriv (eqF (ap1 redexHere input) (ap1 ap2res input))
      headPart = ruleTrans (fork_false_to_snd ap1res restTop (tst Fst 1) input
                              (idxTest_skip Fst 2 1 input (nq 2 1 (\ ())) (hd_tmAp2 g a b)))
                           (fork_true_to_fst ap2res falseB (tst Fst 2) input
                              (idxTest_fire Fst 2 input (hd_tmAp2 g a b)))
      skip7 : Deriv (imp Ga (eqF (ap1 ap2res input) (ap1 ap2rest1 input)))
      skip7 = fork_false_to_snd_imp Ga trueB ap2rest1 (tst funhF 7) input
                (natEqSkip_imp Ga funhF 8 7 input (nq 8 7 (\ ())) v8I)
      fire8 : Deriv (imp Ga (eqF (ap1 ap2rest1 input) (ap1 rRest input)))
      fire8 = fork_true_to_fst_imp Ga rRest falseB (tst funhF 8) input
                (natEqFire_imp Ga funhF 8 input v8I)
      skipBh : Deriv (imp Gb (eqF (ap1 rRest input) (ap1 rRest1 input)))
      skipBh = fork_false_to_snd_imp Gb trueB rRest1 (tst bhF 0) input
                 (natEqSkipNeg_imp Gb bhF 0 input (negBh_imp Gb g a b (identP Gb)))
      skipBf : Deriv (imp Gc (eqF (ap1 rRest1 input) (ap1 falseB input)))
      skipBf = fork_false_to_snd_imp Gc trueB falseB (tst bfunhF 3) input
                 (natEqSkipNeg_imp Gc bfunhF 3 input (identP Gc))
  in trans3c (ap1 redexHere input) (ap1 ap2res input) O
       (lift3 Ga Gb Gc headPart)
       (trans3c (ap1 ap2res input) (ap1 ap2rest1 input) O
          (ap3c (lift3 Ga Gb Gc skip7) (get3a Ga Gb Gc))
          (trans3c (ap1 ap2rest1 input) (ap1 rRest input) O
             (ap3c (lift3 Ga Gb Gc fire8) (get3a Ga Gb Gc))
             (trans3c (ap1 rRest input) (ap1 rRest1 input) O
                (ap3c (lift3 Ga Gb Gc skipBh) (get3b Ga Gb Gc))
                (trans3c (ap1 rRest1 input) (ap1 falseB input) O
                   (ap3c (lift3 Ga Gb Gc skipBf) (get3c Ga Gb Gc))
                   (lift3 Ga Gb Gc (constN_eq 0 input))))))
