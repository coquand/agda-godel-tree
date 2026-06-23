{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ForkImp -- IMP-FORM (htag-carrying) cascade primitives, needed because the
-- object tag dispatch (caseElim on  dtag p = dgK ) exposes the tag equality as
-- an ANTECEDENT  H , not a bare Deriv (no deduction theorem).  These are the
-- one-level fork unfolds + testEq fire/skip with the recovered-label premise
-- carried under  H :
--
--   testEq_fire_imp : imp H (nIdx input = natCode k) -> imp H (testEq k input = s O)
--   testEq_skip_imp : (NatNeqWitness m k) ->
--                       imp H (nIdx input = natCode m) -> imp H (testEq k input = O)
--   fork_true_to_fst_imp : imp H (tst input = s O) -> imp H (body = A input)
--   fork_false_to_snd_imp: imp H (tst input = O)   -> imp H (body = B input)
--
-- Direct Carneiro transcription of the bare versions in T4.DerSrc.
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ForkImp where

open import T4.Base

open import T4.BinTree using ( nIdx )
open import T4.DerSrc  using ( testEq )

open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq )
open import BRA3.ChurchT116    using ( Snd )
open import BRA3.ChurchT117    using ( Fst )
open import BRA3.Church        using ( pi )
open import T4.NatEqReflect    using ( natEqF_complete )

open import T4.Thm12.ImpHelpers using ( impCongL ; impCongR ; impEqTrans ; impLift )
open import T4.ImpEq            using ( impMp )

------------------------------------------------------------------------
-- Generic natEqF-test fire / skip (label  lbl ), carried under H.

natEqFire_imp : (H : Formula) (lbl : Fun1) (k : Nat) (input : Term) ->
  Deriv (imp H (eqF (ap1 lbl input) (natCode k))) ->
  Deriv (imp H (eqF (ap1 (C natEqF lbl (constN k)) input) (ap1 s O)))
natEqFire_imp H lbl k input nieq =
  let t0 : Term
      t0 = ap2 natEqF (ap1 lbl input) (ap1 (constN k) input)
      t1 : Term
      t1 = ap2 natEqF (natCode k) (ap1 (constN k) input)
      t2 : Term
      t2 = ap2 natEqF (natCode k) (natCode k)
      c0 : Deriv (imp H (eqF (ap1 (C natEqF lbl (constN k)) input) t0))
      c0 = impLift {H} (ax_C natEqF lbl (constN k) input)
      c1 : Deriv (imp H (eqF t0 t1))
      c1 = impCongL natEqF (ap1 lbl input) (natCode k) (ap1 (constN k) input) nieq
      c2 : Deriv (imp H (eqF t1 t2))
      c2 = impLift {H} (congR natEqF (natCode k) (constN_eq k input))
      c3 : Deriv (imp H (eqF t2 (ap1 s O)))
      c3 = impLift {H} (natEq_eq k)
  in impEqTrans (ap1 (C natEqF lbl (constN k)) input) t0 (ap1 s O) c0
       (impEqTrans t0 t1 (ap1 s O) c1
         (impEqTrans t1 t2 (ap1 s O) c2 c3))

natEqSkip_imp : (H : Formula) (lbl : Fun1) (m k : Nat) (input : Term) -> NatNeqWitness m k ->
  Deriv (imp H (eqF (ap1 lbl input) (natCode m))) ->
  Deriv (imp H (eqF (ap1 (C natEqF lbl (constN k)) input) O))
natEqSkip_imp H lbl m k input w nieq =
  let t0 : Term
      t0 = ap2 natEqF (ap1 lbl input) (ap1 (constN k) input)
      t1 : Term
      t1 = ap2 natEqF (natCode m) (ap1 (constN k) input)
      t2 : Term
      t2 = ap2 natEqF (natCode m) (natCode k)
      c0 : Deriv (imp H (eqF (ap1 (C natEqF lbl (constN k)) input) t0))
      c0 = impLift {H} (ax_C natEqF lbl (constN k) input)
      c1 : Deriv (imp H (eqF t0 t1))
      c1 = impCongL natEqF (ap1 lbl input) (natCode m) (ap1 (constN k) input) nieq
      c2 : Deriv (imp H (eqF t1 t2))
      c2 = impLift {H} (congR natEqF (natCode m) (constN_eq k input))
      c3 : Deriv (imp H (eqF t2 O))
      c3 = impLift {H} (natEqF_at_neq m k w)
  in impEqTrans (ap1 (C natEqF lbl (constN k)) input) t0 O c0
       (impEqTrans t0 t1 O c1
         (impEqTrans t1 t2 O c2 c3))

-- neg-form skip carried under H:  imp H (neg (lbl input = natCode k))  =>  test = O .
natEqSkipNeg_imp : (H : Formula) (lbl : Fun1) (k : Nat) (input : Term) ->
  Deriv (imp H (neg (eqF (ap1 lbl input) (natCode k)))) ->
  Deriv (imp H (eqF (ap1 (C natEqF lbl (constN k)) input) O))
natEqSkipNeg_imp H lbl k input nneq =
  let t0 : Term
      t0 = ap2 natEqF (ap1 lbl input) (ap1 (constN k) input)
      t1 : Term
      t1 = ap2 natEqF (ap1 lbl input) (natCode k)
      c0 : Deriv (imp H (eqF (ap1 (C natEqF lbl (constN k)) input) t0))
      c0 = impLift {H} (ax_C natEqF lbl (constN k) input)
      c1 : Deriv (imp H (eqF t0 t1))
      c1 = impLift {H} (congR natEqF (ap1 lbl input) (constN_eq k input))
      c2 : Deriv (imp H (eqF t1 O))
      c2 = impMp (impLift {H} (natEqF_complete (ap1 lbl input) (natCode k))) nneq
  in impEqTrans (ap1 (C natEqF lbl (constN k)) input) t0 O c0
       (impEqTrans t0 t1 O c1 c2)

------------------------------------------------------------------------
-- testEq fire / skip (label = nIdx), carried under H.

testEq_fire_imp : (H : Formula) (k : Nat) (input : Term) ->
  Deriv (imp H (eqF (ap1 nIdx input) (natCode k))) ->
  Deriv (imp H (eqF (ap1 (testEq k) input) (ap1 s O)))
testEq_fire_imp H k input nieq = natEqFire_imp H nIdx k input nieq

testEq_skip_imp : (H : Formula) (m k : Nat) (input : Term) -> NatNeqWitness m k ->
  Deriv (imp H (eqF (ap1 nIdx input) (natCode m))) ->
  Deriv (imp H (eqF (ap1 (testEq k) input) O))
testEq_skip_imp H m k input w nieq = natEqSkip_imp H nIdx m k input w nieq

------------------------------------------------------------------------
-- One-level fork unfolds, carried under H.

fork_true_to_fst_imp : (H : Formula) (A B tst : Fun1) (input : Term) ->
  Deriv (imp H (eqF (ap1 tst input) (ap1 s O))) ->
  Deriv (imp H (eqF (ap1 (C condFork (C pi A B) tst) input) (ap1 A input)))
fork_true_to_fst_imp H A B tst input tT =
  let z : Term
      z = ap1 (C pi A B) input
      body : Term
      body = ap1 (C condFork (C pi A B) tst) input
      d0 : Deriv (imp H (eqF body (ap2 condFork z (ap1 tst input))))
      d0 = impLift {H} (ax_C condFork (C pi A B) tst input)
      d1 : Deriv (imp H (eqF (ap2 condFork z (ap1 tst input)) (ap2 condFork z (ap1 s O))))
      d1 = impCongR condFork (ap1 tst input) (ap1 s O) z tT
      d2 : Deriv (imp H (eqF (ap2 condFork z (ap1 s O)) (ap1 Fst z)))
      d2 = impLift {H} (condFork_true_nc z O)
      d3 : Deriv (imp H (eqF (ap1 Fst z) (ap1 Fst (ap2 pi (ap1 A input) (ap1 B input)))))
      d3 = impLift {H} (cong1 Fst (ax_C pi A B input))
      d4 : Deriv (imp H (eqF (ap1 Fst (ap2 pi (ap1 A input) (ap1 B input))) (ap1 A input)))
      d4 = impLift {H} (axFst (ap1 A input) (ap1 B input))
  in impEqTrans body (ap2 condFork z (ap1 tst input)) (ap1 A input) d0
       (impEqTrans (ap2 condFork z (ap1 tst input)) (ap2 condFork z (ap1 s O)) (ap1 A input) d1
         (impEqTrans (ap2 condFork z (ap1 s O)) (ap1 Fst z) (ap1 A input) d2
           (impEqTrans (ap1 Fst z) (ap1 Fst (ap2 pi (ap1 A input) (ap1 B input))) (ap1 A input)
             d3 d4)))

fork_false_to_snd_imp : (H : Formula) (A B tst : Fun1) (input : Term) ->
  Deriv (imp H (eqF (ap1 tst input) O)) ->
  Deriv (imp H (eqF (ap1 (C condFork (C pi A B) tst) input) (ap1 B input)))
fork_false_to_snd_imp H A B tst input tF =
  let z : Term
      z = ap1 (C pi A B) input
      body : Term
      body = ap1 (C condFork (C pi A B) tst) input
      d0 : Deriv (imp H (eqF body (ap2 condFork z (ap1 tst input))))
      d0 = impLift {H} (ax_C condFork (C pi A B) tst input)
      d1 : Deriv (imp H (eqF (ap2 condFork z (ap1 tst input)) (ap2 condFork z O)))
      d1 = impCongR condFork (ap1 tst input) O z tF
      d2 : Deriv (imp H (eqF (ap2 condFork z O) (ap1 Snd z)))
      d2 = impLift {H} (condFork_false z)
      d3 : Deriv (imp H (eqF (ap1 Snd z) (ap1 Snd (ap2 pi (ap1 A input) (ap1 B input)))))
      d3 = impLift {H} (cong1 Snd (ax_C pi A B input))
      d4 : Deriv (imp H (eqF (ap1 Snd (ap2 pi (ap1 A input) (ap1 B input))) (ap1 B input)))
      d4 = impLift {H} (axSnd (ap1 A input) (ap1 B input))
  in impEqTrans body (ap2 condFork z (ap1 tst input)) (ap1 B input) d0
       (impEqTrans (ap2 condFork z (ap1 tst input)) (ap2 condFork z O) (ap1 B input) d1
         (impEqTrans (ap2 condFork z O) (ap1 Snd z) (ap1 B input) d2
           (impEqTrans (ap1 Snd z) (ap1 Snd (ap2 pi (ap1 A input) (ap1 B input))) (ap1 B input)
             d3 d4)))
