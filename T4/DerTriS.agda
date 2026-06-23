{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriS -- the SIZE-PREFIXED triangle map  triFSized : Fun1  over the
-- T4.DerCodeS coding, transcribing T4.DerTri / T4.DerTri2 onto sized codes.
-- Each cell applies a T4.DerCodeSFun constructor code to the FOLDED child
-- values (lookupAt), so the output's size field is recomputed automatically.
--
--   triFSized (szDerZe)        = szDerZe
--   triFSized (szDerSu d)      = szDerSu (triFSized d)
--   triFSized (szDerRO d)      = triFSized d
--   triFSized (szDerRS d1 d2)  = szDerSu (szDerAd (triFSized d1) (triFSized d2))
--   triFSized (szDerAd a d2)   -- dispatch on  dtag a :
--     a = Ze : szDerRO (triFSized d2)
--     a = Su : szDerRS (pArg (triFSized a)) (triFSized d2)   (= szDerRS (triFSized a') (triFSized d2))
--     else   : szDerAd (triFSized a) (triFSized d2)
--
-- THIS FILE: cells + fold + the four NON-Ad built equations.  The Ad
-- critical-pair equations follow (same cells).  No holes, no postulates, no
-- termination warnings; --safe --without-K --exact-split.

module T4.DerTriS where

open import T4.Base

open import T4.DerCodeS
  using ( szDerZe ; szDerSu ; szDerAd ; szDerRO ; szDerRS ; dsize ; pArg
        ; dtag ; dtag_Ze ; dtag_Su ; pArg_Su )
open import T4.DerCodeSFun
  using ( szDerSuF ; szDerROF ; szDerAdF ; szDerRSF
        ; szDerSuF_eq ; szDerROF_eq ; szDerAdF_eq ; szDerRSF_eq )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.SizedFold
  using ( szRunF ; szPkg ; Pout ; sz_unfold ; sz_rc ; sz_lookup ; sz_leq_b )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt )
open import T4.WfRedSized using ( argIdx ; w10 ; w20 ; w30 ; w40 )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church      using ( pi ; sigma )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq )
open import T4.LeqMono   using ( leq_trans ; leq_pi_right )
open import T4.LeqPiLeft using ( leq_pi_left )

------------------------------------------------------------------------
-- SECTION 1.  The cells (apply the constructor codes to folded children).

pArgFn : Fun1                              -- pArg z = Snd (Snd z)
pArgFn = compose1U Snd Snd

cellTriZe : Fun1                           -- constant  szDerZe
cellTriZe = C pi (constN 1) (C pi (constN 0) Z)

cellTriSu : Fun1                           -- szDerSu (triFSized arg)
cellTriSu = compose1U szDerSuF (lookupAt argIdx)

cellTriRO : Fun1                           -- triFSized arg  (bare)
cellTriRO = lookupAt argIdx

cellTriRS : Fun1                           -- szDerSu (szDerAd (triFSized l)(triFSized r))
cellTriRS = compose1U szDerSuF (C szDerAdF (lookupAt lIdx) (lookupAt rIdx))

cellTriAdZe : Fun1                         -- szDerRO (triFSized r)
cellTriAdZe = compose1U szDerROF (lookupAt rIdx)

cellTriAdSu : Fun1                         -- szDerRS (pArg (triFSized l)) (triFSized r)
cellTriAdSu = C szDerRSF (compose1U pArgFn (lookupAt lIdx)) (lookupAt rIdx)

cellTriAdElse : Fun1                       -- szDerAd (triFSized l) (triFSized r)
cellTriAdElse = C szDerAdF (lookupAt lIdx) (lookupAt rIdx)

------------------------------------------------------------------------
-- SECTION 2.  The Ad sub-dispatch (on the left child's dtag) and the cascade.

adLeftTag : Fun1                           -- dtag of left child = Fst (Snd lIdx)
adLeftTag = compose1U Fst (compose1U Snd lIdx)

testAdZeS : Fun1
testAdZeS = C natEqF adLeftTag (constN 0)
testAdSuS : Fun1
testAdSuS = C natEqF adLeftTag (constN 1)

restAdNodeS : Fun1
restAdNodeS = C condFork (C pi cellTriAdSu cellTriAdElse) testAdSuS
adCellTriS : Fun1
adCellTriS = C condFork (C pi cellTriAdZe restAdNodeS) testAdZeS

triRestRS : Fun1
triRestRS = C condFork (C pi cellTriRS cellTriZe) (testEq 4)
triRestRO : Fun1
triRestRO = C condFork (C pi cellTriRO triRestRS) (testEq 3)
triRestAd : Fun1
triRestAd = C condFork (C pi adCellTriS triRestRO) (testEq 2)
triRestSu : Fun1
triRestSu = C condFork (C pi cellTriSu triRestAd) (testEq 1)
triStep : Fun1
triStep = C condFork (C pi cellTriZe triRestSu) (testEq 0)

triFSized : Fun1
triFSized = szRunF triStep

------------------------------------------------------------------------
-- SECTION 3.  Cell-value helpers.

cellTriZe_eq : (input : Term) -> Deriv (eqF (ap1 cellTriZe input) szDerZe)
cellTriZe_eq input =
  let inEq : Deriv (eqF (ap1 (C pi (constN 0) Z) input) (ap2 pi dgZe O))
      inEq = ruleTrans (ax_C pi (constN 0) Z input)
               (ruleTrans (congL pi (ap1 Z input) (constN_eq 0 input))
                          (congR pi (natCode 0) (axZ input)))
  in ruleTrans (ax_C pi (constN 1) (C pi (constN 0) Z) input)
       (ruleTrans (congL pi (ap1 (C pi (constN 0) Z) input) (constN_eq 1 input))
                  (congR pi (natCode 1) inEq))

------------------------------------------------------------------------
-- SECTION 4.  The four non-Ad built equations.

triFSized_Ze : Deriv (eqF (ap1 triFSized szDerZe) szDerZe)
triFSized_Ze =
  let b : Term
      b = ap2 Pair dgZe O
      pkg : Term
      pkg = szPkg triStep O b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgZe)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc triStep O b)) (axFst dgZe O))
      cell_fires : Deriv (eqF (ap1 triStep pkg) (ap1 cellTriZe pkg))
      cell_fires = fork_true_to_fst cellTriZe triRestSu (testEq 0) pkg
                     (testEq_fire 0 pkg nieq)
  in ruleTrans (sz_unfold triStep O b)
       (ruleTrans cell_fires (cellTriZe_eq pkg))

triFSized_Su : (d : Term) ->
  Deriv (eqF (ap1 triFSized (szDerSu d)) (szDerSu (ap1 triFSized d)))
triFSized_Su d =
  let A : Term
      A = dsize d
      b : Term
      b = ap2 Pair dgSu d
      pkg : Term
      pkg = szPkg triStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgSu)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc triStep A b)) (axFst dgSu d))
      cell_fires : Deriv (eqF (ap1 triStep pkg) (ap1 cellTriSu pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) pkg
                     (testEq_skip 1 0 pkg w10 nieq))
                  (fork_true_to_fst cellTriSu triRestAd (testEq 1) pkg
                     (testEq_fire 1 pkg nieq))
      argIdx_eq : Deriv (eqF (ap1 argIdx pkg) d)
      argIdx_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                    (ruleTrans (cong1 Snd (sz_rc triStep A b)) (axSnd dgSu d))
      leq_d : Deriv (leq d (Pout A b))
      leq_d = leq_trans d b (Pout A b) (leq_pi_right dgSu d) (sz_leq_b A b)
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) pkg) (ap1 triFSized d))
      recArg = sz_lookup triStep argIdx A b d argIdx_eq leq_d
      cell_val : Deriv (eqF (ap1 cellTriSu pkg) (szDerSu (ap1 triFSized d)))
      cell_val =
        ruleTrans (compose1U_eq szDerSuF (lookupAt argIdx) pkg)
          (ruleTrans (cong1 szDerSuF recArg) (szDerSuF_eq (ap1 triFSized d)))
  in ruleTrans (sz_unfold triStep A b) (ruleTrans cell_fires cell_val)

triFSized_RO : (d : Term) ->
  Deriv (eqF (ap1 triFSized (szDerRO d)) (ap1 triFSized d))
triFSized_RO d =
  let A : Term
      A = dsize d
      b : Term
      b = ap2 Pair dgRO d
      pkg : Term
      pkg = szPkg triStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgRO)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc triStep A b)) (axFst dgRO d))
      cell_fires : Deriv (eqF (ap1 triStep pkg) (ap1 cellTriRO pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) pkg
                     (testEq_skip 3 0 pkg w30 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) pkg
                        (testEq_skip 3 1 pkg w31 nieq))
            (ruleTrans (fork_false_to_snd adCellTriS triRestRO (testEq 2) pkg
                          (testEq_skip 3 2 pkg w32 nieq))
                       (fork_true_to_fst cellTriRO triRestRS (testEq 3) pkg
                          (testEq_fire 3 pkg nieq))))
      argIdx_eq : Deriv (eqF (ap1 argIdx pkg) d)
      argIdx_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                    (ruleTrans (cong1 Snd (sz_rc triStep A b)) (axSnd dgRO d))
      leq_d : Deriv (leq d (Pout A b))
      leq_d = leq_trans d b (Pout A b) (leq_pi_right dgRO d) (sz_leq_b A b)
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) pkg) (ap1 triFSized d))
      recArg = sz_lookup triStep argIdx A b d argIdx_eq leq_d
  in ruleTrans (sz_unfold triStep A b) (ruleTrans cell_fires recArg)

triFSized_RS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 triFSized (szDerRS d1 d2))
             (szDerSu (szDerAd (ap1 triFSized d1) (ap1 triFSized d2))))
triFSized_RS d1 d2 =
  let A : Term
      A = ap2 sigma (dsize d1) (dsize d2)
      b : Term
      b = ap2 Pair dgRS (ap2 Pair d1 d2)
      pkg : Term
      pkg = szPkg triStep A b
      nieq : Deriv (eqF (ap1 nIdx pkg) dgRS)
      nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
               (ruleTrans (cong1 Fst (sz_rc triStep A b)) (axFst dgRS (ap2 Pair d1 d2)))
      cell_fires : Deriv (eqF (ap1 triStep pkg) (ap1 cellTriRS pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) pkg
                     (testEq_skip 4 0 pkg w40 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) pkg
                        (testEq_skip 4 1 pkg w41 nieq))
            (ruleTrans (fork_false_to_snd adCellTriS triRestRO (testEq 2) pkg
                          (testEq_skip 4 2 pkg w42 nieq))
              (ruleTrans (fork_false_to_snd cellTriRO triRestRS (testEq 3) pkg
                            (testEq_skip 4 3 pkg w43 nieq))
                         (fork_true_to_fst cellTriRS cellTriZe (testEq 4) pkg
                            (testEq_fire 4 pkg nieq)))))
      sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) pkg) (ap2 Pair d1 d2))
      sndArg_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                    (ruleTrans (cong1 Snd (sz_rc triStep A b)) (axSnd dgRS (ap2 Pair d1 d2)))
      lIdx_eq : Deriv (eqF (ap1 lIdx pkg) d1)
      lIdx_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) pkg)
                  (ruleTrans (cong1 Fst sndArg_eq) (axFst d1 d2))
      rIdx_eq : Deriv (eqF (ap1 rIdx pkg) d2)
      rIdx_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) pkg)
                  (ruleTrans (cong1 Snd sndArg_eq) (axSnd d1 d2))
      leq_d1 : Deriv (leq d1 (Pout A b))
      leq_d1 = leq_trans d1 (ap2 Pair d1 d2) (Pout A b) (leq_pi_left d1 d2)
                 (leq_trans (ap2 Pair d1 d2) b (Pout A b)
                    (leq_pi_right dgRS (ap2 Pair d1 d2)) (sz_leq_b A b))
      leq_d2 : Deriv (leq d2 (Pout A b))
      leq_d2 = leq_trans d2 (ap2 Pair d1 d2) (Pout A b) (leq_pi_right d1 d2)
                 (leq_trans (ap2 Pair d1 d2) b (Pout A b)
                    (leq_pi_right dgRS (ap2 Pair d1 d2)) (sz_leq_b A b))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) pkg) (ap1 triFSized d1))
      recL = sz_lookup triStep lIdx A b d1 lIdx_eq leq_d1
      recR : Deriv (eqF (ap1 (lookupAt rIdx) pkg) (ap1 triFSized d2))
      recR = sz_lookup triStep rIdx A b d2 rIdx_eq leq_d2
      innerAd : Deriv (eqF (ap1 (C szDerAdF (lookupAt lIdx) (lookupAt rIdx)) pkg)
                           (szDerAd (ap1 triFSized d1) (ap1 triFSized d2)))
      innerAd =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) pkg)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) pkg) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized d1) recR)
                       (szDerAdF_eq (ap1 triFSized d1) (ap1 triFSized d2))))
      cell_val : Deriv (eqF (ap1 cellTriRS pkg)
                            (szDerSu (szDerAd (ap1 triFSized d1) (ap1 triFSized d2))))
      cell_val =
        ruleTrans (compose1U_eq szDerSuF (C szDerAdF (lookupAt lIdx) (lookupAt rIdx)) pkg)
          (ruleTrans (cong1 szDerSuF innerAd)
                     (szDerSuF_eq (szDerAd (ap1 triFSized d1) (ap1 triFSized d2))))
  in ruleTrans (sz_unfold triStep A b) (ruleTrans cell_fires cell_val)

------------------------------------------------------------------------
-- SECTION 5.  Ad sub-dispatch firing helpers.

testAdZeS_fire : (input : Term) ->
  Deriv (eqF (ap1 adLeftTag input) (natCode 0)) ->
  Deriv (eqF (ap1 testAdZeS input) (ap1 s O))
testAdZeS_fire input heq =
  ruleTrans (ax_C natEqF adLeftTag (constN 0) input)
    (ruleTrans (congL natEqF (ap1 (constN 0) input) heq)
      (ruleTrans (congR natEqF (natCode 0) (constN_eq 0 input)) (natEq_eq 0)))

testAdZeS_skip : (m : Nat) (input : Term) -> NatNeqWitness m 0 ->
  Deriv (eqF (ap1 adLeftTag input) (natCode m)) ->
  Deriv (eqF (ap1 testAdZeS input) O)
testAdZeS_skip m input w heq =
  ruleTrans (ax_C natEqF adLeftTag (constN 0) input)
    (ruleTrans (congL natEqF (ap1 (constN 0) input) heq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq 0 input)) (natEqF_at_neq m 0 w)))

testAdSuS_fire : (input : Term) ->
  Deriv (eqF (ap1 adLeftTag input) (natCode 1)) ->
  Deriv (eqF (ap1 testAdSuS input) (ap1 s O))
testAdSuS_fire input heq =
  ruleTrans (ax_C natEqF adLeftTag (constN 1) input)
    (ruleTrans (congL natEqF (ap1 (constN 1) input) heq)
      (ruleTrans (congR natEqF (natCode 1) (constN_eq 1 input)) (natEq_eq 1)))

testAdSuS_skip : (m : Nat) (input : Term) -> NatNeqWitness m 1 ->
  Deriv (eqF (ap1 adLeftTag input) (natCode m)) ->
  Deriv (eqF (ap1 testAdSuS input) O)
testAdSuS_skip m input w heq =
  ruleTrans (ax_C natEqF adLeftTag (constN 1) input)
    (ruleTrans (congL natEqF (ap1 (constN 1) input) heq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq 1 input)) (natEqF_at_neq m 1 w)))

-- adLeftTag pkg = Fst (Snd a) = dtag a, given lIdx pkg = a.
adLeftTagFrom : (pkg a : Term) -> Deriv (eqF (ap1 lIdx pkg) a) ->
  Deriv (eqF (ap1 adLeftTag pkg) (dtag a))
adLeftTagFrom pkg a lIdx_eq =
  ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) pkg)
    (cong1 Fst (ruleTrans (compose1U_eq Snd lIdx pkg) (cong1 Snd lIdx_eq)))

------------------------------------------------------------------------
-- SECTION 6.  The Ad node: shared recovery (left child a, right child d2).

private
  module AdNode (a d2 : Term) where
    A : Term
    A = ap2 sigma (dsize a) (dsize d2)
    b : Term
    b = ap2 Pair dgAd (ap2 Pair a d2)
    pkg : Term
    pkg = szPkg triStep A b
    nieq : Deriv (eqF (ap1 nIdx pkg) dgAd)
    nieq = ruleTrans (compose1U_eq Fst get_rc pkg)
             (ruleTrans (cong1 Fst (sz_rc triStep A b)) (axFst dgAd (ap2 Pair a d2)))
    sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) pkg) (ap2 Pair a d2))
    sndArg_eq = ruleTrans (compose1U_eq Snd get_rc pkg)
                  (ruleTrans (cong1 Snd (sz_rc triStep A b)) (axSnd dgAd (ap2 Pair a d2)))
    lIdx_eq : Deriv (eqF (ap1 lIdx pkg) a)
    lIdx_eq = ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) pkg)
                (ruleTrans (cong1 Fst sndArg_eq) (axFst a d2))
    rIdx_eq : Deriv (eqF (ap1 rIdx pkg) d2)
    rIdx_eq = ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) pkg)
                (ruleTrans (cong1 Snd sndArg_eq) (axSnd a d2))
    leq_a : Deriv (leq a (Pout A b))
    leq_a = leq_trans a (ap2 Pair a d2) (Pout A b) (leq_pi_left a d2)
              (leq_trans (ap2 Pair a d2) b (Pout A b)
                 (leq_pi_right dgAd (ap2 Pair a d2)) (sz_leq_b A b))
    leq_d2 : Deriv (leq d2 (Pout A b))
    leq_d2 = leq_trans d2 (ap2 Pair a d2) (Pout A b) (leq_pi_right a d2)
              (leq_trans (ap2 Pair a d2) b (Pout A b)
                 (leq_pi_right dgAd (ap2 Pair a d2)) (sz_leq_b A b))
    recL : Deriv (eqF (ap1 (lookupAt lIdx) pkg) (ap1 triFSized a))
    recL = sz_lookup triStep lIdx A b a lIdx_eq leq_a
    recR : Deriv (eqF (ap1 (lookupAt rIdx) pkg) (ap1 triFSized d2))
    recR = sz_lookup triStep rIdx A b d2 rIdx_eq leq_d2
    -- the cascade reaches the Ad cell (tag 2).
    cell_to_ad : Deriv (eqF (ap1 triStep pkg) (ap1 adCellTriS pkg))
    cell_to_ad =
      ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) pkg
                   (testEq_skip 2 0 pkg w20 nieq))
        (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) pkg
                      (testEq_skip 2 1 pkg w21 nieq))
                   (fork_true_to_fst adCellTriS triRestRO (testEq 2) pkg
                      (testEq_fire 2 pkg nieq)))

------------------------------------------------------------------------
-- SECTION 7.  The three Ad critical-pair equations.

triFSized_Ad_Ze : (d2 : Term) ->
  Deriv (eqF (ap1 triFSized (szDerAd szDerZe d2)) (szDerRO (ap1 triFSized d2)))
triFSized_Ad_Ze d2 =
  let open AdNode szDerZe d2
      adLeft : Deriv (eqF (ap1 adLeftTag pkg) (natCode 0))
      adLeft = ruleTrans (adLeftTagFrom pkg szDerZe lIdx_eq) dtag_Ze
      ad_fires : Deriv (eqF (ap1 adCellTriS pkg) (ap1 cellTriAdZe pkg))
      ad_fires = fork_true_to_fst cellTriAdZe restAdNodeS testAdZeS pkg
                   (testAdZeS_fire pkg adLeft)
      cell_val : Deriv (eqF (ap1 cellTriAdZe pkg) (szDerRO (ap1 triFSized d2)))
      cell_val =
        ruleTrans (compose1U_eq szDerROF (lookupAt rIdx) pkg)
          (ruleTrans (cong1 szDerROF recR) (szDerROF_eq (ap1 triFSized d2)))
  in ruleTrans (sz_unfold triStep A b)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))

triFSized_Ad_Su : (a' d2 : Term) ->
  Deriv (eqF (ap1 triFSized (szDerAd (szDerSu a') d2))
             (szDerRS (ap1 triFSized a') (ap1 triFSized d2)))
triFSized_Ad_Su a' d2 =
  let open AdNode (szDerSu a') d2
      adLeft : Deriv (eqF (ap1 adLeftTag pkg) (natCode 1))
      adLeft = ruleTrans (adLeftTagFrom pkg (szDerSu a') lIdx_eq) (dtag_Su a')
      ad_fires : Deriv (eqF (ap1 adCellTriS pkg) (ap1 cellTriAdSu pkg))
      ad_fires =
        ruleTrans (fork_false_to_snd cellTriAdZe restAdNodeS testAdZeS pkg
                     (testAdZeS_skip 1 pkg w10 adLeft))
                  (fork_true_to_fst cellTriAdSu cellTriAdElse testAdSuS pkg
                     (testAdSuS_fire pkg adLeft))
      -- no-grandchild trick: lookupAt lIdx = triFSized (szDerSu a') = szDerSu (triFSized a').
      recL_su : Deriv (eqF (ap1 (lookupAt lIdx) pkg) (szDerSu (ap1 triFSized a')))
      recL_su = ruleTrans recL (triFSized_Su a')
      -- pArgFn (szDerSu x) = x.
      leftRec : Deriv (eqF (ap1 (compose1U pArgFn (lookupAt lIdx)) pkg) (ap1 triFSized a'))
      leftRec =
        ruleTrans (compose1U_eq pArgFn (lookupAt lIdx) pkg)
          (ruleTrans (cong1 pArgFn recL_su)
            (ruleTrans (compose1U_eq Snd Snd (szDerSu (ap1 triFSized a')))
                       (pArg_Su (ap1 triFSized a'))))
      cell_val : Deriv (eqF (ap1 cellTriAdSu pkg)
                            (szDerRS (ap1 triFSized a') (ap1 triFSized d2)))
      cell_val =
        ruleTrans (ax_C szDerRSF (compose1U pArgFn (lookupAt lIdx)) (lookupAt rIdx) pkg)
          (ruleTrans (congL szDerRSF (ap1 (lookupAt rIdx) pkg) leftRec)
            (ruleTrans (congR szDerRSF (ap1 triFSized a') recR)
                       (szDerRSF_eq (ap1 triFSized a') (ap1 triFSized d2))))
  in ruleTrans (sz_unfold triStep A b)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))

triFSized_Ad_else : (a d2 : Term) (m : Nat) ->
  NatNeqWitness m 0 -> NatNeqWitness m 1 ->
  Deriv (eqF (dtag a) (natCode m)) ->
  Deriv (eqF (ap1 triFSized (szDerAd a d2))
             (szDerAd (ap1 triFSized a) (ap1 triFSized d2)))
triFSized_Ad_else a d2 m w0 w1 htag =
  let open AdNode a d2
      adLeft : Deriv (eqF (ap1 adLeftTag pkg) (natCode m))
      adLeft = ruleTrans (adLeftTagFrom pkg a lIdx_eq) htag
      ad_fires : Deriv (eqF (ap1 adCellTriS pkg) (ap1 cellTriAdElse pkg))
      ad_fires =
        ruleTrans (fork_false_to_snd cellTriAdZe restAdNodeS testAdZeS pkg
                     (testAdZeS_skip m pkg w0 adLeft))
                  (fork_false_to_snd cellTriAdSu cellTriAdElse testAdSuS pkg
                     (testAdSuS_skip m pkg w1 adLeft))
      cell_val : Deriv (eqF (ap1 cellTriAdElse pkg)
                            (szDerAd (ap1 triFSized a) (ap1 triFSized d2)))
      cell_val =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) pkg)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) pkg) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized a) recR)
                       (szDerAdF_eq (ap1 triFSized a) (ap1 triFSized d2))))
  in ruleTrans (sz_unfold triStep A b)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))
