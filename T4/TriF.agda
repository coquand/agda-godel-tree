{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriF -- the TRIANGLE CERT TRANSFORMER  triF : Fun1 , the object function
-- that maps a parallel-reduction certificate of  Par t u  to a certificate of
-- Par u (dev t) -- the FULL Takahashi triangle (attempt3 §11 I4) read off the
-- INPUT cert's CODE by a course-of-values fold, so the otherwise-inert object
-- certificate is CONSUMED by recursion-on-the-code (NOT pattern matching).
--
--   triF cZe              = cZe
--   triF (cSu d)          = cSu (triF d)
--   triF (cRO d)          = triF d
--   triF (cRS d1 d2)      = cSu (cAd (triF d1) (triF d2))
--   triF (cAd cZe d2)        = cRO (triF d2)
--   triF (cAd (cSu d1') d2)  = cRS (triF d1') (triF d2)
--   triF (cAd a d2)          = cAd (triF a) (triF d2)   -- chd a in {2,3,4}
--
-- This mirrors  T4.ChurchRosserProto.tri / T4.ParTri.tri  clause-for-clause
-- (the cAd case dispatches on the first sub-cert's head, exactly as tri
-- dispatches on the first parallel sub-step pZe/pSu/_).  Same no-grandchild
-- trick as DevF/DevCertF:  triF d1' = Snd (triF (cSu d1'))  via tri_at_cSu +
-- cSu_sub, so every cell looks up only DIRECT sub-certs.
--
-- THIS FILE: the fold + the SEVEN closure equations (the cAd case split three
-- ways).  Endpoint/validity preservation (src/tgt/isCert of triF) is the object
-- course-of-values ruleIndNat of the NEXT file.  Outer dispatch = T4.ParEnds.src
-- skeleton (4-way, cert tags 1..4); inner cAd dispatch = T4.DevCertF skeleton
-- (3-way, sub-cert tags 0/1/else).  No holes, no postulates.

module T4.TriF where

open import T4.Base
open import T4.FoldRec
open import T4.CoVSpec      using ( cov_spec )
open import T4.CoVSpecUniv  using ( HistP_sbt )
open import T4.Stability    using ( HPsbt )
open import T4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import T4.LeqMono      using ( leq_sigma_right ; leq_pi_right ; leq_trans )
open import T4.LeqPiLeft    using ( leq_pi_left )
open import T4.LenR         using ( get_rc )
open import T4.ProgParse    using ( get_tag )

open import T4.ParCert using
  ( cZe ; cSu ; cAd ; cRO ; cRS ; cSu_sub
  ; chd_cZe ; chd_cSu ; chd_cAd ; chd_cRO ; chd_cRS )

open import BRA3.Church        using ( pi ; sigma ; tau ; hPi ; T90 ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra   using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.Dispatch      using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Cantor-zero collapse  pi O O = O  (cZe = pi O O is the base).

pi_O_O : Deriv (eqF (ap2 pi O O) O)
pi_O_O = ruleTrans (ax_R_base tau sigma hPi O) T90

------------------------------------------------------------------------
-- SECTION 1.  Sub-cert accessors and cells.

lcIdx : Fun1
lcIdx = compose1U Fst get_rc
rcIdx : Fun1
rcIdx = compose1U Snd get_rc
firstHead : Fun1
firstHead = compose1U Fst lcIdx

-- cZe = pi 0 O ; cSu d = pi 1 d ; cAd d1 d2 = pi 2 (pi d1 d2) ;
-- cRO d = pi 3 d ; cRS d1 d2 = pi 4 (pi d1 d2).
cellCSu : Fun1                          -- cSu (triF d')          , d' = get_rc
cellCSu = C pi (constN 1) (lookupAt get_rc)

cellCRO : Fun1                          -- triF d'  (bare)        , d' = get_rc
cellCRO = lookupAt get_rc

cellCRS : Fun1                          -- cSu (cAd (triF d1) (triF d2))
cellCRS = C pi (constN 1) (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)))

-- cAd inner cells (sub-certs d1 = lcIdx , d2 = rcIdx).
cellAdZe : Fun1                         -- cRO (triF d2)
cellAdZe = C pi (constN 3) (lookupAt rcIdx)

cellAdSu : Fun1                         -- cRS (Snd (triF d1)) (triF d2)
cellAdSu = C pi (constN 4)
             (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx))

cellAdAd : Fun1                         -- cAd (triF d1) (triF d2)
cellAdAd = C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))

------------------------------------------------------------------------
-- SECTION 2.  Dispatch cascades.

test1 : Fun1
test1 = C natEqF get_tag (constN 1)
test2 : Fun1
test2 = C natEqF get_tag (constN 2)
test3 : Fun1
test3 = C natEqF get_tag (constN 3)

testF0 : Fun1                           -- first sub-cert head tag = 0 (cZe) ?
testF0 = C natEqF firstHead (constN 0)
testF1 : Fun1                           -- first sub-cert head tag = 1 (cSu) ?
testF1 = C natEqF firstHead (constN 1)

innerAd2 : Fun1                         -- d1-tag1 -> cellAdSu ; else cellAdAd
innerAd2 = C condFork (C pi cellAdSu cellAdAd) testF1
cellCAd : Fun1                          -- d1-tag0 -> cellAdZe ; else innerAd2
cellCAd = C condFork (C pi cellAdZe innerAd2) testF0

innerO2 : Fun1                          -- tag3 -> cellCRO ; else (tag4) cellCRS
innerO2 = C condFork (C pi cellCRO cellCRS) test3
innerO1 : Fun1                          -- tag2 -> cellCAd ; else innerO2
innerO1 = C condFork (C pi cellCAd innerO2) test2
stepBody_tri : Fun1                     -- tag1 -> cellCSu ; else innerO1
stepBody_tri = C condFork (C pi cellCSu innerO1) test1

stepFun_tri : Fun2
stepFun_tri = Post stepBody_tri pi

triBase : Fun1                          -- O |-> cZe = pi O O
triBase = C pi Z Z

triF : Fun1
triF = fold triBase stepFun_tri

------------------------------------------------------------------------
-- SECTION 3.  Base case:  triF cZe = cZe .

triBaseAtO : Deriv (eqF (ap1 triBase O) cZe)
triBaseAtO =
  ruleTrans (ax_C pi Z Z O)
    (ruleTrans (congL pi (ap1 Z O) (axZ O))
               (congR pi O (axZ O)))

tri_at_cZe : Deriv (eqF (ap1 triF cZe) cZe)
tri_at_cZe =
  ruleTrans (cong1 triF pi_O_O)
    (ruleTrans (fold_at_O triBase stepFun_tri) triBaseAtO)

------------------------------------------------------------------------
-- SECTION 4.  Shared node plumbing (generic in A, b).

module NP (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec triBase stepFun_tri) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  np_unfold : Deriv (eqF (ap1 triF node) (ap1 stepBody_tri input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold triBase stepFun_tri A b)
              (axPost stepBody_tri pi P_outer (ap1 Snd prev))

  np_head : Deriv (eqF (ap1 get_tag input_pkg) (ap1 s A))
  np_head =
    let t1 : Deriv (eqF (ap1 get_tag input_pkg) (ap1 Fst (ap1 get_newK input_pkg)))
        t1 = compose1U_eq Fst get_newK input_pkg
        t2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        t2 = get_newK_at_pi P_outer (ap1 Snd prev)
        t3 : Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst node))
        t3 = cong1 Fst (ruleSym (pi_at_succ A b))
        t4 : Deriv (eqF (ap1 Fst node) (ap1 s A))
        t4 = axFst (ap1 s A) b
    in ruleTrans t1 (ruleTrans (cong1 Fst t2) (ruleTrans t3 t4))

  np_rc : Deriv (eqF (ap1 get_rc input_pkg) b)
  np_rc =
    let s1 : Deriv (eqF (ap1 get_rc input_pkg) (ap1 Snd (ap1 get_newK input_pkg)))
        s1 = compose1U_eq Snd get_newK input_pkg
        s2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        s2 = get_newK_at_pi P_outer (ap1 Snd prev)
        s3 : Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd node))
        s3 = cong1 Snd (ruleSym (pi_at_succ A b))
        s4 : Deriv (eqF (ap1 Snd node) b)
        s4 = axSnd (ap1 s A) b
    in ruleTrans s1 (ruleTrans (cong1 Snd s2) (ruleTrans s3 s4))

  leq_b_P : Deriv (leq b P_outer)
  leq_b_P = leq_sigma_right (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

  np_lookup_gen :
    (idx : Fun1) (ct : Term) ->
    Deriv (eqF (ap1 idx input_pkg) ct) ->
    Deriv (leq ct P_outer) ->
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 triF ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt triBase stepFun_tri O P_outer))
        get_table_value = get_table_at_pi P_outer (ap1 Snd prev)
        u1 : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                        (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                  (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)))))
        u1 = lookupAt_unfold idx input_pkg
        sub_eq : Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                            (ap2 sub P_outer ct))
        sub_eq = ruleTrans (congL sub (ap1 idx input_pkg) get_K_value)
                           (congR sub P_outer idx_eq)
        iter_eq : Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                              (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)))
                              (ap2 (iter Snd) (HistP_sbt triBase stepFun_tri O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt triBase stepFun_tri O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt triBase stepFun_tri O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_tri : Deriv (eqF (HPsbt triBase stepFun_tri O ct P_outer) (ap1 triF ct))
        HP_to_tri = lookup_eq_fold triBase stepFun_tri ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_tri

------------------------------------------------------------------------
-- SECTION 5.  Outer dispatch (cert tag 1..4), generic in (A, b).

module Outer (A b : Term) where
  open NP A b public

  pair1 : Term
  pair1 = ap1 (C pi cellCSu innerO1) input_pkg
  pair2 : Term
  pair2 = ap1 (C pi cellCAd innerO2) input_pkg
  pair3 : Term
  pair3 = ap1 (C pi cellCRO cellCRS) input_pkg

  fst_pair1 : Deriv (eqF (ap1 Fst pair1) (ap1 cellCSu input_pkg))
  fst_pair1 = ruleTrans (cong1 Fst (ax_C pi cellCSu innerO1 input_pkg))
                        (axFst (ap1 cellCSu input_pkg) (ap1 innerO1 input_pkg))
  snd_pair1 : Deriv (eqF (ap1 Snd pair1) (ap1 innerO1 input_pkg))
  snd_pair1 = ruleTrans (cong1 Snd (ax_C pi cellCSu innerO1 input_pkg))
                        (axSnd (ap1 cellCSu input_pkg) (ap1 innerO1 input_pkg))
  fst_pair2 : Deriv (eqF (ap1 Fst pair2) (ap1 cellCAd input_pkg))
  fst_pair2 = ruleTrans (cong1 Fst (ax_C pi cellCAd innerO2 input_pkg))
                        (axFst (ap1 cellCAd input_pkg) (ap1 innerO2 input_pkg))
  snd_pair2 : Deriv (eqF (ap1 Snd pair2) (ap1 innerO2 input_pkg))
  snd_pair2 = ruleTrans (cong1 Snd (ax_C pi cellCAd innerO2 input_pkg))
                        (axSnd (ap1 cellCAd input_pkg) (ap1 innerO2 input_pkg))
  fst_pair3 : Deriv (eqF (ap1 Fst pair3) (ap1 cellCRO input_pkg))
  fst_pair3 = ruleTrans (cong1 Fst (ax_C pi cellCRO cellCRS input_pkg))
                        (axFst (ap1 cellCRO input_pkg) (ap1 cellCRS input_pkg))
  snd_pair3 : Deriv (eqF (ap1 Snd pair3) (ap1 cellCRS input_pkg))
  snd_pair3 = ruleTrans (cong1 Snd (ax_C pi cellCRO cellCRS input_pkg))
                        (axSnd (ap1 cellCRO input_pkg) (ap1 cellCRS input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody_tri input_pkg)
                     (ap2 condFork pair1 (ap1 test1 input_pkg)))
  sb_eq = ax_C condFork (C pi cellCSu innerO1) test1 input_pkg
  innerO1_eq : Deriv (eqF (ap1 innerO1 input_pkg)
                          (ap2 condFork pair2 (ap1 test2 input_pkg)))
  innerO1_eq = ax_C condFork (C pi cellCAd innerO2) test2 input_pkg
  innerO2_eq : Deriv (eqF (ap1 innerO2 input_pkg)
                          (ap2 condFork pair3 (ap1 test3 input_pkg)))
  innerO2_eq = ax_C condFork (C pi cellCRO cellCRS) test3 input_pkg

  test1_val : Deriv (eqF (ap1 test1 input_pkg) (ap2 natEqF (ap1 s A) (natCode 1)))
  test1_val =
    ruleTrans (ax_C natEqF get_tag (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 1 input_pkg)))
  test2_val : Deriv (eqF (ap1 test2 input_pkg) (ap2 natEqF (ap1 s A) (natCode 2)))
  test2_val =
    ruleTrans (ax_C natEqF get_tag (constN 2) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 2) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 2 input_pkg)))
  test3_val : Deriv (eqF (ap1 test3 input_pkg) (ap2 natEqF (ap1 s A) (natCode 3)))
  test3_val =
    ruleTrans (ax_C natEqF get_tag (constN 3) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 3) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 3 input_pkg)))

------------------------------------------------------------------------
-- SECTION 6.  cSu closure:  triF (cSu d) = cSu (triF d) .
--   node tag = natCode 1 (A = O) -> test1 fires -> cellCSu.

tri_at_cSu : (d : Term) -> Deriv (eqF (ap1 triF (cSu d)) (cSu (ap1 triF d)))
tri_at_cSu d =
  let open Outer O d
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 triF (cSu d)) (ap1 cellCSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pair1 t1_fire)
              (ruleTrans (condFork_true_nc pair1 O) fst_pair1)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 triF d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
      cellCSu_value : Deriv (eqF (ap1 cellCSu input_pkg) (cSu (ap1 triF d)))
      cellCSu_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec))
  in ruleTrans to_cell cellCSu_value

------------------------------------------------------------------------
-- SECTION 7.  cRO closure:  triF (cRO d) = triF d .
--   node tag = natCode 3 (A = natCode 2) -> test1,2 skip, test3 fires -> cellCRO.

tri_at_cRO : (d : Term) -> Deriv (eqF (ap1 triF (cRO d)) (ap1 triF d))
tri_at_cRO d =
  let open Outer (natCode 2) d
      w31 : NatNeqWitness 3 1
      w31 = decideNatNeq 3 1 (\ ())
      w32 : NatNeqWitness 3 2
      w32 = decideNatNeq 3 2 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 3 1 w31)
      to_innerO1 : Deriv (eqF (ap1 stepBody_tri input_pkg) (ap1 innerO1 input_pkg))
      to_innerO1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pair1 t1_O)
            (ruleTrans (condFork_false pair1) snd_pair1))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 3 2 w32)
      to_innerO2 : Deriv (eqF (ap1 innerO1 input_pkg) (ap1 innerO2 input_pkg))
      to_innerO2 =
        ruleTrans innerO1_eq
          (ruleTrans (congR condFork pair2 t2_O)
            (ruleTrans (condFork_false pair2) snd_pair2))
      t3_fire : Deriv (eqF (ap1 test3 input_pkg) (ap1 s O))
      t3_fire = ruleTrans test3_val (natEq_eq 3)
      to_cell : Deriv (eqF (ap1 innerO2 input_pkg) (ap1 cellCRO input_pkg))
      to_cell =
        ruleTrans innerO2_eq
          (ruleTrans (congR condFork pair3 t3_fire)
            (ruleTrans (condFork_true_nc pair3 O) fst_pair3))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 triF d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
  in ruleTrans np_unfold
       (ruleTrans to_innerO1 (ruleTrans to_innerO2 (ruleTrans to_cell rec)))

------------------------------------------------------------------------
-- SECTION 8.  cRS closure:  triF (cRS d1 d2) = cSu (cAd (triF d1) (triF d2)) .
--   node tag = natCode 4 (A = natCode 3) -> test1,2,3 all skip -> cellCRS.

tri_at_cRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 triF (cRS d1 d2)) (cSu (cAd (ap1 triF d1) (ap1 triF d2))))
tri_at_cRS d1 d2 =
  let open Outer (natCode 3) (ap2 pi d1 d2)
      w41 : NatNeqWitness 4 1
      w41 = decideNatNeq 4 1 (\ ())
      w42 : NatNeqWitness 4 2
      w42 = decideNatNeq 4 2 (\ ())
      w43 : NatNeqWitness 4 3
      w43 = decideNatNeq 4 3 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 4 1 w41)
      to_innerO1 : Deriv (eqF (ap1 stepBody_tri input_pkg) (ap1 innerO1 input_pkg))
      to_innerO1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pair1 t1_O)
            (ruleTrans (condFork_false pair1) snd_pair1))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 4 2 w42)
      to_innerO2 : Deriv (eqF (ap1 innerO1 input_pkg) (ap1 innerO2 input_pkg))
      to_innerO2 =
        ruleTrans innerO1_eq
          (ruleTrans (congR condFork pair2 t2_O)
            (ruleTrans (condFork_false pair2) snd_pair2))
      t3_O : Deriv (eqF (ap1 test3 input_pkg) O)
      t3_O = ruleTrans test3_val (natEqF_at_neq 4 3 w43)
      to_cell : Deriv (eqF (ap1 innerO2 input_pkg) (ap1 cellCRS input_pkg))
      to_cell =
        ruleTrans innerO2_eq
          (ruleTrans (congR condFork pair3 t3_O)
            (ruleTrans (condFork_false pair3) snd_pair3))
      lcIdx_eq : Deriv (eqF (ap1 lcIdx input_pkg) d1)
      lcIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                           (ruleTrans (cong1 Fst np_rc) (axFst d1 d2))
      rcIdx_eq : Deriv (eqF (ap1 rcIdx input_pkg) d2)
      rcIdx_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                           (ruleTrans (cong1 Snd np_rc) (axSnd d1 d2))
      leq_d1 : Deriv (leq d1 P_outer)
      leq_d1 = leq_trans d1 (ap2 pi d1 d2) P_outer (leq_pi_left d1 d2) leq_b_P
      leq_d2 : Deriv (leq d2 P_outer)
      leq_d2 = leq_trans d2 (ap2 pi d1 d2) P_outer (leq_pi_right d1 d2) leq_b_P
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 triF d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 triF d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      ad_pair : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                           (ap2 pi (ap1 triF d1) (ap1 triF d2)))
      ad_pair =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 triF d1) rec2))
      cad : Deriv (eqF (ap1 (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg)
                       (cAd (ap1 triF d1) (ap1 triF d2)))
      cad =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) ad_pair))
      cellCRS_value : Deriv (eqF (ap1 cellCRS input_pkg)
                                 (cSu (cAd (ap1 triF d1) (ap1 triF d2))))
      cellCRS_value =
        ruleTrans (ax_C pi (constN 1)
                     (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg)
                               (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) cad))
  in ruleTrans np_unfold
       (ruleTrans to_innerO1 (ruleTrans to_innerO2 (ruleTrans to_cell cellCRS_value)))

------------------------------------------------------------------------
-- SECTION 9.  cAd dispatch helpers (node = cAd d1 d2 , A = natCode 1 ,
--   b = pi d1 d2 ; test1 skip, test2 fires -> cellCAd ; then inner on d1's tag).

module AdNode (d1 d2 : Term) where
  open Outer (natCode 1) (ap2 pi d1 d2) public

  w21 : NatNeqWitness 2 1
  w21 = decideNatNeq 2 1 (\ ())
  t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
  t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
  t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
  t2_fire = ruleTrans test2_val (natEq_eq 2)
  to_cellCAd : Deriv (eqF (ap1 triF (cAd d1 d2)) (ap1 cellCAd input_pkg))
  to_cellCAd =
    ruleTrans np_unfold
      (ruleTrans sb_eq
        (ruleTrans (congR condFork pair1 t1_O)
          (ruleTrans (condFork_false pair1)
            (ruleTrans snd_pair1
              (ruleTrans innerO1_eq
                (ruleTrans (congR condFork pair2 t2_fire)
                  (ruleTrans (condFork_true_nc pair2 O) fst_pair2)))))))

  lcIdx_eq : Deriv (eqF (ap1 lcIdx input_pkg) d1)
  lcIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                       (ruleTrans (cong1 Fst np_rc) (axFst d1 d2))
  rcIdx_eq : Deriv (eqF (ap1 rcIdx input_pkg) d2)
  rcIdx_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                       (ruleTrans (cong1 Snd np_rc) (axSnd d1 d2))
  leq_d1 : Deriv (leq d1 P_outer)
  leq_d1 = leq_trans d1 (ap2 pi d1 d2) P_outer (leq_pi_left d1 d2) leq_b_P
  leq_d2 : Deriv (leq d2 P_outer)
  leq_d2 = leq_trans d2 (ap2 pi d1 d2) P_outer (leq_pi_right d1 d2) leq_b_P
  rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 triF d1))
  rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
  rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 triF d2))
  rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2

  firstHead_eq : Deriv (eqF (ap1 firstHead input_pkg) (ap1 Fst d1))
  firstHead_eq = ruleTrans (compose1U_eq Fst lcIdx input_pkg) (cong1 Fst lcIdx_eq)

  pairInner0 : Term
  pairInner0 = ap1 (C pi cellAdZe innerAd2) input_pkg
  pairInner1 : Term
  pairInner1 = ap1 (C pi cellAdSu cellAdAd) input_pkg

  fst_pairInner0 : Deriv (eqF (ap1 Fst pairInner0) (ap1 cellAdZe input_pkg))
  fst_pairInner0 = ruleTrans (cong1 Fst (ax_C pi cellAdZe innerAd2 input_pkg))
                             (axFst (ap1 cellAdZe input_pkg) (ap1 innerAd2 input_pkg))
  snd_pairInner0 : Deriv (eqF (ap1 Snd pairInner0) (ap1 innerAd2 input_pkg))
  snd_pairInner0 = ruleTrans (cong1 Snd (ax_C pi cellAdZe innerAd2 input_pkg))
                             (axSnd (ap1 cellAdZe input_pkg) (ap1 innerAd2 input_pkg))
  fst_pairInner1 : Deriv (eqF (ap1 Fst pairInner1) (ap1 cellAdSu input_pkg))
  fst_pairInner1 = ruleTrans (cong1 Fst (ax_C pi cellAdSu cellAdAd input_pkg))
                             (axFst (ap1 cellAdSu input_pkg) (ap1 cellAdAd input_pkg))
  snd_pairInner1 : Deriv (eqF (ap1 Snd pairInner1) (ap1 cellAdAd input_pkg))
  snd_pairInner1 = ruleTrans (cong1 Snd (ax_C pi cellAdSu cellAdAd input_pkg))
                             (axSnd (ap1 cellAdSu input_pkg) (ap1 cellAdAd input_pkg))

  cellCAd_eq : Deriv (eqF (ap1 cellCAd input_pkg)
                          (ap2 condFork pairInner0 (ap1 testF0 input_pkg)))
  cellCAd_eq = ax_C condFork (C pi cellAdZe innerAd2) testF0 input_pkg
  innerAd2_eq : Deriv (eqF (ap1 innerAd2 input_pkg)
                           (ap2 condFork pairInner1 (ap1 testF1 input_pkg)))
  innerAd2_eq = ax_C condFork (C pi cellAdSu cellAdAd) testF1 input_pkg

  testF0_at : (tg : Nat) -> Deriv (eqF (ap1 Fst d1) (natCode tg)) ->
              Deriv (eqF (ap1 testF0 input_pkg) (ap2 natEqF (natCode tg) (natCode 0)))
  testF0_at tg hd_d1 =
    ruleTrans (ax_C natEqF firstHead (constN 0) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 0) input_pkg) (ruleTrans firstHead_eq hd_d1))
                 (congR natEqF (natCode tg) (constN_eq 0 input_pkg)))
  testF1_at : (tg : Nat) -> Deriv (eqF (ap1 Fst d1) (natCode tg)) ->
              Deriv (eqF (ap1 testF1 input_pkg) (ap2 natEqF (natCode tg) (natCode 1)))
  testF1_at tg hd_d1 =
    ruleTrans (ax_C natEqF firstHead (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) (ruleTrans firstHead_eq hd_d1))
                 (congR natEqF (natCode tg) (constN_eq 1 input_pkg)))

------------------------------------------------------------------------
-- SECTION 10.  cAd / first sub-cert = cZe:  triF (cAd cZe d2) = cRO (triF d2) .

tri_at_cAd_cZe : (d2 : Term) ->
  Deriv (eqF (ap1 triF (cAd cZe d2)) (cRO (ap1 triF d2)))
tri_at_cAd_cZe d2 =
  let open AdNode cZe d2
      tF0_fire : Deriv (eqF (ap1 testF0 input_pkg) (ap1 s O))
      tF0_fire = ruleTrans (testF0_at 0 chd_cZe) (natEq_eq 0)
      to_cell : Deriv (eqF (ap1 cellCAd input_pkg) (ap1 cellAdZe input_pkg))
      to_cell =
        ruleTrans cellCAd_eq
          (ruleTrans (congR condFork pairInner0 tF0_fire)
            (ruleTrans (condFork_true_nc pairInner0 O) fst_pairInner0))
      cellAdZe_value : Deriv (eqF (ap1 cellAdZe input_pkg) (cRO (ap1 triF d2)))
      cellAdZe_value =
        ruleTrans (ax_C pi (constN 3) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) (constN_eq 3 input_pkg))
                     (congR pi (natCode 3) rec2))
  in ruleTrans to_cellCAd (ruleTrans to_cell cellAdZe_value)

------------------------------------------------------------------------
-- SECTION 11.  cAd / first sub-cert = cSu:
--   triF (cAd (cSu d1') d2) = cRS (triF d1') (triF d2) .
--   triF d1' = Snd (triF (cSu d1')) via tri_at_cSu + cSu_sub.

tri_at_cAd_cSu : (d1' d2 : Term) ->
  Deriv (eqF (ap1 triF (cAd (cSu d1') d2)) (cRS (ap1 triF d1') (ap1 triF d2)))
tri_at_cAd_cSu d1' d2 =
  let open AdNode (cSu d1') d2
      w10 : NatNeqWitness 1 0
      w10 = decideNatNeq 1 0 (\ ())
      tF0_O : Deriv (eqF (ap1 testF0 input_pkg) O)
      tF0_O = ruleTrans (testF0_at 1 (chd_cSu d1')) (natEqF_at_neq 1 0 w10)
      tF1_fire : Deriv (eqF (ap1 testF1 input_pkg) (ap1 s O))
      tF1_fire = ruleTrans (testF1_at 1 (chd_cSu d1')) (natEq_eq 1)
      to_inner : Deriv (eqF (ap1 cellCAd input_pkg) (ap1 innerAd2 input_pkg))
      to_inner =
        ruleTrans cellCAd_eq
          (ruleTrans (congR condFork pairInner0 tF0_O)
            (ruleTrans (condFork_false pairInner0) snd_pairInner0))
      to_cell : Deriv (eqF (ap1 innerAd2 input_pkg) (ap1 cellAdSu input_pkg))
      to_cell =
        ruleTrans innerAd2_eq
          (ruleTrans (congR condFork pairInner1 tF1_fire)
            (ruleTrans (condFork_true_nc pairInner1 O) fst_pairInner1))
      to_cellAdSu : Deriv (eqF (ap1 triF (cAd (cSu d1') d2)) (ap1 cellAdSu input_pkg))
      to_cellAdSu = ruleTrans to_cellCAd (ruleTrans to_inner to_cell)
      -- Snd (triF (cSu d1')) = Snd (cSu (triF d1')) = triF d1' .
      d1'_eq : Deriv (eqF (ap1 Snd (ap1 (lookupAt lcIdx) input_pkg)) (ap1 triF d1'))
      d1'_eq =
        ruleTrans (cong1 Snd rec1)
          (ruleTrans (cong1 Snd (tri_at_cSu d1')) (cSu_sub (ap1 triF d1')))
      inner_pair : Deriv (eqF (ap1 (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                              (ap2 pi (ap1 triF d1') (ap1 triF d2)))
      inner_pair =
        ruleTrans (ax_C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg)
                        (ruleTrans (compose1U_eq Snd (lookupAt lcIdx) input_pkg) d1'_eq))
                     (congR pi (ap1 triF d1') rec2))
      cellAdSu_value : Deriv (eqF (ap1 cellAdSu input_pkg)
                                  (cRS (ap1 triF d1') (ap1 triF d2)))
      cellAdSu_value =
        ruleTrans (ax_C pi (constN 4)
                     (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 4 input_pkg))
                     (congR pi (natCode 4) inner_pair))
  in ruleTrans to_cellAdSu cellAdSu_value

------------------------------------------------------------------------
-- SECTION 12.  cAd / first sub-cert head in {2,3,4}:
--   triF (cAd d1 d2) = cAd (triF d1) (triF d2)  given  chd d1 = natCode tg ,
--   tg /= 0,1.  Specialised to the three constructors (cAd / cRO / cRS).

-- Generic "else" case, parameterised by the first sub-cert's head tag.
tri_at_cAd_else : (d1 d2 : Term) (tg : Nat) ->
  Deriv (eqF (ap1 Fst d1) (natCode tg)) ->
  NatNeqWitness tg 0 -> NatNeqWitness tg 1 ->
  Deriv (eqF (ap1 triF (cAd d1 d2)) (cAd (ap1 triF d1) (ap1 triF d2)))
tri_at_cAd_else d1 d2 tg hd_d1 wtg0 wtg1 =
  let open AdNode d1 d2
      tF0_O : Deriv (eqF (ap1 testF0 input_pkg) O)
      tF0_O = ruleTrans (testF0_at tg hd_d1) (natEqF_at_neq tg 0 wtg0)
      tF1_O : Deriv (eqF (ap1 testF1 input_pkg) O)
      tF1_O = ruleTrans (testF1_at tg hd_d1) (natEqF_at_neq tg 1 wtg1)
      to_inner : Deriv (eqF (ap1 cellCAd input_pkg) (ap1 innerAd2 input_pkg))
      to_inner =
        ruleTrans cellCAd_eq
          (ruleTrans (congR condFork pairInner0 tF0_O)
            (ruleTrans (condFork_false pairInner0) snd_pairInner0))
      to_cell : Deriv (eqF (ap1 innerAd2 input_pkg) (ap1 cellAdAd input_pkg))
      to_cell =
        ruleTrans innerAd2_eq
          (ruleTrans (congR condFork pairInner1 tF1_O)
            (ruleTrans (condFork_false pairInner1) snd_pairInner1))
      to_cellAdAd : Deriv (eqF (ap1 triF (cAd d1 d2)) (ap1 cellAdAd input_pkg))
      to_cellAdAd = ruleTrans to_cellCAd (ruleTrans to_inner to_cell)
      inner_pair : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                              (ap2 pi (ap1 triF d1) (ap1 triF d2)))
      inner_pair =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 triF d1) rec2))
      cellAdAd_value : Deriv (eqF (ap1 cellAdAd input_pkg)
                                  (cAd (ap1 triF d1) (ap1 triF d2)))
      cellAdAd_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_pair))
  in ruleTrans to_cellAdAd cellAdAd_value

tri_at_cAd_cAd : (d1a d1b d2 : Term) ->
  Deriv (eqF (ap1 triF (cAd (cAd d1a d1b) d2))
             (cAd (ap1 triF (cAd d1a d1b)) (ap1 triF d2)))
tri_at_cAd_cAd d1a d1b d2 =
  tri_at_cAd_else (cAd d1a d1b) d2 2 (chd_cAd d1a d1b)
    (decideNatNeq 2 0 (\ ())) (decideNatNeq 2 1 (\ ()))

tri_at_cAd_cRO : (d1' d2 : Term) ->
  Deriv (eqF (ap1 triF (cAd (cRO d1') d2)) (cAd (ap1 triF (cRO d1')) (ap1 triF d2)))
tri_at_cAd_cRO d1' d2 =
  tri_at_cAd_else (cRO d1') d2 3 (chd_cRO d1')
    (decideNatNeq 3 0 (\ ())) (decideNatNeq 3 1 (\ ()))

tri_at_cAd_cRS : (d1a d1b d2 : Term) ->
  Deriv (eqF (ap1 triF (cAd (cRS d1a d1b) d2))
             (cAd (ap1 triF (cRS d1a d1b)) (ap1 triF d2)))
tri_at_cAd_cRS d1a d1b d2 =
  tri_at_cAd_else (cRS d1a d1b) d2 4 (chd_cRS d1a d1b)
    (decideNatNeq 4 0 (\ ())) (decideNatNeq 4 1 (\ ()))
