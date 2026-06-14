{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParEnds -- STAGE 4a of HANDOFF-guard-t0-cr.md (the RELATIONAL +
-- CARNEIRO route to internal Church-Rosser, attempt3 §8-§11): the
-- structural endpoint maps  src / tgt  over the parallel-reduction
-- certificates of  T4.ParCert , as RECURSIVE OBJECT functions.
--
-- A certificate (T4.ParCert) is a tagged-pair coding of a  Par-derivation
-- of  T4.ChurchRosserProto :
--     cZe          = Pair (natCode 0) O                    -- pZe
--     cSu d        = Pair (natCode 1) d                    -- pSu d
--     cAd d1 d2    = Pair (natCode 2) (Pair d1 d2)         -- pAd d1 d2
--     cRO d        = Pair (natCode 3) d                    -- pRO d
--     cRS d1 d2    = Pair (natCode 4) (Pair d1 d2)         -- pRS d1 d2
-- The source map  src  reads a cert and rebuilds the SOURCE term of the
-- Par-step it certifies (TrsCodeObj coding ze#/su#/ad#):
--     src(cZe)       = ze#
--     src(cSu d)     = su# (src d)
--     src(cAd d1 d2) = ad# (src d1) (src d2)
--     src(cRO d)     = ad# ze# (src d)
--     src(cRS d1 d2) = ad# (su# (src d1)) (src d2)
-- It is a structural fold over the cert tree, built with  T4.FoldRec.fold
-- (course-of-values; the recursion recovery for the sub-certs is the
-- DEEP correctness, deferred -- see NOTE below).
--
-- THIS FILE delivers the cheap HEAD-TAG-ONLY shallow facts (the §4a note):
-- the head TAG of  src d  is determined by  d's top constructor alone, so
--     hd (src (cX ...)) = tagX-head
-- needs ONLY one fold unfold + the branch dispatch, NOT the recursive-call
-- recovery (no  leq  / lookup machinery).  These head-closure facts are
-- exactly what the consistency atom (§4b head-stability:  ze#-headed and
-- su#-headed terms never join) consumes.
--
-- Construction MIRRORS  T4.NextString  (same  fold + node dispatch
-- plumbing); the step BODY is a 4-way  natEqF  cascade on the cert tag
-- (1..4) that REBUILDS the source term's top constructor.
--
-- NOTE (deferred).  The recursive sub-call slots are  lookupAt  accessors
-- (the honest recursion), but this file proves only the HEAD facts, which
-- are independent of those slots.  The DEEP equations  src (cSu d) =
-- su# (src d)  etc. (recovering  lookupAt = src(child)  under  leq) are
-- left for the next stage; the head facts below do not need them.

module T4.ParEnds where

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

open import T4.TrsCodeObj using
  ( ze# ; su# ; ad# ; tagZe ; tagSu ; tagAd ; hd ; hd_ze )
open import T4.ParCert using
  ( cZe ; cSu ; cAd ; cRO ; cRS )

open import BRA3.Church        using ( pi ; sigma ; tau ; hPi ; T90 ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra   using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.Dispatch      using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  The Cantor-zero collapse  pi O O = O .
--
-- cZe = Pair (natCode 0) O = pi O O , and the Cantor pairing of (0,0) is
-- 0 , so the fold's BASE case (fired at the literal O) handles cZe.
--   pi O O = (R tau sigma hPi) O O = tau O = O      [ax_R_base ; T90]

pi_O_O : Deriv (eqF (ap2 pi O O) O)
pi_O_O = ruleTrans (ax_R_base tau sigma hPi O) T90

------------------------------------------------------------------------
-- SECTION 1.  Child accessors and source cells.

-- left / right child of the node's PAYLOAD (right child of the cert):
--   for cAd / cRS the payload is  Pair d1 d2 , so d1 = Fst (get_rc),
--   d2 = Snd (get_rc).
lcIdx : Fun1
lcIdx = compose1U Fst get_rc

rcIdx : Fun1
rcIdx = compose1U Snd get_rc

-- ze# as a Fun1 constant:  C pi Z Z  applied to anything = pi O O = ze#.
ze#F : Fun1
ze#F = C pi Z Z

-- Source cells: each rebuilds the source's top constructor.
-- su# X = pi (natCode 1) X ;  ad# A B = pi (natCode 2) (pi A B).
cellSu : Fun1                       -- su# (src d)           , d = right child
cellSu = C pi (constN 1) (lookupAt get_rc)

cellAd : Fun1                       -- ad# (src d1) (src d2)
cellAd = C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))

cellRO : Fun1                       -- ad# ze# (src d)       , d = right child
cellRO = C pi (constN 2) (C pi ze#F (lookupAt get_rc))

cellRS : Fun1                       -- ad# (su# (src d1)) (src d2)
cellRS = C pi (constN 2) (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx))

------------------------------------------------------------------------
-- SECTION 2.  The tag-dispatch cascade (tags 1..4 ; tag 0 = base).

test1 : Fun1
test1 = C natEqF get_tag (constN 1)
test2 : Fun1
test2 = C natEqF get_tag (constN 2)
test3 : Fun1
test3 = C natEqF get_tag (constN 3)

inner2 : Fun1                       -- tag3 -> cellRO ; else (tag4) cellRS
inner2 = C condFork (C pi cellRO cellRS) test3

inner1 : Fun1                       -- tag2 -> cellAd ; else inner2
inner1 = C condFork (C pi cellAd inner2) test2

stepBody_src : Fun1                 -- tag1 -> cellSu ; else inner1
stepBody_src = C condFork (C pi cellSu inner1) test1

stepFun_src : Fun2
stepFun_src = Post stepBody_src pi

srcBase : Fun1                      -- O ↦ ze# = pi O O
srcBase = C pi Z Z

src : Fun1
src = fold srcBase stepFun_src

------------------------------------------------------------------------
-- SECTION 3.  Base case:  src cZe = ze# , hence  hd (src cZe) = tagZe .

srcBaseAtO : Deriv (eqF (ap1 srcBase O) ze#)
srcBaseAtO =
  ruleTrans (ax_C pi Z Z O)
    (ruleTrans (congL pi (ap1 Z O) (axZ O))
               (congR pi O (axZ O)))

src_cZe : Deriv (eqF (ap1 src cZe) ze#)
src_cZe =
  ruleTrans (cong1 src pi_O_O)
    (ruleTrans (fold_at_O srcBase stepFun_src) srcBaseAtO)

hd_src_cZe : Deriv (eqF (hd (ap1 src cZe)) tagZe)
hd_src_cZe = ruleTrans (cong1 Fst src_cZe) hd_ze

------------------------------------------------------------------------
-- SECTION 4.  Shared node plumbing (generic in A, b ; from NextString:
-- only  np_unfold  and  np_head  are needed for the head facts).

module NodePlumb (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec srcBase stepFun_src) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  -- src node = stepBody_src input_pkg .
  np_unfold : Deriv (eqF (ap1 src node) (ap1 stepBody_src input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold srcBase stepFun_src A b)
              (axPost stepBody_src pi P_outer (ap1 Snd prev))

  -- get_tag input_pkg = s A .
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

  -- get_rc input_pkg = b  (the cert's right child = the node payload).
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

  -- leq b P_outer  (the right child is bounded by the node predecessor).
  leq_b_P : Deriv (leq b P_outer)
  leq_b_P = leq_sigma_right (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

  -- Recursive-call recovery (generalises NextString.np_lookup to any
  -- sub-position accessor  idx  with value  ct  proved  leq ct P_outer):
  --   lookupAt idx input_pkg  =  src ct .
  np_lookup_gen :
    (idx : Fun1) (ct : Term) ->
    Deriv (eqF (ap1 idx input_pkg) ct) ->
    Deriv (leq ct P_outer) ->
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 src ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt srcBase stepFun_src O P_outer))
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
                              (ap2 (iter Snd) (HistP_sbt srcBase stepFun_src O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt srcBase stepFun_src O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt srcBase stepFun_src O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_src : Deriv (eqF (HPsbt srcBase stepFun_src O ct P_outer) (ap1 src ct))
        HP_to_src = lookup_eq_fold srcBase stepFun_src ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_src

------------------------------------------------------------------------
-- SECTION 5.  The dispatch, generic in (A, b) given the head test values.

module Dispatch (A b : Term) where
  open NodePlumb A b

  pairSu : Term
  pairSu = ap1 (C pi cellSu inner1) input_pkg
  pairAd : Term
  pairAd = ap1 (C pi cellAd inner2) input_pkg
  pairRO : Term
  pairRO = ap1 (C pi cellRO cellRS) input_pkg

  -- pi-projections of the three branch pairs.
  fst_pairSu : Deriv (eqF (ap1 Fst pairSu) (ap1 cellSu input_pkg))
  fst_pairSu = ruleTrans (cong1 Fst (ax_C pi cellSu inner1 input_pkg))
                         (axFst (ap1 cellSu input_pkg) (ap1 inner1 input_pkg))
  snd_pairSu : Deriv (eqF (ap1 Snd pairSu) (ap1 inner1 input_pkg))
  snd_pairSu = ruleTrans (cong1 Snd (ax_C pi cellSu inner1 input_pkg))
                         (axSnd (ap1 cellSu input_pkg) (ap1 inner1 input_pkg))
  fst_pairAd : Deriv (eqF (ap1 Fst pairAd) (ap1 cellAd input_pkg))
  fst_pairAd = ruleTrans (cong1 Fst (ax_C pi cellAd inner2 input_pkg))
                         (axFst (ap1 cellAd input_pkg) (ap1 inner2 input_pkg))
  snd_pairAd : Deriv (eqF (ap1 Snd pairAd) (ap1 inner2 input_pkg))
  snd_pairAd = ruleTrans (cong1 Snd (ax_C pi cellAd inner2 input_pkg))
                         (axSnd (ap1 cellAd input_pkg) (ap1 inner2 input_pkg))
  fst_pairRO : Deriv (eqF (ap1 Fst pairRO) (ap1 cellRO input_pkg))
  fst_pairRO = ruleTrans (cong1 Fst (ax_C pi cellRO cellRS input_pkg))
                         (axFst (ap1 cellRO input_pkg) (ap1 cellRS input_pkg))
  snd_pairRO : Deriv (eqF (ap1 Snd pairRO) (ap1 cellRS input_pkg))
  snd_pairRO = ruleTrans (cong1 Snd (ax_C pi cellRO cellRS input_pkg))
                         (axSnd (ap1 cellRO input_pkg) (ap1 cellRS input_pkg))

  -- stepBody_src input = condFork pairSu (test1 input).
  sb_eq : Deriv (eqF (ap1 stepBody_src input_pkg)
                     (ap2 condFork pairSu (ap1 test1 input_pkg)))
  sb_eq = ax_C condFork (C pi cellSu inner1) test1 input_pkg

  inner1_eq : Deriv (eqF (ap1 inner1 input_pkg)
                         (ap2 condFork pairAd (ap1 test2 input_pkg)))
  inner1_eq = ax_C condFork (C pi cellAd inner2) test2 input_pkg

  inner2_eq : Deriv (eqF (ap1 inner2 input_pkg)
                         (ap2 condFork pairRO (ap1 test3 input_pkg)))
  inner2_eq = ax_C condFork (C pi cellRO cellRS) test3 input_pkg

  -- test_k input = natEqF (s A) (natCode k).
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

  -- cell head values:  Fst (cell input) = natCode k .
  cellSu_head : Deriv (eqF (ap1 Fst (ap1 cellSu input_pkg)) (natCode 1))
  cellSu_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 1) (lookupAt get_rc) input_pkg))
      (ruleTrans (axFst (ap1 (constN 1) input_pkg) (ap1 (lookupAt get_rc) input_pkg))
                 (constN_eq 1 input_pkg))
  cellAd_head : Deriv (eqF (ap1 Fst (ap1 cellAd input_pkg)) (natCode 2))
  cellAd_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg))
      (ruleTrans (axFst (ap1 (constN 2) input_pkg)
                        (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg))
                 (constN_eq 2 input_pkg))
  cellRO_head : Deriv (eqF (ap1 Fst (ap1 cellRO input_pkg)) (natCode 2))
  cellRO_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 2) (C pi ze#F (lookupAt get_rc)) input_pkg))
      (ruleTrans (axFst (ap1 (constN 2) input_pkg)
                        (ap1 (C pi ze#F (lookupAt get_rc)) input_pkg))
                 (constN_eq 2 input_pkg))
  cellRS_head : Deriv (eqF (ap1 Fst (ap1 cellRS input_pkg)) (natCode 2))
  cellRS_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 2)
                            (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg))
      (ruleTrans (axFst (ap1 (constN 2) input_pkg)
                        (ap1 (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg))
                 (constN_eq 2 input_pkg))

------------------------------------------------------------------------
-- SECTION 6.  The five source head-closure facts.
--   tagSu = natCode 1 , tagAd = natCode 2 (TrsCodeObj).

-- cSu d : node = pi (s O) d , A = O ; test1 fires.
hd_src_cSu : (d : Term) -> Deriv (eqF (hd (ap1 src (cSu d))) tagSu)
hd_src_cSu d =
  let open NodePlumb O d
      open Dispatch O d
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 src (cSu d)) (ap1 cellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairSu t1_fire)
              (ruleTrans (condFork_true_nc pairSu O) fst_pairSu)))
  in ruleTrans (cong1 Fst to_cell) cellSu_head

-- cAd d1 d2 : node = pi (s (natCode 1)) (Pair d1 d2) , A = natCode 1 ;
--   test1 skip, test2 fires.
hd_src_cAd : (d1 d2 : Term) -> Deriv (eqF (hd (ap1 src (cAd d1 d2))) tagAd)
hd_src_cAd d1 d2 =
  let open NodePlumb (natCode 1) (ap2 pi d1 d2)
      open Dispatch (natCode 1) (ap2 pi d1 d2)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      to_inner1 : Deriv (eqF (ap1 stepBody_src input_pkg) (ap1 inner1 input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq 2)
      inner1_to_cell : Deriv (eqF (ap1 inner1 input_pkg) (ap1 cellAd input_pkg))
      inner1_to_cell =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_fire)
            (ruleTrans (condFork_true_nc pairAd O) fst_pairAd))
      to_cell : Deriv (eqF (ap1 src (cAd d1 d2)) (ap1 cellAd input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 inner1_to_cell)
  in ruleTrans (cong1 Fst to_cell) cellAd_head

-- cRO d : node = pi (s (natCode 2)) d , A = natCode 2 ;
--   test1, test2 skip, test3 fires.
hd_src_cRO : (d : Term) -> Deriv (eqF (hd (ap1 src (cRO d))) tagAd)
hd_src_cRO d =
  let open NodePlumb (natCode 2) d
      open Dispatch (natCode 2) d
      w31 : NatNeqWitness 3 1
      w31 = decideNatNeq 3 1 (\ ())
      w32 : NatNeqWitness 3 2
      w32 = decideNatNeq 3 2 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 3 1 w31)
      to_inner1 : Deriv (eqF (ap1 stepBody_src input_pkg) (ap1 inner1 input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 3 2 w32)
      to_inner2 : Deriv (eqF (ap1 inner1 input_pkg) (ap1 inner2 input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_fire : Deriv (eqF (ap1 test3 input_pkg) (ap1 s O))
      t3_fire = ruleTrans test3_val (natEq_eq 3)
      inner2_to_cell : Deriv (eqF (ap1 inner2 input_pkg) (ap1 cellRO input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_fire)
            (ruleTrans (condFork_true_nc pairRO O) fst_pairRO))
      to_cell : Deriv (eqF (ap1 src (cRO d)) (ap1 cellRO input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
  in ruleTrans (cong1 Fst to_cell) cellRO_head

-- cRS d1 d2 : node = pi (s (natCode 3)) (Pair d1 d2) , A = natCode 3 ;
--   test1, test2, test3 all skip -> cellRS.
hd_src_cRS : (d1 d2 : Term) -> Deriv (eqF (hd (ap1 src (cRS d1 d2))) tagAd)
hd_src_cRS d1 d2 =
  let open NodePlumb (natCode 3) (ap2 pi d1 d2)
      open Dispatch (natCode 3) (ap2 pi d1 d2)
      w41 : NatNeqWitness 4 1
      w41 = decideNatNeq 4 1 (\ ())
      w42 : NatNeqWitness 4 2
      w42 = decideNatNeq 4 2 (\ ())
      w43 : NatNeqWitness 4 3
      w43 = decideNatNeq 4 3 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 4 1 w41)
      to_inner1 : Deriv (eqF (ap1 stepBody_src input_pkg) (ap1 inner1 input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 4 2 w42)
      to_inner2 : Deriv (eqF (ap1 inner1 input_pkg) (ap1 inner2 input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_O : Deriv (eqF (ap1 test3 input_pkg) O)
      t3_O = ruleTrans test3_val (natEqF_at_neq 4 3 w43)
      inner2_to_cell : Deriv (eqF (ap1 inner2 input_pkg) (ap1 cellRS input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_O)
            (ruleTrans (condFork_false pairRO) snd_pairRO))
      to_cell : Deriv (eqF (ap1 src (cRS d1 d2)) (ap1 cellRS input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
  in ruleTrans (cong1 Fst to_cell) cellRS_head

------------------------------------------------------------------------
-- SECTION 6b.  DEEP source equations, UNARY cases (right-child recursion
-- only -- leq_sigma_right, no left-child bound needed).
--   src(cSu d) = su# (src d) ;  src(cRO d) = ad# ze# (src d) .

ze#F_value : (e : Term) -> Deriv (eqF (ap1 ze#F e) ze#)
ze#F_value e =
  ruleTrans (ax_C pi Z Z e)
    (ruleTrans (congL pi (ap1 Z e) (axZ e)) (congR pi O (axZ e)))

src_cSu : (d : Term) -> Deriv (eqF (ap1 src (cSu d)) (su# (ap1 src d)))
src_cSu d =
  let open NodePlumb O d
      open Dispatch O d
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 src (cSu d)) (ap1 cellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairSu t1_fire)
              (ruleTrans (condFork_true_nc pairSu O) fst_pairSu)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 src d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
      cellSu_value : Deriv (eqF (ap1 cellSu input_pkg) (su# (ap1 src d)))
      cellSu_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec))
  in ruleTrans to_cell cellSu_value

src_cRO : (d : Term) -> Deriv (eqF (ap1 src (cRO d)) (ad# ze# (ap1 src d)))
src_cRO d =
  let open NodePlumb (natCode 2) d
      open Dispatch (natCode 2) d
      w31 : NatNeqWitness 3 1
      w31 = decideNatNeq 3 1 (\ ())
      w32 : NatNeqWitness 3 2
      w32 = decideNatNeq 3 2 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 3 1 w31)
      to_inner1 : Deriv (eqF (ap1 stepBody_src input_pkg) (ap1 inner1 input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 3 2 w32)
      to_inner2 : Deriv (eqF (ap1 inner1 input_pkg) (ap1 inner2 input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_fire : Deriv (eqF (ap1 test3 input_pkg) (ap1 s O))
      t3_fire = ruleTrans test3_val (natEq_eq 3)
      inner2_to_cell : Deriv (eqF (ap1 inner2 input_pkg) (ap1 cellRO input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_fire)
            (ruleTrans (condFork_true_nc pairRO O) fst_pairRO))
      to_cell : Deriv (eqF (ap1 src (cRO d)) (ap1 cellRO input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 src d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
      inner_value : Deriv (eqF (ap1 (C pi ze#F (lookupAt get_rc)) input_pkg)
                                (ap2 pi ze# (ap1 src d)))
      inner_value =
        ruleTrans (ax_C pi ze#F (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (ze#F_value input_pkg))
                     (congR pi ze# rec))
      cellRO_value : Deriv (eqF (ap1 cellRO input_pkg) (ad# ze# (ap1 src d)))
      cellRO_value =
        ruleTrans (ax_C pi (constN 2) (C pi ze#F (lookupAt get_rc)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi ze#F (lookupAt get_rc)) input_pkg) (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_value))
  in ruleTrans to_cell cellRO_value

------------------------------------------------------------------------
-- SECTION 6c.  DEEP source equations, BINARY cases (both children:
-- right via leq_pi_right, LEFT via leq_pi_left = the Cantor 1st-coordinate
-- bound, T4.LeqPiLeft).
--   src(cAd d1 d2) = ad# (src d1) (src d2) ;
--   src(cRS d1 d2) = ad# (su# (src d1)) (src d2) .

src_cAd : (d1 d2 : Term) ->
  Deriv (eqF (ap1 src (cAd d1 d2)) (ad# (ap1 src d1) (ap1 src d2)))
src_cAd d1 d2 =
  let open NodePlumb (natCode 1) (ap2 pi d1 d2)
      open Dispatch (natCode 1) (ap2 pi d1 d2)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      to_inner1 : Deriv (eqF (ap1 stepBody_src input_pkg) (ap1 inner1 input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq 2)
      inner1_to_cell : Deriv (eqF (ap1 inner1 input_pkg) (ap1 cellAd input_pkg))
      inner1_to_cell =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_fire)
            (ruleTrans (condFork_true_nc pairAd O) fst_pairAd))
      to_cell : Deriv (eqF (ap1 src (cAd d1 d2)) (ap1 cellAd input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 inner1_to_cell)
      -- child positions and bounds
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
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 src d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 src d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      inner_value : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                                (ap2 pi (ap1 src d1) (ap1 src d2)))
      inner_value =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 src d1) rec2))
      cellAd_value : Deriv (eqF (ap1 cellAd input_pkg) (ad# (ap1 src d1) (ap1 src d2)))
      cellAd_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_value))
  in ruleTrans to_cell cellAd_value

src_cRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 src (cRS d1 d2)) (ad# (su# (ap1 src d1)) (ap1 src d2)))
src_cRS d1 d2 =
  let open NodePlumb (natCode 3) (ap2 pi d1 d2)
      open Dispatch (natCode 3) (ap2 pi d1 d2)
      w41 : NatNeqWitness 4 1
      w41 = decideNatNeq 4 1 (\ ())
      w42 : NatNeqWitness 4 2
      w42 = decideNatNeq 4 2 (\ ())
      w43 : NatNeqWitness 4 3
      w43 = decideNatNeq 4 3 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 4 1 w41)
      to_inner1 : Deriv (eqF (ap1 stepBody_src input_pkg) (ap1 inner1 input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 4 2 w42)
      to_inner2 : Deriv (eqF (ap1 inner1 input_pkg) (ap1 inner2 input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_O : Deriv (eqF (ap1 test3 input_pkg) O)
      t3_O = ruleTrans test3_val (natEqF_at_neq 4 3 w43)
      inner2_to_cell : Deriv (eqF (ap1 inner2 input_pkg) (ap1 cellRS input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_O)
            (ruleTrans (condFork_false pairRO) snd_pairRO))
      to_cell : Deriv (eqF (ap1 src (cRS d1 d2)) (ap1 cellRS input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
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
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 src d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 src d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      -- su# (src d1) = pi (natCode 1) (src d1)
      suL_value : Deriv (eqF (ap1 (C pi (constN 1) (lookupAt lcIdx)) input_pkg)
                              (su# (ap1 src d1)))
      suL_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt lcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt lcIdx) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec1))
      inner_value : Deriv (eqF (ap1 (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                                (ap2 pi (su# (ap1 src d1)) (ap1 src d2)))
      inner_value =
        ruleTrans (ax_C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) suL_value)
                     (congR pi (su# (ap1 src d1)) rec2))
      cellRS_value : Deriv (eqF (ap1 cellRS input_pkg) (ad# (su# (ap1 src d1)) (ap1 src d2)))
      cellRS_value =
        ruleTrans (ax_C pi (constN 2)
                     (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (C pi (constN 1) (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_value))
  in ruleTrans to_cell cellRS_value

------------------------------------------------------------------------
-- SECTION 7.  The TARGET map  tgt .
--
--     tgt(cZe)       = ze#
--     tgt(cSu d)     = su# (tgt d)
--     tgt(cAd d1 d2) = ad# (tgt d1) (tgt d2)
--     tgt(cRO d)     = tgt d                          -- RECURSIVE head
--     tgt(cRS d1 d2) = su# (ad# (tgt d1) (tgt d2))
-- Same fold skeleton as  src ; the cells differ at RO (bare recursive
-- lookup, no wrapper) and RS (su# wrapping ad#).  Heads:
--   cZe->tagZe , cSu->tagSu , cAd->tagAd , cRS->tagSu  are SHALLOW ;
--   cRO->head(tgt sub)  is NOT shallow (the head equals the head of the
--   sub-cert's target) and is DEFERRED -- the consistency atom never
--   enters it (cRO has an  ad#-headed source, not  ze#).

tCellSu : Fun1                      -- su# (tgt d)
tCellSu = C pi (constN 1) (lookupAt get_rc)

tCellAd : Fun1                      -- ad# (tgt d1) (tgt d2)
tCellAd = C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))

tCellRO : Fun1                      -- tgt d  (bare recursive lookup)
tCellRO = lookupAt get_rc

tCellRS : Fun1                      -- su# (ad# (tgt d1) (tgt d2))
tCellRS = C pi (constN 1) (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)))

inner2_t : Fun1                     -- tag3 -> tCellRO ; else (tag4) tCellRS
inner2_t = C condFork (C pi tCellRO tCellRS) test3

inner1_t : Fun1                     -- tag2 -> tCellAd ; else inner2_t
inner1_t = C condFork (C pi tCellAd inner2_t) test2

stepBody_tgt : Fun1                 -- tag1 -> tCellSu ; else inner1_t
stepBody_tgt = C condFork (C pi tCellSu inner1_t) test1

stepFun_tgt : Fun2
stepFun_tgt = Post stepBody_tgt pi

tgt : Fun1
tgt = fold srcBase stepFun_tgt      -- same base: O ↦ ze#

------------------------------------------------------------------------
-- Base case:  tgt cZe = ze# , hd (tgt cZe) = tagZe .

tgt_cZe : Deriv (eqF (ap1 tgt cZe) ze#)
tgt_cZe =
  ruleTrans (cong1 tgt pi_O_O)
    (ruleTrans (fold_at_O srcBase stepFun_tgt) srcBaseAtO)

hd_tgt_cZe : Deriv (eqF (hd (ap1 tgt cZe)) tagZe)
hd_tgt_cZe = ruleTrans (cong1 Fst tgt_cZe) hd_ze

------------------------------------------------------------------------
-- Node plumbing and dispatch for  tgt .

module NodePlumbT (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec srcBase stepFun_tgt) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  np_unfold : Deriv (eqF (ap1 tgt node) (ap1 stepBody_tgt input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold srcBase stepFun_tgt A b)
              (axPost stepBody_tgt pi P_outer (ap1 Snd prev))

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
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 tgt ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt srcBase stepFun_tgt O P_outer))
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
                              (ap2 (iter Snd) (HistP_sbt srcBase stepFun_tgt O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt srcBase stepFun_tgt O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt srcBase stepFun_tgt O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_tgt : Deriv (eqF (HPsbt srcBase stepFun_tgt O ct P_outer) (ap1 tgt ct))
        HP_to_tgt = lookup_eq_fold srcBase stepFun_tgt ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_tgt

module DispatchT (A b : Term) where
  open NodePlumbT A b

  pairSu : Term
  pairSu = ap1 (C pi tCellSu inner1_t) input_pkg
  pairAd : Term
  pairAd = ap1 (C pi tCellAd inner2_t) input_pkg
  pairRO : Term
  pairRO = ap1 (C pi tCellRO tCellRS) input_pkg

  fst_pairSu : Deriv (eqF (ap1 Fst pairSu) (ap1 tCellSu input_pkg))
  fst_pairSu = ruleTrans (cong1 Fst (ax_C pi tCellSu inner1_t input_pkg))
                         (axFst (ap1 tCellSu input_pkg) (ap1 inner1_t input_pkg))
  snd_pairSu : Deriv (eqF (ap1 Snd pairSu) (ap1 inner1_t input_pkg))
  snd_pairSu = ruleTrans (cong1 Snd (ax_C pi tCellSu inner1_t input_pkg))
                         (axSnd (ap1 tCellSu input_pkg) (ap1 inner1_t input_pkg))
  fst_pairAd : Deriv (eqF (ap1 Fst pairAd) (ap1 tCellAd input_pkg))
  fst_pairAd = ruleTrans (cong1 Fst (ax_C pi tCellAd inner2_t input_pkg))
                         (axFst (ap1 tCellAd input_pkg) (ap1 inner2_t input_pkg))
  snd_pairAd : Deriv (eqF (ap1 Snd pairAd) (ap1 inner2_t input_pkg))
  snd_pairAd = ruleTrans (cong1 Snd (ax_C pi tCellAd inner2_t input_pkg))
                         (axSnd (ap1 tCellAd input_pkg) (ap1 inner2_t input_pkg))
  fst_pairRO : Deriv (eqF (ap1 Fst pairRO) (ap1 tCellRO input_pkg))
  fst_pairRO = ruleTrans (cong1 Fst (ax_C pi tCellRO tCellRS input_pkg))
                         (axFst (ap1 tCellRO input_pkg) (ap1 tCellRS input_pkg))
  snd_pairRO : Deriv (eqF (ap1 Snd pairRO) (ap1 tCellRS input_pkg))
  snd_pairRO = ruleTrans (cong1 Snd (ax_C pi tCellRO tCellRS input_pkg))
                         (axSnd (ap1 tCellRO input_pkg) (ap1 tCellRS input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody_tgt input_pkg)
                     (ap2 condFork pairSu (ap1 test1 input_pkg)))
  sb_eq = ax_C condFork (C pi tCellSu inner1_t) test1 input_pkg

  inner1_eq : Deriv (eqF (ap1 inner1_t input_pkg)
                         (ap2 condFork pairAd (ap1 test2 input_pkg)))
  inner1_eq = ax_C condFork (C pi tCellAd inner2_t) test2 input_pkg

  inner2_eq : Deriv (eqF (ap1 inner2_t input_pkg)
                         (ap2 condFork pairRO (ap1 test3 input_pkg)))
  inner2_eq = ax_C condFork (C pi tCellRO tCellRS) test3 input_pkg

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

  tCellSu_head : Deriv (eqF (ap1 Fst (ap1 tCellSu input_pkg)) (natCode 1))
  tCellSu_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 1) (lookupAt get_rc) input_pkg))
      (ruleTrans (axFst (ap1 (constN 1) input_pkg) (ap1 (lookupAt get_rc) input_pkg))
                 (constN_eq 1 input_pkg))
  tCellAd_head : Deriv (eqF (ap1 Fst (ap1 tCellAd input_pkg)) (natCode 2))
  tCellAd_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg))
      (ruleTrans (axFst (ap1 (constN 2) input_pkg)
                        (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg))
                 (constN_eq 2 input_pkg))
  tCellRS_head : Deriv (eqF (ap1 Fst (ap1 tCellRS input_pkg)) (natCode 1))
  tCellRS_head =
    ruleTrans (cong1 Fst (ax_C pi (constN 1)
                            (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg))
      (ruleTrans (axFst (ap1 (constN 1) input_pkg)
                        (ap1 (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg))
                 (constN_eq 1 input_pkg))

------------------------------------------------------------------------
-- SECTION 8.  The four SHALLOW target head-closure facts.

hd_tgt_cSu : (d : Term) -> Deriv (eqF (hd (ap1 tgt (cSu d))) tagSu)
hd_tgt_cSu d =
  let open NodePlumbT O d
      open DispatchT O d
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 tgt (cSu d)) (ap1 tCellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairSu t1_fire)
              (ruleTrans (condFork_true_nc pairSu O) fst_pairSu)))
  in ruleTrans (cong1 Fst to_cell) tCellSu_head

hd_tgt_cAd : (d1 d2 : Term) -> Deriv (eqF (hd (ap1 tgt (cAd d1 d2))) tagAd)
hd_tgt_cAd d1 d2 =
  let open NodePlumbT (natCode 1) (ap2 pi d1 d2)
      open DispatchT (natCode 1) (ap2 pi d1 d2)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      to_inner1 : Deriv (eqF (ap1 stepBody_tgt input_pkg) (ap1 inner1_t input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq 2)
      inner1_to_cell : Deriv (eqF (ap1 inner1_t input_pkg) (ap1 tCellAd input_pkg))
      inner1_to_cell =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_fire)
            (ruleTrans (condFork_true_nc pairAd O) fst_pairAd))
      to_cell : Deriv (eqF (ap1 tgt (cAd d1 d2)) (ap1 tCellAd input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 inner1_to_cell)
  in ruleTrans (cong1 Fst to_cell) tCellAd_head

hd_tgt_cRS : (d1 d2 : Term) -> Deriv (eqF (hd (ap1 tgt (cRS d1 d2))) tagSu)
hd_tgt_cRS d1 d2 =
  let open NodePlumbT (natCode 3) (ap2 pi d1 d2)
      open DispatchT (natCode 3) (ap2 pi d1 d2)
      w41 : NatNeqWitness 4 1
      w41 = decideNatNeq 4 1 (\ ())
      w42 : NatNeqWitness 4 2
      w42 = decideNatNeq 4 2 (\ ())
      w43 : NatNeqWitness 4 3
      w43 = decideNatNeq 4 3 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 4 1 w41)
      to_inner1 : Deriv (eqF (ap1 stepBody_tgt input_pkg) (ap1 inner1_t input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 4 2 w42)
      to_inner2 : Deriv (eqF (ap1 inner1_t input_pkg) (ap1 inner2_t input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_O : Deriv (eqF (ap1 test3 input_pkg) O)
      t3_O = ruleTrans test3_val (natEqF_at_neq 4 3 w43)
      inner2_to_cell : Deriv (eqF (ap1 inner2_t input_pkg) (ap1 tCellRS input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_O)
            (ruleTrans (condFork_false pairRO) snd_pairRO))
      to_cell : Deriv (eqF (ap1 tgt (cRS d1 d2)) (ap1 tCellRS input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
  in ruleTrans (cong1 Fst to_cell) tCellRS_head

------------------------------------------------------------------------
-- SECTION 9.  The validity checker  isCert  (returns O = "valid").
--
--     isCert(cZe)       = O
--     isCert(cSu d)     = isCert d
--     isCert(cAd d1 d2) = pi (isCert d1) (isCert d2)
--     isCert(cRO d)     = isCert d
--     isCert(cRS d1 d2) = pi (isCert d1) (isCert d2)
--     isCert(invalid)   = s O
-- The conjunction for the binary nodes is the CANTOR PAIR itself:
--   pi a b = O  iff  a = b = O  (Cantor (0,0)=0 and pi is injective), so
--   isCert d = O  iff  d is a well-tagged tree.  No extra primitive.
--
-- THIS FILE proves only the BASE equation  isCert cZe = O  (shallow, from
-- the fold base).  The recursive sub-equations  isCert(cSu d) = isCert d
-- etc. need the recursive-call recovery (leq / lookup), the same deferred
-- machinery as the DEEP src/tgt correctness -- next stage.

test4 : Fun1
test4 = C natEqF get_tag (constN 4)

icCellSu : Fun1                     -- isCert d
icCellSu = lookupAt get_rc
icCellAd : Fun1                     -- pi (isCert d1) (isCert d2)
icCellAd = C pi (lookupAt lcIdx) (lookupAt rcIdx)
icCellRO : Fun1                     -- isCert d
icCellRO = lookupAt get_rc
icCellRS : Fun1                     -- pi (isCert d1) (isCert d2)
icCellRS = C pi (lookupAt lcIdx) (lookupAt rcIdx)
invalidF : Fun1                     -- s O  (nonzero = invalid)
invalidF = constN 1

inner3_ic : Fun1                    -- tag4 -> icCellRS ; else invalid
inner3_ic = C condFork (C pi icCellRS invalidF) test4
inner2_ic : Fun1                    -- tag3 -> icCellRO ; else inner3_ic
inner2_ic = C condFork (C pi icCellRO inner3_ic) test3
inner1_ic : Fun1                    -- tag2 -> icCellAd ; else inner2_ic
inner1_ic = C condFork (C pi icCellAd inner2_ic) test2
stepBody_ic : Fun1                  -- tag1 -> icCellSu ; else inner1_ic
stepBody_ic = C condFork (C pi icCellSu inner1_ic) test1

stepFun_ic : Fun2
stepFun_ic = Post stepBody_ic pi

isCert : Fun1
isCert = fold Z stepFun_ic          -- base: O ↦ O (= valid leaf)

isCert_cZe : Deriv (eqF (ap1 isCert cZe) O)
isCert_cZe =
  ruleTrans (cong1 isCert pi_O_O)
    (ruleTrans (fold_at_O Z stepFun_ic) (axZ O))

------------------------------------------------------------------------
-- SECTION 10.  DEEP target equations (all four recursive cases, incl. the
-- non-shallow cRO whose head was deferred in SECTION 8).
--   tgt(cSu d)     = su# (tgt d)
--   tgt(cAd d1 d2) = ad# (tgt d1) (tgt d2)
--   tgt(cRO d)     = tgt d
--   tgt(cRS d1 d2) = su# (ad# (tgt d1) (tgt d2))

tgt_cSu : (d : Term) -> Deriv (eqF (ap1 tgt (cSu d)) (su# (ap1 tgt d)))
tgt_cSu d =
  let open NodePlumbT O d
      open DispatchT O d
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 tgt (cSu d)) (ap1 tCellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairSu t1_fire)
              (ruleTrans (condFork_true_nc pairSu O) fst_pairSu)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 tgt d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
      tCellSu_value : Deriv (eqF (ap1 tCellSu input_pkg) (su# (ap1 tgt d)))
      tCellSu_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec))
  in ruleTrans to_cell tCellSu_value

tgt_cRO : (d : Term) -> Deriv (eqF (ap1 tgt (cRO d)) (ap1 tgt d))
tgt_cRO d =
  let open NodePlumbT (natCode 2) d
      open DispatchT (natCode 2) d
      w31 : NatNeqWitness 3 1
      w31 = decideNatNeq 3 1 (\ ())
      w32 : NatNeqWitness 3 2
      w32 = decideNatNeq 3 2 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 3 1 w31)
      to_inner1 : Deriv (eqF (ap1 stepBody_tgt input_pkg) (ap1 inner1_t input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 3 2 w32)
      to_inner2 : Deriv (eqF (ap1 inner1_t input_pkg) (ap1 inner2_t input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_fire : Deriv (eqF (ap1 test3 input_pkg) (ap1 s O))
      t3_fire = ruleTrans test3_val (natEq_eq 3)
      inner2_to_cell : Deriv (eqF (ap1 inner2_t input_pkg) (ap1 tCellRO input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_fire)
            (ruleTrans (condFork_true_nc pairRO O) fst_pairRO))
      to_cell : Deriv (eqF (ap1 tgt (cRO d)) (ap1 tCellRO input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
      -- tCellRO = lookupAt get_rc , and the recovery gives tgt d directly.
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 tgt d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
  in ruleTrans to_cell rec

-- The cRO head fact, now obtainable from the deep equation: the head of
-- tgt(cRO d) equals the head of tgt d (NOT a constant -- the case the
-- shallow SECTION 8 deferred).
hd_tgt_cRO : (d : Term) -> Deriv (eqF (hd (ap1 tgt (cRO d))) (hd (ap1 tgt d)))
hd_tgt_cRO d = cong1 Fst (tgt_cRO d)

tgt_cAd : (d1 d2 : Term) ->
  Deriv (eqF (ap1 tgt (cAd d1 d2)) (ad# (ap1 tgt d1) (ap1 tgt d2)))
tgt_cAd d1 d2 =
  let open NodePlumbT (natCode 1) (ap2 pi d1 d2)
      open DispatchT (natCode 1) (ap2 pi d1 d2)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      to_inner1 : Deriv (eqF (ap1 stepBody_tgt input_pkg) (ap1 inner1_t input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq 2)
      inner1_to_cell : Deriv (eqF (ap1 inner1_t input_pkg) (ap1 tCellAd input_pkg))
      inner1_to_cell =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_fire)
            (ruleTrans (condFork_true_nc pairAd O) fst_pairAd))
      to_cell : Deriv (eqF (ap1 tgt (cAd d1 d2)) (ap1 tCellAd input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 inner1_to_cell)
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
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 tgt d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 tgt d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      inner_value : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                                (ap2 pi (ap1 tgt d1) (ap1 tgt d2)))
      inner_value =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 tgt d1) rec2))
      tCellAd_value : Deriv (eqF (ap1 tCellAd input_pkg) (ad# (ap1 tgt d1) (ap1 tgt d2)))
      tCellAd_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_value))
  in ruleTrans to_cell tCellAd_value

tgt_cRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 tgt (cRS d1 d2)) (su# (ad# (ap1 tgt d1) (ap1 tgt d2))))
tgt_cRS d1 d2 =
  let open NodePlumbT (natCode 3) (ap2 pi d1 d2)
      open DispatchT (natCode 3) (ap2 pi d1 d2)
      w41 : NatNeqWitness 4 1
      w41 = decideNatNeq 4 1 (\ ())
      w42 : NatNeqWitness 4 2
      w42 = decideNatNeq 4 2 (\ ())
      w43 : NatNeqWitness 4 3
      w43 = decideNatNeq 4 3 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 4 1 w41)
      to_inner1 : Deriv (eqF (ap1 stepBody_tgt input_pkg) (ap1 inner1_t input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 4 2 w42)
      to_inner2 : Deriv (eqF (ap1 inner1_t input_pkg) (ap1 inner2_t input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_O : Deriv (eqF (ap1 test3 input_pkg) O)
      t3_O = ruleTrans test3_val (natEqF_at_neq 4 3 w43)
      inner2_to_cell : Deriv (eqF (ap1 inner2_t input_pkg) (ap1 tCellRS input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_O)
            (ruleTrans (condFork_false pairRO) snd_pairRO))
      to_cell : Deriv (eqF (ap1 tgt (cRS d1 d2)) (ap1 tCellRS input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
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
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 tgt d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 tgt d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      ad_value : Deriv (eqF (ap1 (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg)
                             (ad# (ap1 tgt d1) (ap1 tgt d2)))
      ad_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2)
                       (ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
                         (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                                    (congR pi (ap1 tgt d1) rec2)))))
      tCellRS_value : Deriv (eqF (ap1 tCellRS input_pkg)
                                  (su# (ad# (ap1 tgt d1) (ap1 tgt d2))))
      tCellRS_value =
        ruleTrans (ax_C pi (constN 1)
                     (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))) input_pkg)
                               (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) ad_value))
  in ruleTrans to_cell tCellRS_value

------------------------------------------------------------------------
-- SECTION 11.  DEEP validity equations (the recursive cases).
--   isCert(cSu d)     = isCert d
--   isCert(cAd d1 d2) = pi (isCert d1) (isCert d2)
--   isCert(cRO d)     = isCert d
--   isCert(cRS d1 d2) = pi (isCert d1) (isCert d2)
-- (pi a b = O iff a = b = O, so isCert d = O iff d is a well-tagged tree.)

module NodePlumbIC (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec Z stepFun_ic) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  np_unfold : Deriv (eqF (ap1 isCert node) (ap1 stepBody_ic input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold Z stepFun_ic A b)
              (axPost stepBody_ic pi P_outer (ap1 Snd prev))

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
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 isCert ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt Z stepFun_ic O P_outer))
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
                              (ap2 (iter Snd) (HistP_sbt Z stepFun_ic O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt Z stepFun_ic O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt Z stepFun_ic O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_ic : Deriv (eqF (HPsbt Z stepFun_ic O ct P_outer) (ap1 isCert ct))
        HP_to_ic = lookup_eq_fold Z stepFun_ic ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_ic

module DispatchIC (A b : Term) where
  open NodePlumbIC A b

  pairSu : Term
  pairSu = ap1 (C pi icCellSu inner1_ic) input_pkg
  pairAd : Term
  pairAd = ap1 (C pi icCellAd inner2_ic) input_pkg
  pairRO : Term
  pairRO = ap1 (C pi icCellRO inner3_ic) input_pkg
  pairRS : Term
  pairRS = ap1 (C pi icCellRS invalidF) input_pkg

  fst_pairSu : Deriv (eqF (ap1 Fst pairSu) (ap1 icCellSu input_pkg))
  fst_pairSu = ruleTrans (cong1 Fst (ax_C pi icCellSu inner1_ic input_pkg))
                         (axFst (ap1 icCellSu input_pkg) (ap1 inner1_ic input_pkg))
  snd_pairSu : Deriv (eqF (ap1 Snd pairSu) (ap1 inner1_ic input_pkg))
  snd_pairSu = ruleTrans (cong1 Snd (ax_C pi icCellSu inner1_ic input_pkg))
                         (axSnd (ap1 icCellSu input_pkg) (ap1 inner1_ic input_pkg))
  fst_pairAd : Deriv (eqF (ap1 Fst pairAd) (ap1 icCellAd input_pkg))
  fst_pairAd = ruleTrans (cong1 Fst (ax_C pi icCellAd inner2_ic input_pkg))
                         (axFst (ap1 icCellAd input_pkg) (ap1 inner2_ic input_pkg))
  snd_pairAd : Deriv (eqF (ap1 Snd pairAd) (ap1 inner2_ic input_pkg))
  snd_pairAd = ruleTrans (cong1 Snd (ax_C pi icCellAd inner2_ic input_pkg))
                         (axSnd (ap1 icCellAd input_pkg) (ap1 inner2_ic input_pkg))
  fst_pairRO : Deriv (eqF (ap1 Fst pairRO) (ap1 icCellRO input_pkg))
  fst_pairRO = ruleTrans (cong1 Fst (ax_C pi icCellRO inner3_ic input_pkg))
                         (axFst (ap1 icCellRO input_pkg) (ap1 inner3_ic input_pkg))
  snd_pairRO : Deriv (eqF (ap1 Snd pairRO) (ap1 inner3_ic input_pkg))
  snd_pairRO = ruleTrans (cong1 Snd (ax_C pi icCellRO inner3_ic input_pkg))
                         (axSnd (ap1 icCellRO input_pkg) (ap1 inner3_ic input_pkg))
  fst_pairRS : Deriv (eqF (ap1 Fst pairRS) (ap1 icCellRS input_pkg))
  fst_pairRS = ruleTrans (cong1 Fst (ax_C pi icCellRS invalidF input_pkg))
                         (axFst (ap1 icCellRS input_pkg) (ap1 invalidF input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody_ic input_pkg)
                     (ap2 condFork pairSu (ap1 test1 input_pkg)))
  sb_eq = ax_C condFork (C pi icCellSu inner1_ic) test1 input_pkg
  inner1_eq : Deriv (eqF (ap1 inner1_ic input_pkg)
                         (ap2 condFork pairAd (ap1 test2 input_pkg)))
  inner1_eq = ax_C condFork (C pi icCellAd inner2_ic) test2 input_pkg
  inner2_eq : Deriv (eqF (ap1 inner2_ic input_pkg)
                         (ap2 condFork pairRO (ap1 test3 input_pkg)))
  inner2_eq = ax_C condFork (C pi icCellRO inner3_ic) test3 input_pkg
  inner3_eq : Deriv (eqF (ap1 inner3_ic input_pkg)
                         (ap2 condFork pairRS (ap1 test4 input_pkg)))
  inner3_eq = ax_C condFork (C pi icCellRS invalidF) test4 input_pkg

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
  test4_val : Deriv (eqF (ap1 test4 input_pkg) (ap2 natEqF (ap1 s A) (natCode 4)))
  test4_val =
    ruleTrans (ax_C natEqF get_tag (constN 4) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 4) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 4 input_pkg)))

-- isCert(cSu d) = isCert d .
isCert_cSu : (d : Term) -> Deriv (eqF (ap1 isCert (cSu d)) (ap1 isCert d))
isCert_cSu d =
  let open NodePlumbIC O d
      open DispatchIC O d
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 isCert (cSu d)) (ap1 icCellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairSu t1_fire)
              (ruleTrans (condFork_true_nc pairSu O) fst_pairSu)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 isCert d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
  in ruleTrans to_cell rec

-- isCert(cRO d) = isCert d .
isCert_cRO : (d : Term) -> Deriv (eqF (ap1 isCert (cRO d)) (ap1 isCert d))
isCert_cRO d =
  let open NodePlumbIC (natCode 2) d
      open DispatchIC (natCode 2) d
      w31 : NatNeqWitness 3 1
      w31 = decideNatNeq 3 1 (\ ())
      w32 : NatNeqWitness 3 2
      w32 = decideNatNeq 3 2 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 3 1 w31)
      to_inner1 : Deriv (eqF (ap1 stepBody_ic input_pkg) (ap1 inner1_ic input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 3 2 w32)
      to_inner2 : Deriv (eqF (ap1 inner1_ic input_pkg) (ap1 inner2_ic input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_fire : Deriv (eqF (ap1 test3 input_pkg) (ap1 s O))
      t3_fire = ruleTrans test3_val (natEq_eq 3)
      inner2_to_cell : Deriv (eqF (ap1 inner2_ic input_pkg) (ap1 icCellRO input_pkg))
      inner2_to_cell =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_fire)
            (ruleTrans (condFork_true_nc pairRO O) fst_pairRO))
      to_cell : Deriv (eqF (ap1 isCert (cRO d)) (ap1 icCellRO input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 (ruleTrans to_inner2 inner2_to_cell))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 isCert d))
      rec = np_lookup_gen get_rc d np_rc leq_b_P
  in ruleTrans to_cell rec

-- isCert(cAd d1 d2) = pi (isCert d1) (isCert d2) .
isCert_cAd : (d1 d2 : Term) ->
  Deriv (eqF (ap1 isCert (cAd d1 d2)) (ap2 pi (ap1 isCert d1) (ap1 isCert d2)))
isCert_cAd d1 d2 =
  let open NodePlumbIC (natCode 1) (ap2 pi d1 d2)
      open DispatchIC (natCode 1) (ap2 pi d1 d2)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      to_inner1 : Deriv (eqF (ap1 stepBody_ic input_pkg) (ap1 inner1_ic input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq 2)
      inner1_to_cell : Deriv (eqF (ap1 inner1_ic input_pkg) (ap1 icCellAd input_pkg))
      inner1_to_cell =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_fire)
            (ruleTrans (condFork_true_nc pairAd O) fst_pairAd))
      to_cell : Deriv (eqF (ap1 isCert (cAd d1 d2)) (ap1 icCellAd input_pkg))
      to_cell = ruleTrans np_unfold (ruleTrans to_inner1 inner1_to_cell)
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
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 isCert d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 isCert d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      icCellAd_value : Deriv (eqF (ap1 icCellAd input_pkg)
                                   (ap2 pi (ap1 isCert d1) (ap1 isCert d2)))
      icCellAd_value =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 isCert d1) rec2))
  in ruleTrans to_cell icCellAd_value

-- isCert(cRS d1 d2) = pi (isCert d1) (isCert d2) .
isCert_cRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 isCert (cRS d1 d2)) (ap2 pi (ap1 isCert d1) (ap1 isCert d2)))
isCert_cRS d1 d2 =
  let open NodePlumbIC (natCode 3) (ap2 pi d1 d2)
      open DispatchIC (natCode 3) (ap2 pi d1 d2)
      w41 : NatNeqWitness 4 1
      w41 = decideNatNeq 4 1 (\ ())
      w42 : NatNeqWitness 4 2
      w42 = decideNatNeq 4 2 (\ ())
      w43 : NatNeqWitness 4 3
      w43 = decideNatNeq 4 3 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 4 1 w41)
      to_inner1 : Deriv (eqF (ap1 stepBody_ic input_pkg) (ap1 inner1_ic input_pkg))
      to_inner1 =
        ruleTrans sb_eq
          (ruleTrans (congR condFork pairSu t1_O)
            (ruleTrans (condFork_false pairSu) snd_pairSu))
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 4 2 w42)
      to_inner2 : Deriv (eqF (ap1 inner1_ic input_pkg) (ap1 inner2_ic input_pkg))
      to_inner2 =
        ruleTrans inner1_eq
          (ruleTrans (congR condFork pairAd t2_O)
            (ruleTrans (condFork_false pairAd) snd_pairAd))
      t3_O : Deriv (eqF (ap1 test3 input_pkg) O)
      t3_O = ruleTrans test3_val (natEqF_at_neq 4 3 w43)
      to_inner3 : Deriv (eqF (ap1 inner2_ic input_pkg) (ap1 inner3_ic input_pkg))
      to_inner3 =
        ruleTrans inner2_eq
          (ruleTrans (congR condFork pairRO t3_O)
            (ruleTrans (condFork_false pairRO) snd_pairRO))
      t4_fire : Deriv (eqF (ap1 test4 input_pkg) (ap1 s O))
      t4_fire = ruleTrans test4_val (natEq_eq 4)
      inner3_to_cell : Deriv (eqF (ap1 inner3_ic input_pkg) (ap1 icCellRS input_pkg))
      inner3_to_cell =
        ruleTrans inner3_eq
          (ruleTrans (congR condFork pairRS t4_fire)
            (ruleTrans (condFork_true_nc pairRS O) fst_pairRS))
      to_cell : Deriv (eqF (ap1 isCert (cRS d1 d2)) (ap1 icCellRS input_pkg))
      to_cell = ruleTrans np_unfold
                  (ruleTrans to_inner1 (ruleTrans to_inner2 (ruleTrans to_inner3 inner3_to_cell)))
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
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 isCert d1))
      rec1 = np_lookup_gen lcIdx d1 lcIdx_eq leq_d1
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 isCert d2))
      rec2 = np_lookup_gen rcIdx d2 rcIdx_eq leq_d2
      icCellRS_value : Deriv (eqF (ap1 icCellRS input_pkg)
                                   (ap2 pi (ap1 isCert d1) (ap1 isCert d2)))
      icCellRS_value =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 isCert d1) rec2))
  in ruleTrans to_cell icCellRS_value
