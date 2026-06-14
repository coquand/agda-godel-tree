{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevCertF -- the DEVELOPMENT-CERTIFICATE builder  devCertF : Fun1 , the
-- object function that maps a term code to the code of the parallel-reduction
-- CERTIFICATE (T4.ParCert cZe/cSu/cAd/cRO/cRS) witnessing the complete-
-- development step  t => dev t .  This is the witness side of the object
-- triangle (attempt3 §11 I4): the diagonal  Par (code t) (devF (code t))  is
-- introduced (T4.ParIntro.parIntro) at the certificate  devCertF (code t) ,
-- once its endpoint/validity equations  src/tgt/isCert  are proved by object
-- course-of-values ruleIndNat (the NEXT file).
--
-- Same FoldRec.fold + dispatch SKELETON as T4.DevF (so the per-case structure
-- matches devF clause-for-clause), but each cell emits the matching CERT node:
--     devCert ze#              = cZe
--     devCert (su# t)          = cSu (devCert t)
--     devCert (ad# ze# y)      = cRO (devCert y)
--     devCert (ad# (su# x) y)  = cRS (devCert x) (devCert y)
--     devCert (ad# (ad# p q) y) = cAd (devCert (ad# p q)) (devCert y)
-- These mirror the Par-derivation shapes pZe/pSu/pRO/pRS/pAd of the complete
-- development (T4.ChurchRosserProto / T4.ParTri.tri at the reflexive step).
--
-- ★ Same no-grandchild trick as DevF.  cRS needs  devCert x  (x a grandchild),
-- but  devCert (su# x) = cSu (devCert x) , so  devCert x = Snd (devCert (su# x))
-- from the DIRECT-child lookup; the adSu equation chains  devCert_at_su +
-- cSu_sub.  No holes, no postulates.

module T4.DevCertF where

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
  ( ze# ; su# ; ad# ; hd_ze ; hd_su ; hd_ad )
open import T4.ParCert using
  ( cZe ; cSu ; cAd ; cRO ; cRS ; cSu_sub )

open import BRA3.Church        using ( pi ; sigma ; tau ; hPi ; T90 ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra   using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.Dispatch      using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Cantor-zero collapse  pi O O = O  (so cZe = pi O O is the base).

pi_O_O : Deriv (eqF (ap2 pi O O) O)
pi_O_O = ruleTrans (ax_R_base tau sigma hPi O) T90

------------------------------------------------------------------------
-- SECTION 1.  Child accessors and cert cells.

lcIdx : Fun1
lcIdx = compose1U Fst get_rc
rcIdx : Fun1
rcIdx = compose1U Snd get_rc
firstHead : Fun1
firstHead = compose1U Fst lcIdx

-- cSu d = pi (natCode 1) d ; cAd d1 d2 = pi (natCode 2)(pi d1 d2) ;
-- cRO d = pi (natCode 3) d ; cRS d1 d2 = pi (natCode 4)(pi d1 d2).
cellSu : Fun1                           -- cSu (devCert child)     , child = get_rc
cellSu = C pi (constN 1) (lookupAt get_rc)

cellRO : Fun1                           -- cRO (devCert y)         , y = right child
cellRO = C pi (constN 3) (lookupAt rcIdx)

cellRS : Fun1                           -- cRS (Snd (devCert a)) (devCert y)
cellRS = C pi (constN 4)
           (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx))

cellAd : Fun1                           -- cAd (devCert a) (devCert y)
cellAd = C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))

------------------------------------------------------------------------
-- SECTION 2.  Dispatch cascade (same shape as DevF).

testTagSu : Fun1                        -- node head tag = 1 (su#) ?
testTagSu = C natEqF get_tag (constN 1)

testF0 : Fun1                           -- first-child head tag = 0 (ze#) ?
testF0 = C natEqF firstHead (constN 0)
testF1 : Fun1                           -- first-child head tag = 1 (su#) ?
testF1 = C natEqF firstHead (constN 1)

innerAd2 : Fun1                         -- a-tag1 -> cellRS ; else cellAd
innerAd2 = C condFork (C pi cellRS cellAd) testF1

cellAdD : Fun1                          -- a-tag0 -> cellRO ; else innerAd2
cellAdD = C condFork (C pi cellRO innerAd2) testF0

stepBody_dc : Fun1                      -- node-tag1 -> cellSu ; else cellAdD
stepBody_dc = C condFork (C pi cellSu cellAdD) testTagSu

stepFun_dc : Fun2
stepFun_dc = Post stepBody_dc pi

devCertBase : Fun1                      -- O |-> cZe = pi O O
devCertBase = C pi Z Z

devCertF : Fun1
devCertF = fold devCertBase stepFun_dc

------------------------------------------------------------------------
-- SECTION 3.  Base case:  devCertF ze# = cZe .

devCertBaseAtO : Deriv (eqF (ap1 devCertBase O) cZe)
devCertBaseAtO =
  ruleTrans (ax_C pi Z Z O)
    (ruleTrans (congL pi (ap1 Z O) (axZ O))
               (congR pi O (axZ O)))

devCert_at_ze : Deriv (eqF (ap1 devCertF ze#) cZe)
devCert_at_ze =
  ruleTrans (cong1 devCertF pi_O_O)
    (ruleTrans (fold_at_O devCertBase stepFun_dc) devCertBaseAtO)

------------------------------------------------------------------------
-- SECTION 4.  Shared node plumbing (generic in A, b ; mirrors T4.DevF.NP).

module NP (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec devCertBase stepFun_dc) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  np_unfold : Deriv (eqF (ap1 devCertF node) (ap1 stepBody_dc input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold devCertBase stepFun_dc A b)
              (axPost stepBody_dc pi P_outer (ap1 Snd prev))

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
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 devCertF ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt devCertBase stepFun_dc O P_outer))
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
                              (ap2 (iter Snd) (HistP_sbt devCertBase stepFun_dc O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt devCertBase stepFun_dc O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt devCertBase stepFun_dc O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_dc : Deriv (eqF (HPsbt devCertBase stepFun_dc O ct P_outer) (ap1 devCertF ct))
        HP_to_dc = lookup_eq_fold devCertBase stepFun_dc ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_dc

  pairOuter : Term
  pairOuter = ap1 (C pi cellSu cellAdD) input_pkg

  fst_pairOuter : Deriv (eqF (ap1 Fst pairOuter) (ap1 cellSu input_pkg))
  fst_pairOuter = ruleTrans (cong1 Fst (ax_C pi cellSu cellAdD input_pkg))
                            (axFst (ap1 cellSu input_pkg) (ap1 cellAdD input_pkg))
  snd_pairOuter : Deriv (eqF (ap1 Snd pairOuter) (ap1 cellAdD input_pkg))
  snd_pairOuter = ruleTrans (cong1 Snd (ax_C pi cellSu cellAdD input_pkg))
                            (axSnd (ap1 cellSu input_pkg) (ap1 cellAdD input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody_dc input_pkg)
                     (ap2 condFork pairOuter (ap1 testTagSu input_pkg)))
  sb_eq = ax_C condFork (C pi cellSu cellAdD) testTagSu input_pkg

  testTagSu_val : Deriv (eqF (ap1 testTagSu input_pkg) (ap2 natEqF (ap1 s A) (natCode 1)))
  testTagSu_val =
    ruleTrans (ax_C natEqF get_tag (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 1 input_pkg)))

------------------------------------------------------------------------
-- SECTION 5.  su# closure:  devCertF (su# t) = cSu (devCertF t) .

devCert_at_su : (t : Term) -> Deriv (eqF (ap1 devCertF (su# t)) (cSu (ap1 devCertF t)))
devCert_at_su t =
  let open NP O t
      t1_fire : Deriv (eqF (ap1 testTagSu input_pkg) (ap1 s O))
      t1_fire = ruleTrans testTagSu_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 devCertF (su# t)) (ap1 cellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairOuter t1_fire)
              (ruleTrans (condFork_true_nc pairOuter O) fst_pairOuter)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 devCertF t))
      rec = np_lookup_gen get_rc t np_rc leq_b_P
      cellSu_value : Deriv (eqF (ap1 cellSu input_pkg) (cSu (ap1 devCertF t)))
      cellSu_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec))
  in ruleTrans to_cell cellSu_value

------------------------------------------------------------------------
-- SECTION 6.  ad# dispatch helpers (node = ad# a y , A = natCode 1 , b = pi a y).

module AdNode (a y : Term) where
  open NP (natCode 1) (ap2 pi a y) public

  w_node : NatNeqWitness 2 1
  w_node = decideNatNeq 2 1 (\ ())
  testTagSu_O : Deriv (eqF (ap1 testTagSu input_pkg) O)
  testTagSu_O = ruleTrans testTagSu_val (natEqF_at_neq 2 1 w_node)

  to_adCell : Deriv (eqF (ap1 devCertF (ad# a y)) (ap1 cellAdD input_pkg))
  to_adCell =
    ruleTrans np_unfold
      (ruleTrans sb_eq
        (ruleTrans (congR condFork pairOuter testTagSu_O)
          (ruleTrans (condFork_false pairOuter) snd_pairOuter)))

  lcIdx_eq : Deriv (eqF (ap1 lcIdx input_pkg) a)
  lcIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                       (ruleTrans (cong1 Fst np_rc) (axFst a y))
  rcIdx_eq : Deriv (eqF (ap1 rcIdx input_pkg) y)
  rcIdx_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                       (ruleTrans (cong1 Snd np_rc) (axSnd a y))
  leq_a : Deriv (leq a P_outer)
  leq_a = leq_trans a (ap2 pi a y) P_outer (leq_pi_left a y) leq_b_P
  leq_y : Deriv (leq y P_outer)
  leq_y = leq_trans y (ap2 pi a y) P_outer (leq_pi_right a y) leq_b_P

  rec_a : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 devCertF a))
  rec_a = np_lookup_gen lcIdx a lcIdx_eq leq_a
  rec_y : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 devCertF y))
  rec_y = np_lookup_gen rcIdx y rcIdx_eq leq_y

  firstHead_eq : Deriv (eqF (ap1 firstHead input_pkg) (ap1 Fst a))
  firstHead_eq = ruleTrans (compose1U_eq Fst lcIdx input_pkg) (cong1 Fst lcIdx_eq)

  pairInner0 : Term
  pairInner0 = ap1 (C pi cellRO innerAd2) input_pkg
  pairInner1 : Term
  pairInner1 = ap1 (C pi cellRS cellAd) input_pkg

  fst_pairInner0 : Deriv (eqF (ap1 Fst pairInner0) (ap1 cellRO input_pkg))
  fst_pairInner0 = ruleTrans (cong1 Fst (ax_C pi cellRO innerAd2 input_pkg))
                             (axFst (ap1 cellRO input_pkg) (ap1 innerAd2 input_pkg))
  snd_pairInner0 : Deriv (eqF (ap1 Snd pairInner0) (ap1 innerAd2 input_pkg))
  snd_pairInner0 = ruleTrans (cong1 Snd (ax_C pi cellRO innerAd2 input_pkg))
                             (axSnd (ap1 cellRO input_pkg) (ap1 innerAd2 input_pkg))
  fst_pairInner1 : Deriv (eqF (ap1 Fst pairInner1) (ap1 cellRS input_pkg))
  fst_pairInner1 = ruleTrans (cong1 Fst (ax_C pi cellRS cellAd input_pkg))
                             (axFst (ap1 cellRS input_pkg) (ap1 cellAd input_pkg))
  snd_pairInner1 : Deriv (eqF (ap1 Snd pairInner1) (ap1 cellAd input_pkg))
  snd_pairInner1 = ruleTrans (cong1 Snd (ax_C pi cellRS cellAd input_pkg))
                             (axSnd (ap1 cellRS input_pkg) (ap1 cellAd input_pkg))

  cellAdD_eq : Deriv (eqF (ap1 cellAdD input_pkg)
                          (ap2 condFork pairInner0 (ap1 testF0 input_pkg)))
  cellAdD_eq = ax_C condFork (C pi cellRO innerAd2) testF0 input_pkg

  innerAd2_eq : Deriv (eqF (ap1 innerAd2 input_pkg)
                           (ap2 condFork pairInner1 (ap1 testF1 input_pkg)))
  innerAd2_eq = ax_C condFork (C pi cellRS cellAd) testF1 input_pkg

  testF0_at : (tg : Nat) -> Deriv (eqF (ap1 Fst a) (natCode tg)) ->
              Deriv (eqF (ap1 testF0 input_pkg) (ap2 natEqF (natCode tg) (natCode 0)))
  testF0_at tg hd_a =
    ruleTrans (ax_C natEqF firstHead (constN 0) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 0) input_pkg) (ruleTrans firstHead_eq hd_a))
                 (congR natEqF (natCode tg) (constN_eq 0 input_pkg)))
  testF1_at : (tg : Nat) -> Deriv (eqF (ap1 Fst a) (natCode tg)) ->
              Deriv (eqF (ap1 testF1 input_pkg) (ap2 natEqF (natCode tg) (natCode 1)))
  testF1_at tg hd_a =
    ruleTrans (ax_C natEqF firstHead (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) (ruleTrans firstHead_eq hd_a))
                 (congR natEqF (natCode tg) (constN_eq 1 input_pkg)))

------------------------------------------------------------------------
-- SECTION 7.  ad/ze closure:  devCertF (ad# ze# y) = cRO (devCertF y) .

devCert_at_adZe : (y : Term) -> Deriv (eqF (ap1 devCertF (ad# ze# y)) (cRO (ap1 devCertF y)))
devCert_at_adZe y =
  let open AdNode ze# y
      tF0_fire : Deriv (eqF (ap1 testF0 input_pkg) (ap1 s O))
      tF0_fire = ruleTrans (testF0_at 0 hd_ze) (natEq_eq 0)
      adCell_to_cell : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 cellRO input_pkg))
      adCell_to_cell =
        ruleTrans cellAdD_eq
          (ruleTrans (congR condFork pairInner0 tF0_fire)
            (ruleTrans (condFork_true_nc pairInner0 O) fst_pairInner0))
      cellRO_value : Deriv (eqF (ap1 cellRO input_pkg) (cRO (ap1 devCertF y)))
      cellRO_value =
        ruleTrans (ax_C pi (constN 3) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) (constN_eq 3 input_pkg))
                     (congR pi (natCode 3) rec_y))
  in ruleTrans to_adCell (ruleTrans adCell_to_cell cellRO_value)

------------------------------------------------------------------------
-- SECTION 8.  ad/su closure:
--   devCertF (ad# (su# x) y) = cRS (devCertF x) (devCertF y) .

devCert_at_adSu : (x y : Term) ->
  Deriv (eqF (ap1 devCertF (ad# (su# x) y)) (cRS (ap1 devCertF x) (ap1 devCertF y)))
devCert_at_adSu x y =
  let open AdNode (su# x) y
      w10 : NatNeqWitness 1 0
      w10 = decideNatNeq 1 0 (\ ())
      tF0_O : Deriv (eqF (ap1 testF0 input_pkg) O)
      tF0_O = ruleTrans (testF0_at 1 (hd_su x)) (natEqF_at_neq 1 0 w10)
      tF1_fire : Deriv (eqF (ap1 testF1 input_pkg) (ap1 s O))
      tF1_fire = ruleTrans (testF1_at 1 (hd_su x)) (natEq_eq 1)
      adCell_to_inner : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 innerAd2 input_pkg))
      adCell_to_inner =
        ruleTrans cellAdD_eq
          (ruleTrans (congR condFork pairInner0 tF0_O)
            (ruleTrans (condFork_false pairInner0) snd_pairInner0))
      inner_to_cell : Deriv (eqF (ap1 innerAd2 input_pkg) (ap1 cellRS input_pkg))
      inner_to_cell =
        ruleTrans innerAd2_eq
          (ruleTrans (congR condFork pairInner1 tF1_fire)
            (ruleTrans (condFork_true_nc pairInner1 O) fst_pairInner1))
      to_cell : Deriv (eqF (ap1 devCertF (ad# (su# x) y)) (ap1 cellRS input_pkg))
      to_cell = ruleTrans to_adCell (ruleTrans adCell_to_inner inner_to_cell)
      -- Snd (devCertF (su# x)) = Snd (cSu (devCertF x)) = devCertF x .
      devx_eq : Deriv (eqF (ap1 Snd (ap1 (lookupAt lcIdx) input_pkg)) (ap1 devCertF x))
      devx_eq =
        ruleTrans (cong1 Snd rec_a)
          (ruleTrans (cong1 Snd (devCert_at_su x)) (cSu_sub (ap1 devCertF x)))
      inner_pair : Deriv (eqF (ap1 (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                              (ap2 pi (ap1 devCertF x) (ap1 devCertF y)))
      inner_pair =
        ruleTrans (ax_C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg)
                        (ruleTrans (compose1U_eq Snd (lookupAt lcIdx) input_pkg) devx_eq))
                     (congR pi (ap1 devCertF x) rec_y))
      cellRS_value : Deriv (eqF (ap1 cellRS input_pkg)
                                (cRS (ap1 devCertF x) (ap1 devCertF y)))
      cellRS_value =
        ruleTrans (ax_C pi (constN 4)
                     (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 4 input_pkg))
                     (congR pi (natCode 4) inner_pair))
  in ruleTrans to_cell cellRS_value

------------------------------------------------------------------------
-- SECTION 9.  ad/ad closure:
--   devCertF (ad# (ad# p q) y) = cAd (devCertF (ad# p q)) (devCertF y) .

devCert_at_adAd : (p q y : Term) ->
  Deriv (eqF (ap1 devCertF (ad# (ad# p q) y))
             (cAd (ap1 devCertF (ad# p q)) (ap1 devCertF y)))
devCert_at_adAd p q y =
  let open AdNode (ad# p q) y
      w20 : NatNeqWitness 2 0
      w20 = decideNatNeq 2 0 (\ ())
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      tF0_O : Deriv (eqF (ap1 testF0 input_pkg) O)
      tF0_O = ruleTrans (testF0_at 2 (hd_ad p q)) (natEqF_at_neq 2 0 w20)
      tF1_O : Deriv (eqF (ap1 testF1 input_pkg) O)
      tF1_O = ruleTrans (testF1_at 2 (hd_ad p q)) (natEqF_at_neq 2 1 w21)
      adCell_to_inner : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 innerAd2 input_pkg))
      adCell_to_inner =
        ruleTrans cellAdD_eq
          (ruleTrans (congR condFork pairInner0 tF0_O)
            (ruleTrans (condFork_false pairInner0) snd_pairInner0))
      inner_to_cell : Deriv (eqF (ap1 innerAd2 input_pkg) (ap1 cellAd input_pkg))
      inner_to_cell =
        ruleTrans innerAd2_eq
          (ruleTrans (congR condFork pairInner1 tF1_O)
            (ruleTrans (condFork_false pairInner1) snd_pairInner1))
      to_cell : Deriv (eqF (ap1 devCertF (ad# (ad# p q) y)) (ap1 cellAd input_pkg))
      to_cell = ruleTrans to_adCell (ruleTrans adCell_to_inner inner_to_cell)
      inner_pair : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                              (ap2 pi (ap1 devCertF (ad# p q)) (ap1 devCertF y)))
      inner_pair =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec_a)
                     (congR pi (ap1 devCertF (ad# p q)) rec_y))
      cellAd_value : Deriv (eqF (ap1 cellAd input_pkg)
                                (cAd (ap1 devCertF (ad# p q)) (ap1 devCertF y)))
      cellAd_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_pair))
  in ruleTrans to_cell cellAd_value
