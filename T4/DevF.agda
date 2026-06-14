{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DevF -- STAGE I3/I4 of attempt3 §11: the complete development  dev  as a
-- TRUE single-argument OBJECT function  devF : Fun1  over the TrsCodeObj term
-- codes (ze#/su#/ad#), built as a  T4.FoldRec.fold  course-of-values fold (the
-- same machinery that builds  src/tgt  in T4.ParEnds and  parsSrc/parsTgt in
-- T4.ParsObj), with the FIVE complete-development clauses proved as object
-- Deriv equations SCHEMATIC in the subterm codes:
--
--     dev_at_ze   :  devF ze#              = ze#
--     dev_at_su   :  devF (su# t)          = su# (devF t)
--     dev_at_adZe :  devF (ad# ze# y)      = devF y
--     dev_at_adSu :  devF (ad# (su# x) y)  = su# (ad# (devF x) (devF y))
--     dev_at_adAd :  devF (ad# (ad# p q) y) = ad# (devF (ad# p q)) (devF y)
--
-- This is the object  devF  attempt3 §11 (c)/(I3) calls for: a Fun1 usable at
-- SYMBOLIC codes, so the triangle (I4) can be an object course-of-values
-- ruleIndNat whose 5 cases are exactly these equations (IH at smaller codes).
--
-- ★ KEY (no grandchild lookup).  dev (ad (su x) y) = su (ad (dev x) (dev y))
-- needs  dev x  where  x  is a GRAND-child of the ad node.  But the FIRST child
-- here is  a = su# x , and  dev a = dev (su x) = su# (dev x) , so
--   dev x = Snd (dev a) .
-- Hence EVERY cell looks up only DIRECT children (a , y), never grandchildren:
-- the  adSu  cell reads  dev a  (lookup at the left child) and projects  Snd .
-- The  adSu  EQUATION then chains  dev_at_su  to expose  Snd (su# (dev x)) = dev x.
--
-- Dispatch.  Outer 2-way on the node head tag (su#=1 -> suD cell ; else ad
-- node).  The ad cell is an inner 3-way cascade on the FIRST CHILD's head tag
-- (ze#=0 -> dev y ; su#=1 -> su#(ad#(Snd(dev a))(dev y)) ; else (ad#) ->
-- ad#(dev a)(dev y)).  Mirrors T4.ParEnds lemma-for-lemma; no holes/postulates.

module T4.DevF where

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
  ( ze# ; su# ; ad# ; tagZe ; tagSu ; tagAd
  ; hd ; hd_ze ; hd_su ; hd_ad ; ar_su )

open import BRA3.Church        using ( pi ; sigma ; tau ; hPi ; T90 ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra   using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.Dispatch      using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Cantor-zero collapse  pi O O = O  (so ze# = pi O O is the base).

pi_O_O : Deriv (eqF (ap2 pi O O) O)
pi_O_O = ruleTrans (ax_R_base tau sigma hPi O) T90

------------------------------------------------------------------------
-- SECTION 1.  Child accessors and cells.

-- The payload of an  ad#  node is  pi a y ;  a = Fst (get_rc), y = Snd (get_rc).
lcIdx : Fun1
lcIdx = compose1U Fst get_rc
rcIdx : Fun1
rcIdx = compose1U Snd get_rc

-- Head tag of the FIRST child a  =  Fst a  =  Fst (lcIdx ..).
firstHead : Fun1
firstHead = compose1U Fst lcIdx

-- ze# as a constant Fun1:  C pi Z Z  applied to anything = pi O O = ze#.
ze#F : Fun1
ze#F = C pi Z Z

-- su# X = pi (natCode 1) X ;  ad# A B = pi (natCode 2) (pi A B).
cellSuD : Fun1                          -- su# (devF child)        , child = get_rc
cellSuD = C pi (constN 1) (lookupAt get_rc)

cellAdZe : Fun1                         -- devF y                  , y = right child
cellAdZe = lookupAt rcIdx

cellAdSu : Fun1                         -- su# (ad# (Snd (devF a)) (devF y))
cellAdSu = C pi (constN 1) (C pi (constN 2)
             (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)))

cellAdAd : Fun1                         -- ad# (devF a) (devF y)
cellAdAd = C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx))

------------------------------------------------------------------------
-- SECTION 2.  The dispatch cascade.
--   outer:  node tag = 1 (su#)  ->  cellSuD ;  else  cellAdD .
--   ad cell (cellAdD): first-child tag = 0 (ze#)  ->  cellAdZe ;
--                      first-child tag = 1 (su#)  ->  cellAdSu ;  else cellAdAd .

testTagSu : Fun1                        -- node head tag = 1 ?
testTagSu = C natEqF get_tag (constN 1)

testF0 : Fun1                           -- first-child head tag = 0 ?
testF0 = C natEqF firstHead (constN 0)
testF1 : Fun1                           -- first-child head tag = 1 ?
testF1 = C natEqF firstHead (constN 1)

innerAd2 : Fun1                         -- a-tag1 -> cellAdSu ; else cellAdAd
innerAd2 = C condFork (C pi cellAdSu cellAdAd) testF1

cellAdD : Fun1                          -- a-tag0 -> cellAdZe ; else innerAd2
cellAdD = C condFork (C pi cellAdZe innerAd2) testF0

stepBody_dev : Fun1                     -- node-tag1 -> cellSuD ; else cellAdD
stepBody_dev = C condFork (C pi cellSuD cellAdD) testTagSu

stepFun_dev : Fun2
stepFun_dev = Post stepBody_dev pi

devBase : Fun1                          -- O |-> ze# = pi O O
devBase = C pi Z Z

devF : Fun1
devF = fold devBase stepFun_dev

------------------------------------------------------------------------
-- SECTION 3.  Base case:  devF ze# = ze# .

devBaseAtO : Deriv (eqF (ap1 devBase O) ze#)
devBaseAtO =
  ruleTrans (ax_C pi Z Z O)
    (ruleTrans (congL pi (ap1 Z O) (axZ O))
               (congR pi O (axZ O)))

dev_at_ze : Deriv (eqF (ap1 devF ze#) ze#)
dev_at_ze =
  ruleTrans (cong1 devF pi_O_O)
    (ruleTrans (fold_at_O devBase stepFun_dev) devBaseAtO)

ze#F_value : (e : Term) -> Deriv (eqF (ap1 ze#F e) ze#)
ze#F_value e =
  ruleTrans (ax_C pi Z Z e)
    (ruleTrans (congL pi (ap1 Z e) (axZ e)) (congR pi O (axZ e)))

------------------------------------------------------------------------
-- SECTION 4.  Shared node plumbing (generic in A, b ; mirrors T4.ParEnds).

module NP (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec devBase stepFun_dev) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  np_unfold : Deriv (eqF (ap1 devF node) (ap1 stepBody_dev input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold devBase stepFun_dev A b)
              (axPost stepBody_dev pi P_outer (ap1 Snd prev))

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
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 devF ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt devBase stepFun_dev O P_outer))
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
                              (ap2 (iter Snd) (HistP_sbt devBase stepFun_dev O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt devBase stepFun_dev O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt devBase stepFun_dev O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_dev : Deriv (eqF (HPsbt devBase stepFun_dev O ct P_outer) (ap1 devF ct))
        HP_to_dev = lookup_eq_fold devBase stepFun_dev ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_dev

  -- Outer dispatch:  stepBody_dev input = condFork (pi cellSuD cellAdD input)(testTagSu input).
  pairOuter : Term
  pairOuter = ap1 (C pi cellSuD cellAdD) input_pkg

  fst_pairOuter : Deriv (eqF (ap1 Fst pairOuter) (ap1 cellSuD input_pkg))
  fst_pairOuter = ruleTrans (cong1 Fst (ax_C pi cellSuD cellAdD input_pkg))
                            (axFst (ap1 cellSuD input_pkg) (ap1 cellAdD input_pkg))
  snd_pairOuter : Deriv (eqF (ap1 Snd pairOuter) (ap1 cellAdD input_pkg))
  snd_pairOuter = ruleTrans (cong1 Snd (ax_C pi cellSuD cellAdD input_pkg))
                            (axSnd (ap1 cellSuD input_pkg) (ap1 cellAdD input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody_dev input_pkg)
                     (ap2 condFork pairOuter (ap1 testTagSu input_pkg)))
  sb_eq = ax_C condFork (C pi cellSuD cellAdD) testTagSu input_pkg

  testTagSu_val : Deriv (eqF (ap1 testTagSu input_pkg) (ap2 natEqF (ap1 s A) (natCode 1)))
  testTagSu_val =
    ruleTrans (ax_C natEqF get_tag (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 1 input_pkg)))

------------------------------------------------------------------------
-- SECTION 5.  su# closure:  devF (su# t) = su# (devF t) .
--   node = pi (s O) t , A = O ; node tag = s O = natCode 1 -> testTagSu fires.

dev_at_su : (t : Term) -> Deriv (eqF (ap1 devF (su# t)) (su# (ap1 devF t)))
dev_at_su t =
  let open NP O t
      t1_fire : Deriv (eqF (ap1 testTagSu input_pkg) (ap1 s O))
      t1_fire = ruleTrans testTagSu_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 devF (su# t)) (ap1 cellSuD input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairOuter t1_fire)
              (ruleTrans (condFork_true_nc pairOuter O) fst_pairOuter)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 devF t))
      rec = np_lookup_gen get_rc t np_rc leq_b_P
      cellSuD_value : Deriv (eqF (ap1 cellSuD input_pkg) (su# (ap1 devF t)))
      cellSuD_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec))
  in ruleTrans to_cell cellSuD_value

------------------------------------------------------------------------
-- SECTION 6.  ad# dispatch helpers (the node is an ad# node:
--   A = natCode 1 , b = pi a y ,  testTagSu SKIPS).  Shared by the three
--   ad-cases; parameterised by the first-child code  a  and right child  y .

module AdNode (a y : Term) where
  open NP (natCode 1) (ap2 pi a y) public

  -- testTagSu skips (node tag = natCode 2).
  w_node : NatNeqWitness 2 1
  w_node = decideNatNeq 2 1 (\ ())
  testTagSu_O : Deriv (eqF (ap1 testTagSu input_pkg) O)
  testTagSu_O = ruleTrans testTagSu_val (natEqF_at_neq 2 1 w_node)

  to_adCell : Deriv (eqF (ap1 devF (ad# a y)) (ap1 cellAdD input_pkg))
  to_adCell =
    ruleTrans np_unfold
      (ruleTrans sb_eq
        (ruleTrans (congR condFork pairOuter testTagSu_O)
          (ruleTrans (condFork_false pairOuter) snd_pairOuter)))

  -- left / right child positions.
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

  rec_a : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 devF a))
  rec_a = np_lookup_gen lcIdx a lcIdx_eq leq_a
  rec_y : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 devF y))
  rec_y = np_lookup_gen rcIdx y rcIdx_eq leq_y

  -- first-child head value:  firstHead input = Fst a .
  firstHead_eq : Deriv (eqF (ap1 firstHead input_pkg) (ap1 Fst a))
  firstHead_eq = ruleTrans (compose1U_eq Fst lcIdx input_pkg) (cong1 Fst lcIdx_eq)

  -- inner-cascade dispatch pairs.
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

  cellAdD_eq : Deriv (eqF (ap1 cellAdD input_pkg)
                          (ap2 condFork pairInner0 (ap1 testF0 input_pkg)))
  cellAdD_eq = ax_C condFork (C pi cellAdZe innerAd2) testF0 input_pkg

  innerAd2_eq : Deriv (eqF (ap1 innerAd2 input_pkg)
                           (ap2 condFork pairInner1 (ap1 testF1 input_pkg)))
  innerAd2_eq = ax_C condFork (C pi cellAdSu cellAdAd) testF1 input_pkg

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
-- SECTION 7.  ad/ze closure:  devF (ad# ze# y) = devF y .
--   first child a = ze# , head = tagZe = natCode 0 -> testF0 fires -> cellAdZe.

dev_at_adZe : (y : Term) -> Deriv (eqF (ap1 devF (ad# ze# y)) (ap1 devF y))
dev_at_adZe y =
  let open AdNode ze# y
      tF0_fire : Deriv (eqF (ap1 testF0 input_pkg) (ap1 s O))
      tF0_fire = ruleTrans (testF0_at 0 hd_ze) (natEq_eq 0)
      adCell_to_cell : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 cellAdZe input_pkg))
      adCell_to_cell =
        ruleTrans cellAdD_eq
          (ruleTrans (congR condFork pairInner0 tF0_fire)
            (ruleTrans (condFork_true_nc pairInner0 O) fst_pairInner0))
      -- cellAdZe input = lookupAt rcIdx input = devF y .
  in ruleTrans to_adCell (ruleTrans adCell_to_cell rec_y)

------------------------------------------------------------------------
-- SECTION 8.  ad/su closure:  devF (ad# (su# x) y) = su# (ad# (devF x) (devF y)) .
--   first child a = su# x , head = tagSu = natCode 1 -> testF0 skip, testF1 fire
--   -> cellAdSu = su#(ad#(Snd(devF a))(devF y)) , and  Snd(devF(su# x)) = devF x
--   via dev_at_su + ar_su.

dev_at_adSu : (x y : Term) ->
  Deriv (eqF (ap1 devF (ad# (su# x) y)) (su# (ad# (ap1 devF x) (ap1 devF y))))
dev_at_adSu x y =
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
      inner_to_cell : Deriv (eqF (ap1 innerAd2 input_pkg) (ap1 cellAdSu input_pkg))
      inner_to_cell =
        ruleTrans innerAd2_eq
          (ruleTrans (congR condFork pairInner1 tF1_fire)
            (ruleTrans (condFork_true_nc pairInner1 O) fst_pairInner1))
      to_cell : Deriv (eqF (ap1 devF (ad# (su# x) y)) (ap1 cellAdSu input_pkg))
      to_cell = ruleTrans to_adCell (ruleTrans adCell_to_inner inner_to_cell)
      -- Snd (devF a) = Snd (su# (devF x)) = devF x .
      devx_eq : Deriv (eqF (ap1 Snd (ap1 (lookupAt lcIdx) input_pkg)) (ap1 devF x))
      devx_eq =
        ruleTrans (cong1 Snd rec_a)
          (ruleTrans (cong1 Snd (dev_at_su x)) (ar_su (ap1 devF x)))
      -- cellAdSu input = su# (ad# (Snd(devF a)) (devF y)) -> su#(ad#(devF x)(devF y)).
      inner_ad : Deriv (eqF (ap1 (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                            (ap2 pi (ap1 devF x) (ap1 devF y)))
      inner_ad =
        ruleTrans (ax_C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg)
                        (ruleTrans (compose1U_eq Snd (lookupAt lcIdx) input_pkg) devx_eq))
                     (congR pi (ap1 devF x) rec_y))
      ad_wrap : Deriv (eqF (ap1 (C pi (constN 2)
                              (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx))) input_pkg)
                           (ad# (ap1 devF x) (ap1 devF y)))
      ad_wrap =
        ruleTrans (ax_C pi (constN 2)
                     (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_ad))
      cellAdSu_value : Deriv (eqF (ap1 cellAdSu input_pkg)
                                  (su# (ad# (ap1 devF x) (ap1 devF y))))
      cellAdSu_value =
        ruleTrans (ax_C pi (constN 1)
                     (C pi (constN 2) (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx)))
                     input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 2)
                                   (C pi (compose1U Snd (lookupAt lcIdx)) (lookupAt rcIdx))) input_pkg)
                               (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) ad_wrap))
  in ruleTrans to_cell cellAdSu_value

------------------------------------------------------------------------
-- SECTION 9.  ad/ad closure:  devF (ad# (ad# p q) y) = ad# (devF (ad# p q)) (devF y) .
--   first child a = ad# p q , head = tagAd = natCode 2 -> testF0 skip, testF1 skip
--   -> cellAdAd = ad#(devF a)(devF y) .

dev_at_adAd : (p q y : Term) ->
  Deriv (eqF (ap1 devF (ad# (ad# p q) y)) (ad# (ap1 devF (ad# p q)) (ap1 devF y)))
dev_at_adAd p q y =
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
      inner_to_cell : Deriv (eqF (ap1 innerAd2 input_pkg) (ap1 cellAdAd input_pkg))
      inner_to_cell =
        ruleTrans innerAd2_eq
          (ruleTrans (congR condFork pairInner1 tF1_O)
            (ruleTrans (condFork_false pairInner1) snd_pairInner1))
      to_cell : Deriv (eqF (ap1 devF (ad# (ad# p q) y)) (ap1 cellAdAd input_pkg))
      to_cell = ruleTrans to_adCell (ruleTrans adCell_to_inner inner_to_cell)
      inner_ad : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                            (ap2 pi (ap1 devF (ad# p q)) (ap1 devF y)))
      inner_ad =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec_a)
                     (congR pi (ap1 devF (ad# p q)) rec_y))
      cellAdAd_value : Deriv (eqF (ap1 cellAdAd input_pkg)
                                  (ad# (ap1 devF (ad# p q)) (ap1 devF y)))
      cellAdAd_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_ad))
  in ruleTrans to_cell cellAdAd_value
