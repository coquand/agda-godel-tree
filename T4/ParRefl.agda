{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParRefl -- STAGE 4b (first lemma) of HANDOFF-guard-t0-cr.md: the
-- reflexivity certificate builder  reflCert : Fun1  for the relational
-- internal Church-Rosser route, the object analog of
--     parRefl : (t : Tm) -> Par t t           (T4.ChurchRosserProto)
--
-- reflCert reads a TrsCodeObj term code (ze#/su#/ad#, tags 0/1/2) and
-- builds the diagonal Par-certificate (T4.ParCert) whose source and target
-- are both that term:
--     reflCert(ze#)     = cZe
--     reflCert(su# t)   = cSu (reflCert t)
--     reflCert(ad# a b) = cAd (reflCert a) (reflCert b)
-- It is a structural fold over the term code (T4.FoldRec.fold), with a
-- 2-way  natEqF  cascade on the term tag (1 = su#, else 2 = ad#); the base
-- (tag 0 = ze#, the Cantor zero) returns cZe.
--
-- NB.  ze# and cZe are the SAME object term (both  Pair O O = pi O O ), so
-- the fold's base case  srcBase O = ze#  IS  reflCert ze# = cZe .  The
-- su#/ad# CELLS are literally  T4.ParEnds.cellSu / cellAd  (both wrap with
-- the cSu/cAd tags 1/2 around the recursive  lookupAt  calls), so we reuse
-- them; only the dispatch (2-way here) and the fold differ.
--
-- THIS FILE: reflCert + its three DEFINING equations as Deriv.  The
-- endpoint/validity PRESERVATION (src(reflCert t) = t , tgt(reflCert t) = t,
-- isCert(reflCert t) = O , i.e. parRefl proper) is a course-of-values
-- induction on the term code (ruleIndNat over the cov_spec stability
-- foundation) and is the next step.

module T4.ParRefl where

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

open import T4.ParEnds using
  ( srcBase ; srcBaseAtO ; cellSu ; cellAd ; test1 ; lcIdx ; rcIdx ; pi_O_O )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )
open import T4.ParCert    using ( cZe ; cSu ; cAd )

open import BRA3.Church        using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import BRA3.PairAlgebra   using ( Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.Dispatch      using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- The fold:  2-way cascade (tag 1 = su# -> cellSu ; else tag 2 = ad# ->
-- cellAd).  Base = srcBase (O -> ze# = cZe).

stepBody_rc : Fun1
stepBody_rc = C condFork (C pi cellSu cellAd) test1

stepFun_rc : Fun2
stepFun_rc = Post stepBody_rc pi

reflCert : Fun1
reflCert = fold srcBase stepFun_rc

------------------------------------------------------------------------
-- Base:  reflCert ze# = cZe  (ze# = cZe = pi O O).

reflCert_ze : Deriv (eqF (ap1 reflCert ze#) cZe)
reflCert_ze =
  ruleTrans (cong1 reflCert pi_O_O)
    (ruleTrans (fold_at_O srcBase stepFun_rc) srcBaseAtO)

------------------------------------------------------------------------
-- Node plumbing for reflCert (mirrors T4.ParEnds.NodePlumb).

module NodePlumbR (A b : Term) where
  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec srcBase stepFun_rc) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  np_unfold : Deriv (eqF (ap1 reflCert node) (ap1 stepBody_rc input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold srcBase stepFun_rc A b)
              (axPost stepBody_rc pi P_outer (ap1 Snd prev))

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
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 reflCert ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt srcBase stepFun_rc O P_outer))
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
                              (ap2 (iter Snd) (HistP_sbt srcBase stepFun_rc O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt srcBase stepFun_rc O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt srcBase stepFun_rc O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_refl : Deriv (eqF (HPsbt srcBase stepFun_rc O ct P_outer) (ap1 reflCert ct))
        HP_to_refl = lookup_eq_fold srcBase stepFun_rc ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_refl

------------------------------------------------------------------------
-- Dispatch for reflCert (2-way:  tag1 -> cellSu ; else cellAd).

module DispatchR (A b : Term) where
  open NodePlumbR A b

  pairC : Term
  pairC = ap1 (C pi cellSu cellAd) input_pkg

  fst_pairC : Deriv (eqF (ap1 Fst pairC) (ap1 cellSu input_pkg))
  fst_pairC = ruleTrans (cong1 Fst (ax_C pi cellSu cellAd input_pkg))
                        (axFst (ap1 cellSu input_pkg) (ap1 cellAd input_pkg))
  snd_pairC : Deriv (eqF (ap1 Snd pairC) (ap1 cellAd input_pkg))
  snd_pairC = ruleTrans (cong1 Snd (ax_C pi cellSu cellAd input_pkg))
                        (axSnd (ap1 cellSu input_pkg) (ap1 cellAd input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody_rc input_pkg)
                     (ap2 condFork pairC (ap1 test1 input_pkg)))
  sb_eq = ax_C condFork (C pi cellSu cellAd) test1 input_pkg

  test1_val : Deriv (eqF (ap1 test1 input_pkg) (ap2 natEqF (ap1 s A) (natCode 1)))
  test1_val =
    ruleTrans (ax_C natEqF get_tag (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 1 input_pkg)))

------------------------------------------------------------------------
-- reflCert(su# t) = cSu (reflCert t) .   ( node = pi (s O) t , A = O )

reflCert_su : (t : Term) -> Deriv (eqF (ap1 reflCert (su# t)) (cSu (ap1 reflCert t)))
reflCert_su t =
  let open NodePlumbR O t
      open DispatchR O t
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      to_cell : Deriv (eqF (ap1 reflCert (su# t)) (ap1 cellSu input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairC t1_fire)
              (ruleTrans (condFork_true_nc pairC O) fst_pairC)))
      rec : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 reflCert t))
      rec = np_lookup_gen get_rc t np_rc leq_b_P
      cellSu_value : Deriv (eqF (ap1 cellSu input_pkg) (cSu (ap1 reflCert t)))
      cellSu_value =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) rec))
  in ruleTrans to_cell cellSu_value

------------------------------------------------------------------------
-- reflCert(ad# a b) = cAd (reflCert a) (reflCert b) .
--   ( node = pi (s (natCode 1)) (Pair a b) , A = natCode 1 ; test1 skip )

reflCert_ad : (a b : Term) ->
  Deriv (eqF (ap1 reflCert (ad# a b)) (cAd (ap1 reflCert a) (ap1 reflCert b)))
reflCert_ad a b =
  let open NodePlumbR (natCode 1) (ap2 pi a b)
      open DispatchR (natCode 1) (ap2 pi a b)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      to_cell : Deriv (eqF (ap1 reflCert (ad# a b)) (ap1 cellAd input_pkg))
      to_cell =
        ruleTrans np_unfold
          (ruleTrans sb_eq
            (ruleTrans (congR condFork pairC t1_O)
              (ruleTrans (condFork_false pairC) snd_pairC)))
      lcIdx_eq : Deriv (eqF (ap1 lcIdx input_pkg) a)
      lcIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                           (ruleTrans (cong1 Fst np_rc) (axFst a b))
      rcIdx_eq : Deriv (eqF (ap1 rcIdx input_pkg) b)
      rcIdx_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                           (ruleTrans (cong1 Snd np_rc) (axSnd a b))
      leq_a : Deriv (leq a P_outer)
      leq_a = leq_trans a (ap2 pi a b) P_outer (leq_pi_left a b) leq_b_P
      leq_b' : Deriv (leq b P_outer)
      leq_b' = leq_trans b (ap2 pi a b) P_outer (leq_pi_right a b) leq_b_P
      rec1 : Deriv (eqF (ap1 (lookupAt lcIdx) input_pkg) (ap1 reflCert a))
      rec1 = np_lookup_gen lcIdx a lcIdx_eq leq_a
      rec2 : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 reflCert b))
      rec2 = np_lookup_gen rcIdx b rcIdx_eq leq_b'
      inner_value : Deriv (eqF (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                                (ap2 pi (ap1 reflCert a) (ap1 reflCert b)))
      inner_value =
        ruleTrans (ax_C pi (lookupAt lcIdx) (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) rec1)
                     (congR pi (ap1 reflCert a) rec2))
      cellAd_value : Deriv (eqF (ap1 cellAd input_pkg)
                                 (cAd (ap1 reflCert a) (ap1 reflCert b)))
      cellAd_value =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lcIdx) (lookupAt rcIdx)) input_pkg)
                               (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_value))
  in ruleTrans to_cell cellAd_value
