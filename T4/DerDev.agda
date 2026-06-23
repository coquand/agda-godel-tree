{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerDev -- the OBJECT COMPLETE DEVELOPMENT  devF : Fun1  over coded TERMS
-- (T4.TrsCodeObj : ze# = pi O O = O is the fold BASE, su# = tag 1, ad# = tag 2),
-- a primitive-recursive  binRec  fold, with its defining equations as object
-- Deriv .  This is Takahashi's complete development internalised:
--
--   devF (ze#)              = ze#
--   devF (su# t)            = su# (devF t)
--   devF (ad# ze# y)        = devF y                                  (rO redex)
--   devF (ad# (su# x) y)    = su# (ad# (devF x) (devF y))             (rS redex)
--   devF (ad# (ad# p q) y)  = ad# (devF (ad# p q)) (devF y)           (no root redex)
--
-- The  ad#  case is the depth-2 dispatch: it inspects the HEAD of the left
-- subterm  a  (the redex check) and reuses the recursion values  devF a / devF b
-- already produced by the fold (in the rS case  devF x = ar (devF a) , since
-- devF a = devF (su# x) = su# (devF x)).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerDev where

open import T4.Base

open import T4.BinTree using ( binRec )
open import T4.ParsObj using ( foldOf ; stepOf ; test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt ; fold_at_O )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagZe ; tagSu ; tagAd ; ar ; ar_su )
open import T4.ParEnds  using ( pi_O_O )

open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  Child-index Fun1s and the cells.

-- su# payload IS the child t (b = t), so its index is  get_rc  itself.
suCellD : Fun1                                         -- su# (devF t)
suCellD = C pi (constN 1) (lookupAt get_rc)

-- ad# payload is  pi a b ; children a, b read by Fst/Snd of get_rc.
lcD : Fun1
lcD = compose1U Fst get_rc                             -- left subterm a
rcD : Fun1
rcD = compose1U Snd get_rc                             -- right subterm b
headA : Fun1
headA = compose1U Fst lcD                              -- head tag of a

devA : Fun1                                            -- devF a
devA = lookupAt lcD
devB : Fun1                                            -- devF b
devB = lookupAt rcD

zeBranch : Fun1                                        -- devF b
zeBranch = devB
suBranch : Fun1                                        -- su# (ad# (ar (devF a)) (devF b))
suBranch = C pi (constN 1) (C pi (constN 2) (C pi (compose1U Snd devA) devB))
adBranch : Fun1                                        -- ad# (devF a) (devF b)
adBranch = C pi (constN 2) (C pi devA devB)

testHd : Nat -> Fun1
testHd k = C natEqF headA (constN k)

restSuD : Fun1                                         -- head=su(1) -> suBranch ; else adBranch
restSuD = C condFork (C pi suBranch adBranch) (testHd 1)
cellAdD : Fun1                                         -- head=ze(0) -> zeBranch ; else restSuD
cellAdD = C condFork (C pi zeBranch restSuD) (testHd 0)

devF : Fun1
devF = binRec Z suCellD cellAdD

------------------------------------------------------------------------
-- SECTION 2.  head-tag tests on  headA  (mirror DerSrc.testEq_*).

testHd_fire : (k : Nat) (input : Term) ->
  Deriv (eqF (ap1 headA input) (natCode k)) ->
  Deriv (eqF (ap1 (testHd k) input) (ap1 s O))
testHd_fire k input heq =
  ruleTrans (ax_C natEqF headA (constN k) input)
    (ruleTrans (congL natEqF (ap1 (constN k) input) heq)
      (ruleTrans (congR natEqF (natCode k) (constN_eq k input)) (natEq_eq k)))

testHd_skip : (m k : Nat) (input : Term) -> NatNeqWitness m k ->
  Deriv (eqF (ap1 headA input) (natCode m)) ->
  Deriv (eqF (ap1 (testHd k) input) O)
testHd_skip m k input w heq =
  ruleTrans (ax_C natEqF headA (constN k) input)
    (ruleTrans (congL natEqF (ap1 (constN k) input) heq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq k input)) (natEqF_at_neq m k w)))

w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())
w10 : NatNeqWitness 1 0
w10 = decideNatNeq 1 0 (\ ())
w20 : NatNeqWitness 2 0
w20 = decideNatNeq 2 0 (\ ())

------------------------------------------------------------------------
-- SECTION 3.  Base:  devF (ze#) = ze#   (ze# = pi O O = O, the fold base).

devF_O : Deriv (eqF (ap1 devF O) O)
devF_O = ruleTrans (fold_at_O Z (Post (stepOf suCellD cellAdD) pi)) (axZ O)

devF_ze# : Deriv (eqF (ap1 devF ze#) ze#)
devF_ze# = ruleTrans (cong1 devF pi_O_O) (ruleTrans devF_O (ruleSym pi_O_O))

------------------------------------------------------------------------
-- SECTION 4.  su:  devF (su# t) = su# (devF t)   (su# = tag 1 = the leaf cell).

devF_su# : (t : Term) -> Deriv (eqF (ap1 devF (su# t)) (su# (ap1 devF t)))
devF_su# t =
  let open NP Z suCellD cellAdD O t
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      recC : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 devF t))
      recC = np_lookup_gen get_rc t np_rc leq_b_P
      cell_val : Deriv (eqF (ap1 suCellD input_pkg) (su# (ap1 devF t)))
      cell_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt get_rc) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt get_rc) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) recC))
  in ruleTrans (collapse_fst t1_fire) cell_val

------------------------------------------------------------------------
-- SECTION 5.  The ad# cases (depth-2 redex dispatch on  headA = Fst a ).
-- Node  ad# a b = pi (s (s O)) (pi a b) :  A = natCode 1 , payload = pi a b.

-- rO redex:  devF (ad# ze# y) = devF y .
devF_ad_ze : (y : Term) -> Deriv (eqF (ap1 devF (ad# ze# y)) (ap1 devF y))
devF_ad_ze y =
  let open NP Z suCellD cellAdD (natCode 1) (ap2 Pair ze# y)
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      rcD_eq : Deriv (eqF (ap1 rcD input_pkg) y)
      rcD_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                 (ruleTrans (cong1 Snd np_rc) (axSnd ze# y))
      recB : Deriv (eqF (ap1 (lookupAt rcD) input_pkg) (ap1 devF y))
      recB = np_lookup_gen rcD y rcD_eq
               (leq_trans y (ap2 Pair ze# y) P_outer (leq_pi_right ze# y) leq_b_P)
      lcD_eq : Deriv (eqF (ap1 lcD input_pkg) ze#)
      lcD_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                 (ruleTrans (cong1 Fst np_rc) (axFst ze# y))
      headA_eq : Deriv (eqF (ap1 headA input_pkg) O)
      headA_eq = ruleTrans (compose1U_eq Fst lcD input_pkg)
                   (ruleTrans (cong1 Fst lcD_eq) (axFst O O))
      cell_fires : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 zeBranch input_pkg))
      cell_fires = fork_true_to_fst zeBranch restSuD (testHd 0) input_pkg
                     (testHd_fire 0 input_pkg headA_eq)
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires recB)

-- rS redex:  devF (ad# (su# x) y) = su# (ad# (devF x) (devF y)) .
devF_ad_su : (x y : Term) ->
  Deriv (eqF (ap1 devF (ad# (su# x) y)) (su# (ad# (ap1 devF x) (ap1 devF y))))
devF_ad_su x y =
  let open NP Z suCellD cellAdD (natCode 1) (ap2 Pair (su# x) y)
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      lcD_eq : Deriv (eqF (ap1 lcD input_pkg) (su# x))
      lcD_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                 (ruleTrans (cong1 Fst np_rc) (axFst (su# x) y))
      rcD_eq : Deriv (eqF (ap1 rcD input_pkg) y)
      rcD_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                 (ruleTrans (cong1 Snd np_rc) (axSnd (su# x) y))
      recA : Deriv (eqF (ap1 (lookupAt lcD) input_pkg) (ap1 devF (su# x)))
      recA = np_lookup_gen lcD (su# x) lcD_eq
               (leq_trans (su# x) (ap2 Pair (su# x) y) P_outer (leq_pi_left (su# x) y) leq_b_P)
      recB : Deriv (eqF (ap1 (lookupAt rcD) input_pkg) (ap1 devF y))
      recB = np_lookup_gen rcD y rcD_eq
               (leq_trans y (ap2 Pair (su# x) y) P_outer (leq_pi_right (su# x) y) leq_b_P)
      headA_eq : Deriv (eqF (ap1 headA input_pkg) (natCode 1))
      headA_eq = ruleTrans (compose1U_eq Fst lcD input_pkg)
                   (ruleTrans (cong1 Fst lcD_eq) (axFst tagSu x))
      -- cellAdD -> (skip ze) restSuD -> (fire su) suBranch.
      cell_fires : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 suBranch input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd zeBranch restSuD (testHd 0) input_pkg
                     (testHd_skip 1 0 input_pkg w10 headA_eq))
                  (fork_true_to_fst suBranch adBranch (testHd 1) input_pkg
                     (testHd_fire 1 input_pkg headA_eq))
      -- ar (devF a) = devF x , because devF a = devF (su# x) = su# (devF x).
      inner_a : Deriv (eqF (ap1 (compose1U Snd devA) input_pkg) (ap1 devF x))
      inner_a =
        ruleTrans (compose1U_eq Snd devA input_pkg)
          (ruleTrans (cong1 Snd recA)
            (ruleTrans (cong1 Snd (devF_su# x)) (ar_su (ap1 devF x))))
      inner_val : Deriv (eqF (ap1 (C pi (compose1U Snd devA) devB) input_pkg)
                             (ap2 pi (ap1 devF x) (ap1 devF y)))
      inner_val =
        ruleTrans (ax_C pi (compose1U Snd devA) devB input_pkg)
          (ruleTrans (congL pi (ap1 devB input_pkg) inner_a)
                     (congR pi (ap1 devF x) recB))
      mid_val : Deriv (eqF (ap1 (C pi (constN 2) (C pi (compose1U Snd devA) devB)) input_pkg)
                           (ad# (ap1 devF x) (ap1 devF y)))
      mid_val =
        ruleTrans (ax_C pi (constN 2) (C pi (compose1U Snd devA) devB) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (compose1U Snd devA) devB) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_val))
      suBranch_val : Deriv (eqF (ap1 suBranch input_pkg)
                             (su# (ad# (ap1 devF x) (ap1 devF y))))
      suBranch_val =
        ruleTrans (ax_C pi (constN 1) (C pi (constN 2) (C pi (compose1U Snd devA) devB)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (compose1U Snd devA) devB)) input_pkg)
                         (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) mid_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires suBranch_val)

-- no root redex:  devF (ad# (ad# p q) y) = ad# (devF (ad# p q)) (devF y) .
devF_ad_ad : (p q y : Term) ->
  Deriv (eqF (ap1 devF (ad# (ad# p q) y)) (ad# (ap1 devF (ad# p q)) (ap1 devF y)))
devF_ad_ad p q y =
  let open NP Z suCellD cellAdD (natCode 1) (ap2 Pair (ad# p q) y)
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      lcD_eq : Deriv (eqF (ap1 lcD input_pkg) (ad# p q))
      lcD_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                 (ruleTrans (cong1 Fst np_rc) (axFst (ad# p q) y))
      rcD_eq : Deriv (eqF (ap1 rcD input_pkg) y)
      rcD_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                 (ruleTrans (cong1 Snd np_rc) (axSnd (ad# p q) y))
      recA : Deriv (eqF (ap1 (lookupAt lcD) input_pkg) (ap1 devF (ad# p q)))
      recA = np_lookup_gen lcD (ad# p q) lcD_eq
               (leq_trans (ad# p q) (ap2 Pair (ad# p q) y) P_outer (leq_pi_left (ad# p q) y) leq_b_P)
      recB : Deriv (eqF (ap1 (lookupAt rcD) input_pkg) (ap1 devF y))
      recB = np_lookup_gen rcD y rcD_eq
               (leq_trans y (ap2 Pair (ad# p q) y) P_outer (leq_pi_right (ad# p q) y) leq_b_P)
      headA_eq : Deriv (eqF (ap1 headA input_pkg) (natCode 2))
      headA_eq = ruleTrans (compose1U_eq Fst lcD input_pkg)
                   (ruleTrans (cong1 Fst lcD_eq) (axFst tagAd (ap2 Pair p q)))
      -- cellAdD -> (skip ze) restSuD -> (skip su) adBranch.
      cell_fires : Deriv (eqF (ap1 cellAdD input_pkg) (ap1 adBranch input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd zeBranch restSuD (testHd 0) input_pkg
                     (testHd_skip 2 0 input_pkg w20 headA_eq))
                  (fork_false_to_snd suBranch adBranch (testHd 1) input_pkg
                     (testHd_skip 2 1 input_pkg w21 headA_eq))
      inner_val : Deriv (eqF (ap1 (C pi devA devB) input_pkg)
                             (ap2 pi (ap1 devF (ad# p q)) (ap1 devF y)))
      inner_val =
        ruleTrans (ax_C pi devA devB input_pkg)
          (ruleTrans (congL pi (ap1 devB input_pkg) recA)
                     (congR pi (ap1 devF (ad# p q)) recB))
      adBranch_val : Deriv (eqF (ap1 adBranch input_pkg)
                             (ad# (ap1 devF (ad# p q)) (ap1 devF y)))
      adBranch_val =
        ruleTrans (ax_C pi (constN 2) (C pi devA devB) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi devA devB) input_pkg) (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires adBranch_val)
