{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ValF -- the OBJECT DENOTATIONAL VALUE functor  valF : Fun1  over coded
-- TERMS (T4.TrsCodeObj : ze# = pi O O = O the fold BASE, su# = tag 1, ad# = tag
-- 2), a primitive-recursive  binRec  fold producing the NUMERIC value of a term,
-- with its defining equations as object Deriv :
--
--   valF (ze#)      = O
--   valF (su# t)    = s (valF t)
--   valF (ad# a b)  = sigma (valF a) (valF b)            -- object addition
--
-- This is the standard-model interpretation of the addition TRS: every coded
-- term denotes a numeral.  Unlike  devF  the  ad#  cell does NOT dispatch on the
-- head (value is unconditional sigma of the child values), so there is a single
-- flat  valF_ad#  equation.  This is the quantifier-free invariant that the
-- object soundness induction for Con(Eq) carries.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ValF where

open import T4.Base

open import T4.BinTree using ( binRec )
open import T4.ParsObj using ( foldOf ; stepOf ; test1 ; module NP )
open import T4.FoldRec using ( lookupAt ; fold_at_O )
open import T4.LenR    using ( get_rc )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )
open import T4.ParEnds  using ( pi_O_O )
open import T4.DerSrc   using ( w21 )

open import BRA3.Church       using ( pi ; sigma )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq ; Post )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq )

------------------------------------------------------------------------
-- SECTION 1.  The cells and  valF .

-- su# payload IS the child t, index  get_rc ; cell value = s (valF t).
suCellV : Fun1
suCellV = compose1U s (lookupAt get_rc)

-- ad# payload is  pi a b ; children a, b read by Fst/Snd of get_rc.
lcD : Fun1
lcD = compose1U Fst get_rc                             -- left subterm a
rcD : Fun1
rcD = compose1U Snd get_rc                             -- right subterm b

valA : Fun1                                            -- valF a
valA = lookupAt lcD
valB : Fun1                                            -- valF b
valB = lookupAt rcD

cellAdV : Fun1                                         -- sigma (valF a) (valF b)
cellAdV = C sigma valA valB

valF : Fun1
valF = binRec Z suCellV cellAdV

------------------------------------------------------------------------
-- SECTION 2.  Base:  valF (ze#) = O   (ze# = pi O O = O, the fold base).

valF_O : Deriv (eqF (ap1 valF O) O)
valF_O = ruleTrans (fold_at_O Z (Post (stepOf suCellV cellAdV) pi)) (axZ O)

valF_ze# : Deriv (eqF (ap1 valF ze#) O)
valF_ze# = ruleTrans (cong1 valF pi_O_O) valF_O

------------------------------------------------------------------------
-- SECTION 3.  su:  valF (su# t) = s (valF t)   (su# = tag 1 = the leaf cell).

valF_su# : (t : Term) -> Deriv (eqF (ap1 valF (su# t)) (ap1 s (ap1 valF t)))
valF_su# t =
  let open NP Z suCellV cellAdV O t
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      recC : Deriv (eqF (ap1 (lookupAt get_rc) input_pkg) (ap1 valF t))
      recC = np_lookup_gen get_rc t np_rc leq_b_P
      cell_val : Deriv (eqF (ap1 suCellV input_pkg) (ap1 s (ap1 valF t)))
      cell_val = ruleTrans (compose1U_eq s (lookupAt get_rc) input_pkg) (cong1 s recC)
  in ruleTrans (collapse_fst t1_fire) cell_val

------------------------------------------------------------------------
-- SECTION 4.  ad:  valF (ad# a b) = sigma (valF a) (valF b)   (tag 2 node,
-- no head dispatch -- the value is unconditionally the sum of the children).

valF_ad# : (a b : Term) ->
  Deriv (eqF (ap1 valF (ad# a b)) (ap2 sigma (ap1 valF a) (ap1 valF b)))
valF_ad# a b =
  let open NP Z suCellV cellAdV (natCode 1) (ap2 Pair a b)
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      lcD_eq : Deriv (eqF (ap1 lcD input_pkg) a)
      lcD_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                 (ruleTrans (cong1 Fst np_rc) (axFst a b))
      rcD_eq : Deriv (eqF (ap1 rcD input_pkg) b)
      rcD_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                 (ruleTrans (cong1 Snd np_rc) (axSnd a b))
      recA : Deriv (eqF (ap1 (lookupAt lcD) input_pkg) (ap1 valF a))
      recA = np_lookup_gen lcD a lcD_eq
               (leq_trans a (ap2 Pair a b) P_outer (leq_pi_left a b) leq_b_P)
      recB : Deriv (eqF (ap1 (lookupAt rcD) input_pkg) (ap1 valF b))
      recB = np_lookup_gen rcD b rcD_eq
               (leq_trans b (ap2 Pair a b) P_outer (leq_pi_right a b) leq_b_P)
      cell_val : Deriv (eqF (ap1 cellAdV input_pkg) (ap2 sigma (ap1 valF a) (ap1 valF b)))
      cell_val =
        ruleTrans (ax_C sigma valA valB input_pkg)
          (ruleTrans (congL sigma (ap1 valB input_pkg) recA)
                     (congR sigma (ap1 valF a) recB))
  in ruleTrans (collapse_snd t1_O) cell_val
