{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SizedFold -- the GENERIC course-of-values fold harness for the SIZE-
-- PREFIXED derivation coding (T4.DerCodeS).  Unlike  binRec  (whose test1
-- dispatches on  Fst = the leaf/node tag), a sized code  p = pi (size) body
-- has  Fst p = size , so EVERY sized code is a fold NODE  pi (s A) b  and the
-- sbf fires uniformly; the real 5-way dispatch happens INSIDE the sbf on
-- dtag = Fst body.  So we use  fold Z (Post sbf pi)  directly (NOT binRec) and
-- expose the generic node lemmas for an ARBITRARY sbf:
--
--   szRunF sbf = fold Z (Post sbf pi)
--   sz_unfold : szRunF sbf (pi (s A) b) = sbf (szPkg sbf A b)      (fold fires)
--   sz_rc     : get_rc (szPkg sbf A b) = b                            (payload)
--   sz_lookup : (idx reads ct, ct <= P_outer) -> lookupAt idx pkg = szRunF sbf ct
--   sz_leq_b  : leq b (P_outer A b)                                    (payload bound)
--
-- These are exactly  T4.ParsObj.NP 's generic pieces (np_unfold / np_rc /
-- np_lookup_gen = T4.OpaqueLookup.lookup_op / leq_b_P), abstracted over the sbf.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.SizedFold where

open import T4.Base

open import T4.FoldRec using ( fold ; fold_node_unfold ; lookupAt ; get_newK ; get_newK_at_pi )
open import T4.LenR    using ( get_rc )
open import T4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.CoVSpec using ( cov_spec )
open import T4.LeqMono using ( leq_sigma_right )

open import BRA3.Church      using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.PairAlgebra using ( compose1U_eq )

------------------------------------------------------------------------
-- SECTION 1.  The fold and its input package.

szRunF : Fun1 -> Fun1
szRunF sbf = fold Z (Post sbf pi)

-- the outer "P_outer" of a node  pi (s A) b .
Pout : Term -> Term -> Term
Pout A b = pi_succ_outer A b

-- the recovery package the fold hands the sbf at node  pi (s A) b .
szPkg : Fun1 -> Term -> Term -> Term
szPkg sbf A b =
  ap2 pi (Pout A b) (ap1 Snd (ap2 (cov_spec Z (Post sbf pi)) O (Pout A b)))

------------------------------------------------------------------------
-- SECTION 2.  The node lemmas (generic in  sbf ).

sz_unfold : (sbf : Fun1) (A b : Term) ->
  Deriv (eqF (ap1 (szRunF sbf) (ap2 pi (ap1 s A) b)) (ap1 sbf (szPkg sbf A b)))
sz_unfold sbf A b =
  ruleTrans (fold_node_unfold Z (Post sbf pi) A b)
            (axPost sbf pi (Pout A b)
              (ap1 Snd (ap2 (cov_spec Z (Post sbf pi)) O (Pout A b))))

sz_rc : (sbf : Fun1) (A b : Term) ->
  Deriv (eqF (ap1 get_rc (szPkg sbf A b)) b)
sz_rc sbf A b =
  let prevS : Term
      prevS = ap1 Snd (ap2 (cov_spec Z (Post sbf pi)) O (Pout A b))
  in ruleTrans (compose1U_eq Snd get_newK (szPkg sbf A b))
       (ruleTrans (cong1 Snd (get_newK_at_pi (Pout A b) prevS))
         (ruleTrans (cong1 Snd (ruleSym (pi_at_succ A b)))
                    (axSnd (ap1 s A) b)))

sz_lookup : (sbf idx : Fun1) (A b ct : Term) ->
  Deriv (eqF (ap1 idx (szPkg sbf A b)) ct) ->
  Deriv (leq ct (Pout A b)) ->
  Deriv (eqF (ap1 (lookupAt idx) (szPkg sbf A b)) (ap1 (szRunF sbf) ct))
sz_lookup sbf idx A b ct idx_eq leq_ct =
  lookup_op Z sbf idx (Pout A b) ct idx_eq leq_ct

sz_leq_b : (A b : Term) -> Deriv (leq b (Pout A b))
sz_leq_b A b =
  leq_sigma_right (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

-- the STORED size  Fst (get_newK pkg) = s A = dsize (pi (s A) b)  (Fst-analog of sz_rc).
sz_self : (sb : Fun1) (A b : Term) ->
  Deriv (eqF (ap1 (compose1U Fst get_newK) (szPkg sb A b)) (ap1 s A))
sz_self sb A b =
  let prevS : Term
      prevS = ap1 Snd (ap2 (cov_spec Z (Post sb pi)) O (Pout A b))
  in ruleTrans (compose1U_eq Fst get_newK (szPkg sb A b))
       (ruleTrans (cong1 Fst (get_newK_at_pi (Pout A b) prevS))
         (ruleTrans (cong1 Fst (ruleSym (pi_at_succ A b)))
                    (axFst (ap1 s A) b)))
