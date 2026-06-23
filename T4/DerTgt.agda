{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTgt -- the OBJECT TARGET endpoint  tgtF : Fun1  over the DerCode
-- derivation coding, the mirror of T4.DerSrc.  Same  binRec  engine and tag
-- cascade; the cells build the TARGET term of each parallel-reduction rule:
--
--   tgtF (derZe)        = ze#
--   tgtF (derSu d)      = su# (tgtF d)
--   tgtF (derAd d1 d2)  = ad# (tgtF d1) (tgtF d2)
--   tgtF (derRO d)      = tgtF d                          ( ad ze y => y' )
--   tgtF (derRS d1 d2)  = su# (ad# (tgtF d1) (tgtF d2))   ( ad (su x) y => su (ad x' y') )
--
-- Reuses the generic plumbing helpers proved in T4.DerSrc (fork_*, testEq_*,
-- nIdxOf/lIdxOf/rIdxOf, leqChildL/R, ze#F/ze#F_at, the neq witnesses) and the
-- shared su / ad cells; only roCell / rsCell differ.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTgt where

open import T4.Base

open import T4.DerCode
  using ( derZe ; derSu ; derAd ; derRO ; derRS
        ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS ; filler )
open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.FoldRec using ( lookupAt )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# )

open import T4.DerSrc
  using ( ze#F ; ze#F_at ; suCell ; adCell ; testEq
        ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; nIdxOf ; lIdxOf ; rIdxOf ; leqChildL ; leqChildR
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church       using ( pi )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq )

------------------------------------------------------------------------
-- SECTION 1.  The TARGET-specific cells and the cascade.

roCellT : Fun1                                         -- tgtF l  (RO drops the head)
roCellT = lookupAt lIdx

rsCellT : Fun1                                         -- su# (ad# (tgtF l) (tgtF r))
rsCellT = C pi (constN 1) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)))

restROT : Fun1
restROT = C condFork (C pi roCellT rsCellT) (testEq 3)

restAdT : Fun1
restAdT = C condFork (C pi adCell restROT) (testEq 2)

cellNodeT : Fun1
cellNodeT = C condFork (C pi suCell restAdT) (testEq 1)

tgtF : Fun1
tgtF = binRec Z ze#F cellNodeT

------------------------------------------------------------------------
-- SECTION 2.  Leaf:  tgtF (derZe) = ze# .

tgtF_derZe : Deriv (eqF (ap1 tgtF derZe) ze#)
tgtF_derZe =
  let open NP Z ze#F cellNodeT O dgZe
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (ze#F_at input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  su:  tgtF (derSu d) = su# (tgtF d) .

tgtF_derSu : (d : Term) -> Deriv (eqF (ap1 tgtF (derSu d)) (su# (ap1 tgtF d)))
tgtF_derSu d =
  let payload : Term
      payload = ap2 Pair dgSu (ap2 Pair d filler)
      open NP Z ze#F cellNodeT (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgSu)
      nieq = nIdxOf input_pkg dgSu d filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 tgtF d))
      recL = np_lookup_gen lIdx d (lIdxOf input_pkg dgSu d filler np_rc)
               (leqChildL dgSu d filler P_outer leq_b_P)

      cell_fires : Deriv (eqF (ap1 cellNodeT input_pkg) (ap1 suCell input_pkg))
      cell_fires = fork_true_to_fst suCell restAdT (testEq 1) input_pkg
                     (testEq_fire 1 input_pkg nieq)
      suCell_val : Deriv (eqF (ap1 suCell input_pkg) (su# (ap1 tgtF d)))
      suCell_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt lIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) recL))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires suCell_val)

------------------------------------------------------------------------
-- SECTION 4.  ad:  tgtF (derAd d1 d2) = ad# (tgtF d1) (tgtF d2) .

tgtF_derAd : (d1 d2 : Term) ->
  Deriv (eqF (ap1 tgtF (derAd d1 d2)) (ad# (ap1 tgtF d1) (ap1 tgtF d2)))
tgtF_derAd d1 d2 =
  let payload : Term
      payload = ap2 Pair dgAd (ap2 Pair d1 d2)
      open NP Z ze#F cellNodeT (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd d1 d2 np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 tgtF d1))
      recL = np_lookup_gen lIdx d1 (lIdxOf input_pkg dgAd d1 d2 np_rc)
               (leqChildL dgAd d1 d2 P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 tgtF d2))
      recR = np_lookup_gen rIdx d2 (rIdxOf input_pkg dgAd d1 d2 np_rc)
               (leqChildR dgAd d1 d2 P_outer leq_b_P)

      cell_fires : Deriv (eqF (ap1 cellNodeT input_pkg) (ap1 adCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAdT (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCell restROT (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                             (ap2 pi (ap1 tgtF d1) (ap1 tgtF d2)))
      inner_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 tgtF d1) recR))
      adCell_val : Deriv (eqF (ap1 adCell input_pkg) (ad# (ap1 tgtF d1) (ap1 tgtF d2)))
      adCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires adCell_val)

------------------------------------------------------------------------
-- SECTION 5.  rO:  tgtF (derRO d) = tgtF d  (the head rule drops to the child).

tgtF_derRO : (d : Term) -> Deriv (eqF (ap1 tgtF (derRO d)) (ap1 tgtF d))
tgtF_derRO d =
  let payload : Term
      payload = ap2 Pair dgRO (ap2 Pair d filler)
      open NP Z ze#F cellNodeT (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRO)
      nieq = nIdxOf input_pkg dgRO d filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 tgtF d))
      recL = np_lookup_gen lIdx d (lIdxOf input_pkg dgRO d filler np_rc)
               (leqChildL dgRO d filler P_outer leq_b_P)

      -- cellNodeT -> (skip su) restAdT -> (skip ad) restROT -> (fire ro) roCellT.
      cell_fires : Deriv (eqF (ap1 cellNodeT input_pkg) (ap1 roCellT input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAdT (testEq 1) input_pkg
                     (testEq_skip 3 1 input_pkg w31 nieq))
          (ruleTrans (fork_false_to_snd adCell restROT (testEq 2) input_pkg
                        (testEq_skip 3 2 input_pkg w32 nieq))
                     (fork_true_to_fst roCellT rsCellT (testEq 3) input_pkg
                        (testEq_fire 3 input_pkg nieq)))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires recL)

------------------------------------------------------------------------
-- SECTION 6.  rS:  tgtF (derRS d1 d2) = su# (ad# (tgtF d1) (tgtF d2)) .

tgtF_derRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 tgtF (derRS d1 d2)) (su# (ad# (ap1 tgtF d1) (ap1 tgtF d2))))
tgtF_derRS d1 d2 =
  let payload : Term
      payload = ap2 Pair dgRS (ap2 Pair d1 d2)
      open NP Z ze#F cellNodeT (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRS)
      nieq = nIdxOf input_pkg dgRS d1 d2 np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 tgtF d1))
      recL = np_lookup_gen lIdx d1 (lIdxOf input_pkg dgRS d1 d2 np_rc)
               (leqChildL dgRS d1 d2 P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 tgtF d2))
      recR = np_lookup_gen rIdx d2 (rIdxOf input_pkg dgRS d1 d2 np_rc)
               (leqChildR dgRS d1 d2 P_outer leq_b_P)

      cell_fires : Deriv (eqF (ap1 cellNodeT input_pkg) (ap1 rsCellT input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAdT (testEq 1) input_pkg
                     (testEq_skip 4 1 input_pkg w41 nieq))
          (ruleTrans (fork_false_to_snd adCell restROT (testEq 2) input_pkg
                        (testEq_skip 4 2 input_pkg w42 nieq))
                     (fork_false_to_snd roCellT rsCellT (testEq 3) input_pkg
                        (testEq_skip 4 3 input_pkg w43 nieq)))
      -- inner  ad# (tgtF d1) (tgtF d2)  then wrap with su#.
      inner2_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                              (ap2 pi (ap1 tgtF d1) (ap1 tgtF d2)))
      inner2_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 tgtF d1) recR))
      mid_val : Deriv (eqF (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input_pkg)
                           (ad# (ap1 tgtF d1) (ap1 tgtF d2)))
      mid_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner2_val))
      rsCell_val : Deriv (eqF (ap1 rsCellT input_pkg)
                             (su# (ad# (ap1 tgtF d1) (ap1 tgtF d2))))
      rsCell_val =
        ruleTrans (ax_C pi (constN 1) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input_pkg)
                         (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) mid_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires rsCell_val)
