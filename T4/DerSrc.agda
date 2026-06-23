{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerSrc -- the OBJECT SOURCE endpoint  srcF : Fun1  over the DerCode
-- derivation coding, a primitive-recursive  binRec  fold, with all five
-- defining equations as object  Deriv .  This is the endpoint-projection half
-- of Theorem A's infrastructure (T4/CON-T0-ARCHITECTURE.md), rebuilt on
-- T4.BinTree (DISCARDING the ParEnds / isCert fold), modelled on
-- T4.BinTree.isWfW (same  binRec  engine + np_lookup_gen recovery).
--
--   srcF (derZe)        = ze#
--   srcF (derSu d)      = su# (srcF d)
--   srcF (derAd d1 d2)  = ad# (srcF d1) (srcF d2)
--   srcF (derRO d)      = ad# ze# (srcF d)
--   srcF (derRS d1 d2)  = ad# (su# (srcF d1)) (srcF d2)
--
-- The node cell dispatches on the derivation tag (label 1..4) with a nested
-- condFork / natEqF cascade (convention: natEqF = s O when equal -> condFork
-- picks Fst; = O otherwise -> picks Snd), and recovers the child fold-values via
-- T4.ParsObj.NP.np_lookup_gen (children are < node by the leq_pi bounds).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerSrc where

open import T4.Base

open import T4.DerCode
  using ( derZe ; derSu ; derAd ; derRO ; derRS
        ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS ; filler )
open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.LenR    using ( get_rc )
open import T4.FoldRec using ( lookupAt )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.TrsCodeObj using ( ze# ; su# ; ad# ; tagSu ; tagAd )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 1.  The cells (leaf + the four node-constructor cells).

ze#F : Fun1                                            -- pZe -> ze# = pi O O
ze#F = C pi Z Z

suCell : Fun1                                          -- su# (srcF l)
suCell = C pi (constN 1) (lookupAt lIdx)

adCell : Fun1                                          -- ad# (srcF l) (srcF r)
adCell = C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))

roCell : Fun1                                          -- ad# ze# (srcF l)
roCell = C pi (constN 2) (C pi ze#F (lookupAt lIdx))

rsCell : Fun1                                          -- ad# (su# (srcF l)) (srcF r)
rsCell = C pi (constN 2) (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx))

------------------------------------------------------------------------
-- SECTION 2.  The tag-dispatch cascade and  srcF .
--  testEq k = natEqF (label) (natCode k) ;  fires (s O) exactly when label = k.

testEq : Nat -> Fun1
testEq k = C natEqF nIdx (constN k)

restRO : Fun1
restRO = C condFork (C pi roCell rsCell) (testEq 3)

restAd : Fun1
restAd = C condFork (C pi adCell restRO) (testEq 2)

cellNode : Fun1
cellNode = C condFork (C pi suCell restAd) (testEq 1)

srcF : Fun1
srcF = binRec Z ze#F cellNode

------------------------------------------------------------------------
-- SECTION 3.  Generic plumbing helpers (input given explicitly).

-- condFork picks the Fst branch when its test fires (= s O).
fork_true_to_fst : (A B tst : Fun1) (input : Term) ->
  Deriv (eqF (ap1 tst input) (ap1 s O)) ->
  Deriv (eqF (ap1 (C condFork (C pi A B) tst) input) (ap1 A input))
fork_true_to_fst A B tst input tT =
  ruleTrans (ax_C condFork (C pi A B) tst input)
    (ruleTrans (congR condFork (ap1 (C pi A B) input) tT)
      (ruleTrans (condFork_true_nc (ap1 (C pi A B) input) O)
        (ruleTrans (cong1 Fst (ax_C pi A B input))
                   (axFst (ap1 A input) (ap1 B input)))))

-- condFork picks the Snd branch when its test skips (= O).
fork_false_to_snd : (A B tst : Fun1) (input : Term) ->
  Deriv (eqF (ap1 tst input) O) ->
  Deriv (eqF (ap1 (C condFork (C pi A B) tst) input) (ap1 B input))
fork_false_to_snd A B tst input tF =
  ruleTrans (ax_C condFork (C pi A B) tst input)
    (ruleTrans (congR condFork (ap1 (C pi A B) input) tF)
      (ruleTrans (condFork_false (ap1 (C pi A B) input))
        (ruleTrans (cong1 Snd (ax_C pi A B input))
                   (axSnd (ap1 A input) (ap1 B input)))))

-- the tag-test value, from the recovered label  nIdx input = natCode m .
testEq_fire : (k : Nat) (input : Term) ->
  Deriv (eqF (ap1 nIdx input) (natCode k)) ->
  Deriv (eqF (ap1 (testEq k) input) (ap1 s O))
testEq_fire k input nieq =
  ruleTrans (ax_C natEqF nIdx (constN k) input)
    (ruleTrans (congL natEqF (ap1 (constN k) input) nieq)
      (ruleTrans (congR natEqF (natCode k) (constN_eq k input)) (natEq_eq k)))

testEq_skip : (m k : Nat) (input : Term) -> NatNeqWitness m k ->
  Deriv (eqF (ap1 nIdx input) (natCode m)) ->
  Deriv (eqF (ap1 (testEq k) input) O)
testEq_skip m k input w nieq =
  ruleTrans (ax_C natEqF nIdx (constN k) input)
    (ruleTrans (congL natEqF (ap1 (constN k) input) nieq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq k input)) (natEqF_at_neq m k w)))

-- child-index recovery from  get_rc input = Pair n (Pair l r) .
nIdxOf : (input n l r : Term) ->
  Deriv (eqF (ap1 get_rc input) (ap2 Pair n (ap2 Pair l r))) ->
  Deriv (eqF (ap1 nIdx input) n)
nIdxOf input n l r rc =
  ruleTrans (compose1U_eq Fst get_rc input)
    (ruleTrans (cong1 Fst rc) (axFst n (ap2 Pair l r)))

sndArgOf : (input n l r : Term) ->
  Deriv (eqF (ap1 get_rc input) (ap2 Pair n (ap2 Pair l r))) ->
  Deriv (eqF (ap1 (compose1U Snd get_rc) input) (ap2 Pair l r))
sndArgOf input n l r rc =
  ruleTrans (compose1U_eq Snd get_rc input)
    (ruleTrans (cong1 Snd rc) (axSnd n (ap2 Pair l r)))

lIdxOf : (input n l r : Term) ->
  Deriv (eqF (ap1 get_rc input) (ap2 Pair n (ap2 Pair l r))) ->
  Deriv (eqF (ap1 lIdx input) l)
lIdxOf input n l r rc =
  ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input)
    (ruleTrans (cong1 Fst (sndArgOf input n l r rc)) (axFst l r))

rIdxOf : (input n l r : Term) ->
  Deriv (eqF (ap1 get_rc input) (ap2 Pair n (ap2 Pair l r))) ->
  Deriv (eqF (ap1 rIdx input) r)
rIdxOf input n l r rc =
  ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input)
    (ruleTrans (cong1 Snd (sndArgOf input n l r rc)) (axSnd l r))

-- the two children are < node : both bounded by  P_outer .
leqChildL : (n l r P : Term) ->
  Deriv (leq (ap2 Pair n (ap2 Pair l r)) P) -> Deriv (leq l P)
leqChildL n l r P lbp =
  leq_trans l (ap2 Pair l r) P (leq_pi_left l r)
    (leq_trans (ap2 Pair l r) (ap2 Pair n (ap2 Pair l r)) P
       (leq_pi_right n (ap2 Pair l r)) lbp)

leqChildR : (n l r P : Term) ->
  Deriv (leq (ap2 Pair n (ap2 Pair l r)) P) -> Deriv (leq r P)
leqChildR n l r P lbp =
  leq_trans r (ap2 Pair l r) P (leq_pi_right l r)
    (leq_trans (ap2 Pair l r) (ap2 Pair n (ap2 Pair l r)) P
       (leq_pi_right n (ap2 Pair l r)) lbp)

-- the leaf-value  ze#F input = ze#  (shared by the pZe leaf and the roCell).
ze#F_at : (input : Term) -> Deriv (eqF (ap1 ze#F input) ze#)
ze#F_at input =
  ruleTrans (ax_C pi Z Z input)
    (ruleTrans (congL pi (ap1 Z input) (axZ input)) (congR pi O (axZ input)))

-- node-tag mismatch witness  (binTag = 2 != 1)  for collapse_snd.
w21 : NatNeqWitness 2 1
w21 = decideNatNeq 2 1 (\ ())

------------------------------------------------------------------------
-- SECTION 4.  Leaf equation:  srcF (derZe) = ze# .

srcF_derZe : Deriv (eqF (ap1 srcF derZe) ze#)
srcF_derZe =
  let open NP Z ze#F cellNode O dgZe
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (ze#F_at input_pkg)

------------------------------------------------------------------------
-- SECTION 5.  su equation:  srcF (derSu d) = su# (srcF d) .

srcF_derSu : (d : Term) -> Deriv (eqF (ap1 srcF (derSu d)) (su# (ap1 srcF d)))
srcF_derSu d =
  let payload : Term
      payload = ap2 Pair dgSu (ap2 Pair d filler)
      open NP Z ze#F cellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgSu)
      nieq = nIdxOf input_pkg dgSu d filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 srcF d))
      recL = np_lookup_gen lIdx d (lIdxOf input_pkg dgSu d filler np_rc)
               (leqChildL dgSu d filler P_outer leq_b_P)

      cell_fires : Deriv (eqF (ap1 cellNode input_pkg) (ap1 suCell input_pkg))
      cell_fires = fork_true_to_fst suCell restAd (testEq 1) input_pkg
                     (testEq_fire 1 input_pkg nieq)
      suCell_val : Deriv (eqF (ap1 suCell input_pkg) (su# (ap1 srcF d)))
      suCell_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt lIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) recL))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires suCell_val)

------------------------------------------------------------------------
-- SECTION 6.  ad equation:  srcF (derAd d1 d2) = ad# (srcF d1) (srcF d2) .

srcF_derAd : (d1 d2 : Term) ->
  Deriv (eqF (ap1 srcF (derAd d1 d2)) (ad# (ap1 srcF d1) (ap1 srcF d2)))
srcF_derAd d1 d2 =
  let payload : Term
      payload = ap2 Pair dgAd (ap2 Pair d1 d2)
      open NP Z ze#F cellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd d1 d2 np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 srcF d1))
      recL = np_lookup_gen lIdx d1 (lIdxOf input_pkg dgAd d1 d2 np_rc)
               (leqChildL dgAd d1 d2 P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 srcF d2))
      recR = np_lookup_gen rIdx d2 (rIdxOf input_pkg dgAd d1 d2 np_rc)
               (leqChildR dgAd d1 d2 P_outer leq_b_P)

      -- cellNode -> (skip su) restAd -> (fire ad) adCell.
      cell_fires : Deriv (eqF (ap1 cellNode input_pkg) (ap1 adCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAd (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCell restRO (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                             (ap2 pi (ap1 srcF d1) (ap1 srcF d2)))
      inner_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 srcF d1) recR))
      adCell_val : Deriv (eqF (ap1 adCell input_pkg) (ad# (ap1 srcF d1) (ap1 srcF d2)))
      adCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires adCell_val)

------------------------------------------------------------------------
-- SECTION 7.  rO equation:  srcF (derRO d) = ad# ze# (srcF d) .

w31 : NatNeqWitness 3 1
w31 = decideNatNeq 3 1 (\ ())
w32 : NatNeqWitness 3 2
w32 = decideNatNeq 3 2 (\ ())

srcF_derRO : (d : Term) ->
  Deriv (eqF (ap1 srcF (derRO d)) (ad# ze# (ap1 srcF d)))
srcF_derRO d =
  let payload : Term
      payload = ap2 Pair dgRO (ap2 Pair d filler)
      open NP Z ze#F cellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRO)
      nieq = nIdxOf input_pkg dgRO d filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 srcF d))
      recL = np_lookup_gen lIdx d (lIdxOf input_pkg dgRO d filler np_rc)
               (leqChildL dgRO d filler P_outer leq_b_P)

      -- cellNode -> (skip su) restAd -> (skip ad) restRO -> (fire ro) roCell.
      cell_fires : Deriv (eqF (ap1 cellNode input_pkg) (ap1 roCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAd (testEq 1) input_pkg
                     (testEq_skip 3 1 input_pkg w31 nieq))
          (ruleTrans (fork_false_to_snd adCell restRO (testEq 2) input_pkg
                        (testEq_skip 3 2 input_pkg w32 nieq))
                     (fork_true_to_fst roCell rsCell (testEq 3) input_pkg
                        (testEq_fire 3 input_pkg nieq)))
      inner_val : Deriv (eqF (ap1 (C pi ze#F (lookupAt lIdx)) input_pkg)
                             (ap2 pi ze# (ap1 srcF d)))
      inner_val =
        ruleTrans (ax_C pi ze#F (lookupAt lIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) input_pkg) (ze#F_at input_pkg))
                     (congR pi ze# recL))
      roCell_val : Deriv (eqF (ap1 roCell input_pkg) (ad# ze# (ap1 srcF d)))
      roCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi ze#F (lookupAt lIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi ze#F (lookupAt lIdx)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires roCell_val)

------------------------------------------------------------------------
-- SECTION 8.  rS equation:  srcF (derRS d1 d2) = ad# (su# (srcF d1)) (srcF d2) .

w41 : NatNeqWitness 4 1
w41 = decideNatNeq 4 1 (\ ())
w42 : NatNeqWitness 4 2
w42 = decideNatNeq 4 2 (\ ())
w43 : NatNeqWitness 4 3
w43 = decideNatNeq 4 3 (\ ())

srcF_derRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 srcF (derRS d1 d2)) (ad# (su# (ap1 srcF d1)) (ap1 srcF d2)))
srcF_derRS d1 d2 =
  let payload : Term
      payload = ap2 Pair dgRS (ap2 Pair d1 d2)
      open NP Z ze#F cellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRS)
      nieq = nIdxOf input_pkg dgRS d1 d2 np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 srcF d1))
      recL = np_lookup_gen lIdx d1 (lIdxOf input_pkg dgRS d1 d2 np_rc)
               (leqChildL dgRS d1 d2 P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 srcF d2))
      recR = np_lookup_gen rIdx d2 (rIdxOf input_pkg dgRS d1 d2 np_rc)
               (leqChildR dgRS d1 d2 P_outer leq_b_P)

      -- cellNode -> restAd -> restRO -> (skip ro) rsCell  (condFork_false).
      cell_fires : Deriv (eqF (ap1 cellNode input_pkg) (ap1 rsCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suCell restAd (testEq 1) input_pkg
                     (testEq_skip 4 1 input_pkg w41 nieq))
          (ruleTrans (fork_false_to_snd adCell restRO (testEq 2) input_pkg
                        (testEq_skip 4 2 input_pkg w42 nieq))
                     (fork_false_to_snd roCell rsCell (testEq 3) input_pkg
                        (testEq_skip 4 3 input_pkg w43 nieq)))
      left_val : Deriv (eqF (ap1 (C pi (constN 1) (lookupAt lIdx)) input_pkg)
                            (su# (ap1 srcF d1)))
      left_val =
        ruleTrans (ax_C pi (constN 1) (lookupAt lIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) recL))
      inner_val : Deriv (eqF (ap1 (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) input_pkg)
                             (ap2 pi (su# (ap1 srcF d1)) (ap1 srcF d2)))
      inner_val =
        ruleTrans (ax_C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) left_val)
                     (congR pi (su# (ap1 srcF d1)) recR))
      rsCell_val : Deriv (eqF (ap1 rsCell input_pkg) (ad# (su# (ap1 srcF d1)) (ap1 srcF d2)))
      rsCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (C pi (constN 1) (lookupAt lIdx)) (lookupAt rIdx)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires rsCell_val)
