{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRed -- the OBJECT STRICT VALIDITY predicate  wfRed : Fun1  for coded
-- parallel-reduction DERIVATIONS, over ARBITRARY codes  p : Term  (NOT the DerM
-- shadow).  This is the tag-pinning validity the weak  isCert  lacked, and the
-- prerequisite for the arbitrary-code course-of-values lift of Theorem A
-- (the genuine CR-in-BRA step,  triPresObjOpaque ).
--
--   wfRed (derZe)        = O                              (a leaf is valid)
--   wfRed (derSu d)      = wfRed d
--   wfRed (derAd d1 d2)  = pi (wfRed d1) (wfRed d2)
--   wfRed (derRO d)      = wfRed d
--   wfRed (derRS d1 d2)  = pi (wfRed d1) (wfRed d2)
--   wfRed (node, label not in 1..4) = s O                 (REJECT -- strictness)
--
-- The node cell dispatches on the derivation label (nIdx) with the DerSrc
-- cascade, BUT with a final  reject  default (constN 1 = s O), so an invalid tag
-- is NOT silently accepted -- this is what lets the opaque cov-dispatch be total
-- (other tags excluded by  wfRed p = O ).  The cells are just the recursive
-- validity lookups (lookupAt lIdx / rIdx), no term-building.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRed where

open import T4.Base

open import T4.DerCode
  using ( derZe ; derSu ; derAd ; derRO ; derRS
        ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS ; filler )
open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.FoldRec using ( lookupAt )

open import T4.DerSrc
  using ( testEq
        ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; nIdxOf ; lIdxOf ; rIdxOf ; leqChildL ; leqChildR
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church       using ( pi )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq )

------------------------------------------------------------------------
-- SECTION 1.  Cells and the strict cascade.

wfAdCell : Fun1                                       -- pi (wfRed l) (wfRed r)
wfAdCell = C pi (lookupAt lIdx) (lookupAt rIdx)

rejectCell : Fun1                                      -- s O  (invalid tag)
rejectCell = constN 1

-- label 4 (dRS) -> wfAdCell ; else -> reject.
wfRestRS : Fun1
wfRestRS = C condFork (C pi wfAdCell rejectCell) (testEq 4)
-- label 3 (dRO) -> wfRed l ; else -> wfRestRS.
wfRestRO : Fun1
wfRestRO = C condFork (C pi (lookupAt lIdx) wfRestRS) (testEq 3)
-- label 2 (dAd) -> wfAdCell ; else -> wfRestRO.
wfRestAd : Fun1
wfRestAd = C condFork (C pi wfAdCell wfRestRO) (testEq 2)
-- label 1 (dSu) -> wfRed l ; else -> wfRestAd.
wfCellNode : Fun1
wfCellNode = C condFork (C pi (lookupAt lIdx) wfRestAd) (testEq 1)

-- The fold BASE is  rejectCell (= s O) , NOT  Z : so  wfRed O = s O , i.e.  O
-- is NOT a valid derivation.  This propagates: ANY code with an  O  subterm gets
-- wfRed /= O  (a child lookup of  O  reads the base  s O ), so  wfRed p = O
-- forces  p  to be a GENUINE derivation tree -- every node non-O with a valid
-- tag and recursively-valid non-O children, exactly the  codeDer  structure.
-- (The leaf cell stays  Z , so a genuine leaf  derZe  is still valid.)
wfRed : Fun1
wfRed = binRec rejectCell Z wfCellNode

------------------------------------------------------------------------
-- SECTION 2.  Leaf:  wfRed (derZe) = O .

wfRed_derZe : Deriv (eqF (ap1 wfRed derZe) O)
wfRed_derZe =
  let open NP rejectCell Z wfCellNode O dgZe
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (axZ input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  dSu:  wfRed (derSu d) = wfRed d .

wfRed_derSu : (d : Term) -> Deriv (eqF (ap1 wfRed (derSu d)) (ap1 wfRed d))
wfRed_derSu d =
  let payload : Term
      payload = ap2 Pair dgSu (ap2 Pair d filler)
      open NP rejectCell Z wfCellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgSu)
      nieq = nIdxOf input_pkg dgSu d filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 wfRed d))
      recL = np_lookup_gen lIdx d (lIdxOf input_pkg dgSu d filler np_rc)
               (leqChildL dgSu d filler P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 wfCellNode input_pkg) (ap1 (lookupAt lIdx) input_pkg))
      cell_fires = fork_true_to_fst (lookupAt lIdx) wfRestAd (testEq 1) input_pkg
                     (testEq_fire 1 input_pkg nieq)
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires recL)

------------------------------------------------------------------------
-- SECTION 4.  dAd:  wfRed (derAd d1 d2) = pi (wfRed d1) (wfRed d2) .

wfRed_derAd : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRed (derAd d1 d2)) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
wfRed_derAd d1 d2 =
  let payload : Term
      payload = ap2 Pair dgAd (ap2 Pair d1 d2)
      open NP rejectCell Z wfCellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd d1 d2 np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 wfRed d1))
      recL = np_lookup_gen lIdx d1 (lIdxOf input_pkg dgAd d1 d2 np_rc)
               (leqChildL dgAd d1 d2 P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 wfRed d2))
      recR = np_lookup_gen rIdx d2 (rIdxOf input_pkg dgAd d1 d2 np_rc)
               (leqChildR dgAd d1 d2 P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 wfCellNode input_pkg) (ap1 wfAdCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst wfAdCell wfRestRO (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      ad_val : Deriv (eqF (ap1 wfAdCell input_pkg) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
      ad_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 wfRed d1) recR))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires ad_val)

------------------------------------------------------------------------
-- SECTION 5.  dRO:  wfRed (derRO d) = wfRed d .

wfRed_derRO : (d : Term) -> Deriv (eqF (ap1 wfRed (derRO d)) (ap1 wfRed d))
wfRed_derRO d =
  let payload : Term
      payload = ap2 Pair dgRO (ap2 Pair d filler)
      open NP rejectCell Z wfCellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRO)
      nieq = nIdxOf input_pkg dgRO d filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 wfRed d))
      recL = np_lookup_gen lIdx d (lIdxOf input_pkg dgRO d filler np_rc)
               (leqChildL dgRO d filler P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 wfCellNode input_pkg) (ap1 (lookupAt lIdx) input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) input_pkg
                     (testEq_skip 3 1 input_pkg w31 nieq))
          (ruleTrans (fork_false_to_snd wfAdCell wfRestRO (testEq 2) input_pkg
                        (testEq_skip 3 2 input_pkg w32 nieq))
                     (fork_true_to_fst (lookupAt lIdx) wfRestRS (testEq 3) input_pkg
                        (testEq_fire 3 input_pkg nieq)))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires recL)

------------------------------------------------------------------------
-- SECTION 6.  dRS:  wfRed (derRS d1 d2) = pi (wfRed d1) (wfRed d2) .

wfRed_derRS : (d1 d2 : Term) ->
  Deriv (eqF (ap1 wfRed (derRS d1 d2)) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
wfRed_derRS d1 d2 =
  let payload : Term
      payload = ap2 Pair dgRS (ap2 Pair d1 d2)
      open NP rejectCell Z wfCellNode (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRS)
      nieq = nIdxOf input_pkg dgRS d1 d2 np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 wfRed d1))
      recL = np_lookup_gen lIdx d1 (lIdxOf input_pkg dgRS d1 d2 np_rc)
               (leqChildL dgRS d1 d2 P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 wfRed d2))
      recR = np_lookup_gen rIdx d2 (rIdxOf input_pkg dgRS d1 d2 np_rc)
               (leqChildR dgRS d1 d2 P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 wfCellNode input_pkg) (ap1 wfAdCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestAd (testEq 1) input_pkg
                     (testEq_skip 4 1 input_pkg w41 nieq))
          (ruleTrans (fork_false_to_snd wfAdCell wfRestRO (testEq 2) input_pkg
                        (testEq_skip 4 2 input_pkg w42 nieq))
            (ruleTrans (fork_false_to_snd (lookupAt lIdx) wfRestRS (testEq 3) input_pkg
                          (testEq_skip 4 3 input_pkg w43 nieq))
                       (fork_true_to_fst wfAdCell rejectCell (testEq 4) input_pkg
                          (testEq_fire 4 input_pkg nieq))))
      ad_val : Deriv (eqF (ap1 wfAdCell input_pkg) (ap2 pi (ap1 wfRed d1) (ap1 wfRed d2)))
      ad_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 wfRed d1) recR))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires ad_val)
