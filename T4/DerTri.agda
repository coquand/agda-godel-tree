{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTri -- the OBJECT TRIANGLE MAP  triF : Fun1  over the DerCode derivation
-- coding: a primitive-recursive  binRec  fold that BUILDS new derivation codes,
-- transcribing T4.ChurchRosserProto.tri / T4.ObjCR.tri clause-for-clause.  This
-- is the last fold of Theorem A's infrastructure (T4/CON-T0-ARCHITECTURE.md).
--
--   triF (derZe)              = derZe
--   triF (derSu p)            = derSu (triF p)
--   triF (derAd derZe q)      = derRO (triF q)
--   triF (derAd (derSu p) q)  = derRS (derL (triF (derSu p))) (triF q)   (= derRS (triF p) (triF q))
--   triF (derAd (derAd ..) q) = derAd (triF (derAd ..)) (triF q)
--   triF (derAd (derRO p) q)  = derAd (triF (derRO p)) (triF q)
--   triF (derAd (derRS ..) q) = derAd (triF (derRS ..)) (triF q)
--   triF (derRO p)            = triF p
--   triF (derRS p q)          = derSu (derAd (triF p) (triF q))
--
-- The node cell reuses the DerSrc 4-way label cascade; the  dAd  branch
-- (label 2) sub-dispatches on the LEFT child a (leaf=derRO, dSu=derRS via
-- derL recovery, else=derAd) -- the depth-2 critical-pair dispatch.
--
-- This file (PART 1) defines all cells + triF and proves the four non-dAd
-- equations (derZe, derSu, derRO, derRS).  The dAd cases follow in DerTri2.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTri where

open import T4.Base

open import T4.DerCode
  using ( derZe ; derSu ; derAd ; derRO ; derRS
        ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS ; filler )
open import T4.BinTree using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.FoldRec using ( lookupAt )
open import T4.LeqMono using ( leq_trans )

open import T4.DerSrc
  using ( testEq
        ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; nIdxOf ; lIdxOf ; rIdxOf ; leqChildL ; leqChildR
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq )

------------------------------------------------------------------------
-- SECTION 1.  The cells.

-- pZe -> derZe  (= filler = binLeaf dgZe = pi (natCode 1) (natCode 0)).
cellLeafTri : Fun1
cellLeafTri = C pi (constN 1) (constN 0)

-- dSu -> derSu (triF p) = binNode dgSu (triF p) filler.
suNodeCell : Fun1
suNodeCell = C pi (constN 2) (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri))

-- dRO -> triF p  (just the left recursion value).
roNodeCell : Fun1
roNodeCell = lookupAt lIdx

-- dRS -> derSu (derAd (triF p) (triF q)).
adExprRS : Fun1                                        -- derAd (triF p) (triF q)
adExprRS = C pi (constN 2) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)))
rsNodeCell : Fun1
rsNodeCell = C pi (constN 2) (C pi (constN 1) (C pi adExprRS cellLeafTri))

------------------------------------------------------------------------
-- SECTION 2.  The dAd branch (depth-2 dispatch on the left child a).

derLF : Fun1                                           -- derL z = Fst (Snd (Snd z))
derLF = compose1U Fst (compose1U Snd Snd)

tagAidx : Fun1                                         -- binTag a = Fst a
tagAidx = compose1U Fst lIdx
labAidx : Fun1                                         -- derLab a = Fst (Snd a)
labAidx = compose1U Fst (compose1U Snd lIdx)

testLeafA : Fun1                                       -- a is a leaf (binTag a = 1) ?
testLeafA = C natEqF tagAidx (constN 1)
testSuA : Fun1                                         -- a's deriv-label = 1 (dSu) ?
testSuA = C natEqF labAidx (constN 1)

adZeBranch : Fun1                                      -- derRO (triF q)
adZeBranch = C pi (constN 2) (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri))
adSuBranch : Fun1                                      -- derRS (derL (triF a)) (triF q)
adSuBranch = C pi (constN 2) (C pi (constN 4)
               (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)))
adElseBranch : Fun1                                    -- derAd (triF a) (triF q)
adElseBranch = C pi (constN 2) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)))

restNodeAd : Fun1
restNodeAd = C condFork (C pi adSuBranch adElseBranch) testSuA
adCellTri : Fun1
adCellTri = C condFork (C pi adZeBranch restNodeAd) testLeafA

------------------------------------------------------------------------
-- SECTION 3.  The 4-way label cascade and  triF .

restROTri : Fun1
restROTri = C condFork (C pi roNodeCell rsNodeCell) (testEq 3)
restAdTri : Fun1
restAdTri = C condFork (C pi adCellTri restROTri) (testEq 2)
cellNodeTri : Fun1
cellNodeTri = C condFork (C pi suNodeCell restAdTri) (testEq 1)

triF : Fun1
triF = binRec Z cellLeafTri cellNodeTri

------------------------------------------------------------------------
-- SECTION 4.  cellLeafTri input = filler (= derZe), shared.

cellLeafTri_at : (input : Term) -> Deriv (eqF (ap1 cellLeafTri input) filler)
cellLeafTri_at input =
  ruleTrans (ax_C pi (constN 1) (constN 0) input)
    (ruleTrans (congL pi (ap1 (constN 0) input) (constN_eq 1 input))
               (congR pi (natCode 1) (constN_eq 0 input)))

------------------------------------------------------------------------
-- SECTION 5.  pZe:  triF (derZe) = derZe .

triF_derZe : Deriv (eqF (ap1 triF derZe) derZe)
triF_derZe =
  let open NP Z cellLeafTri cellNodeTri O dgZe
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (cellLeafTri_at input_pkg)

------------------------------------------------------------------------
-- SECTION 6.  dSu:  triF (derSu p) = derSu (triF p) .

triF_derSu : (p : Term) -> Deriv (eqF (ap1 triF (derSu p)) (derSu (ap1 triF p)))
triF_derSu p =
  let payload : Term
      payload = ap2 Pair dgSu (ap2 Pair p filler)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgSu)
      nieq = nIdxOf input_pkg dgSu p filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF p))
      recL = np_lookup_gen lIdx p (lIdxOf input_pkg dgSu p filler np_rc)
               (leqChildL dgSu p filler P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 suNodeCell input_pkg))
      cell_fires = fork_true_to_fst suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_fire 1 input_pkg nieq)
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) cellLeafTri) input_pkg)
                             (ap2 pi (ap1 triF p) filler))
      inner_val =
        ruleTrans (ax_C pi (lookupAt lIdx) cellLeafTri input_pkg)
          (ruleTrans (congL pi (ap1 cellLeafTri input_pkg) recL)
                     (congR pi (ap1 triF p) (cellLeafTri_at input_pkg)))
      mid_val : Deriv (eqF (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) input_pkg)
                           (ap2 pi dgSu (ap2 pi (ap1 triF p) filler)))
      mid_val =
        ruleTrans (ax_C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) cellLeafTri) input_pkg)
                         (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) inner_val))
      suNodeCell_val : Deriv (eqF (ap1 suNodeCell input_pkg) (derSu (ap1 triF p)))
      suNodeCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 1) (C pi (lookupAt lIdx) cellLeafTri)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) mid_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires suNodeCell_val)

------------------------------------------------------------------------
-- SECTION 7.  dRO:  triF (derRO p) = triF p .

triF_derRO : (p : Term) -> Deriv (eqF (ap1 triF (derRO p)) (ap1 triF p))
triF_derRO p =
  let payload : Term
      payload = ap2 Pair dgRO (ap2 Pair p filler)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRO)
      nieq = nIdxOf input_pkg dgRO p filler np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF p))
      recL = np_lookup_gen lIdx p (lIdxOf input_pkg dgRO p filler np_rc)
               (leqChildL dgRO p filler P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 roNodeCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 3 1 input_pkg w31 nieq))
          (ruleTrans (fork_false_to_snd adCellTri restROTri (testEq 2) input_pkg
                        (testEq_skip 3 2 input_pkg w32 nieq))
                     (fork_true_to_fst roNodeCell rsNodeCell (testEq 3) input_pkg
                        (testEq_fire 3 input_pkg nieq)))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires recL)

------------------------------------------------------------------------
-- SECTION 8.  dRS:  triF (derRS p q) = derSu (derAd (triF p) (triF q)) .

triF_derRS : (p q : Term) ->
  Deriv (eqF (ap1 triF (derRS p q)) (derSu (derAd (ap1 triF p) (ap1 triF q))))
triF_derRS p q =
  let payload : Term
      payload = ap2 Pair dgRS (ap2 Pair p q)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgRS)
      nieq = nIdxOf input_pkg dgRS p q np_rc
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF p))
      recL = np_lookup_gen lIdx p (lIdxOf input_pkg dgRS p q np_rc)
               (leqChildL dgRS p q P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 triF q))
      recR = np_lookup_gen rIdx q (rIdxOf input_pkg dgRS p q np_rc)
               (leqChildR dgRS p q P_outer leq_b_P)
      cell_fires : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 rsNodeCell input_pkg))
      cell_fires =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 4 1 input_pkg w41 nieq))
          (ruleTrans (fork_false_to_snd adCellTri restROTri (testEq 2) input_pkg
                        (testEq_skip 4 2 input_pkg w42 nieq))
                     (fork_false_to_snd roNodeCell rsNodeCell (testEq 3) input_pkg
                        (testEq_skip 4 3 input_pkg w43 nieq)))
      innerAd_val : Deriv (eqF (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                               (ap2 pi (ap1 triF p) (ap1 triF q)))
      innerAd_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 triF p) recR))
      midAd_val : Deriv (eqF (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input_pkg)
                             (ap2 pi dgAd (ap2 pi (ap1 triF p) (ap1 triF q))))
      midAd_val =
        ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) innerAd_val))
      adExprRS_val : Deriv (eqF (ap1 adExprRS input_pkg)
                               (derAd (ap1 triF p) (ap1 triF q)))
      adExprRS_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) midAd_val))
      innerRS_val : Deriv (eqF (ap1 (C pi adExprRS cellLeafTri) input_pkg)
                               (ap2 pi (derAd (ap1 triF p) (ap1 triF q)) filler))
      innerRS_val =
        ruleTrans (ax_C pi adExprRS cellLeafTri input_pkg)
          (ruleTrans (congL pi (ap1 cellLeafTri input_pkg) adExprRS_val)
                     (congR pi (derAd (ap1 triF p) (ap1 triF q)) (cellLeafTri_at input_pkg)))
      midRS_val : Deriv (eqF (ap1 (C pi (constN 1) (C pi adExprRS cellLeafTri)) input_pkg)
                             (ap2 pi dgSu (ap2 pi (derAd (ap1 triF p) (ap1 triF q)) filler)))
      midRS_val =
        ruleTrans (ax_C pi (constN 1) (C pi adExprRS cellLeafTri) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi adExprRS cellLeafTri) input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) innerRS_val))
      rsNodeCell_val : Deriv (eqF (ap1 rsNodeCell input_pkg)
                             (derSu (derAd (ap1 triF p) (ap1 triF q))))
      rsNodeCell_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 1) (C pi adExprRS cellLeafTri)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 1) (C pi adExprRS cellLeafTri)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) midRS_val))
  in ruleTrans (collapse_snd t1_O) (ruleTrans cell_fires rsNodeCell_val)
