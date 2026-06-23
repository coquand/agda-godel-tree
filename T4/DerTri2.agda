{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTri2 -- PART 2 of the object triangle map: the  dAd  critical-pair
-- cases of  triF  (T4.DerTri), the depth-2 dispatch on the left child a.
--
--   triF (derAd derZe q)        = derRO (triF q)                       (a leaf)
--   triF (derAd (derSu p) q)    = derRS (triF p) (triF q)              (a = dSu)
--   triF (derAd (derAd p1 p2) q)= derAd (triF (derAd p1 p2)) (triF q)  (a = dAd)
--   triF (derAd (derRO p) q)    = derAd (triF (derRO p)) (triF q)      (a = dRO)
--   triF (derAd (derRS p1 p2) q)= derAd (triF (derRS p1 p2)) (triF q)  (a = dRS)
--
-- The cascade to the  dAd  cell (label 2) reuses DerSrc; inside the cell the
-- dispatch is on the left child: leaf -> derRO; deriv-label 1 (dSu) -> derRS
-- with  derL (triF (derSu p)) = triF p  recovered from the dSu equation; else
-- -> derAd.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTri2 where

open import T4.Base

open import T4.DerCode
  using ( derZe ; derSu ; derAd ; derRO ; derRS
        ; dgZe ; dgSu ; dgAd ; dgRO ; dgRS ; filler ; derChildL_Su )
open import T4.BinTree
  using ( binLeaf ; binNode ; nIdx ; lIdx ; rIdx
        ; binTag_leaf ; binTag_node ; binLab )
open import T4.ParsObj using ( foldOf ; test1 ; module NP )
open import T4.FoldRec using ( lookupAt )

open import T4.DerTri
  using ( triF ; triF_derSu
        ; cellLeafTri ; cellLeafTri_at
        ; suNodeCell ; roNodeCell ; rsNodeCell
        ; adCellTri ; restNodeAd ; restROTri ; restAdTri ; cellNodeTri
        ; adZeBranch ; adSuBranch ; adElseBranch
        ; tagAidx ; labAidx ; testLeafA ; testSuA ; derLF )

open import T4.DerSrc
  using ( testEq
        ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; nIdxOf ; lIdxOf ; rIdxOf ; leqChildL ; leqChildR
        ; w21 ; w31 ; w41 )

open import BRA3.Church       using ( pi )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq )

------------------------------------------------------------------------
-- SECTION 1.  Local helpers: the inner-dispatch tests and  derLF  unfolding.

testLeafA_fire : (input : Term) ->
  Deriv (eqF (ap1 tagAidx input) (natCode 1)) ->
  Deriv (eqF (ap1 testLeafA input) (ap1 s O))
testLeafA_fire input heq =
  ruleTrans (ax_C natEqF tagAidx (constN 1) input)
    (ruleTrans (congL natEqF (ap1 (constN 1) input) heq)
      (ruleTrans (congR natEqF (natCode 1) (constN_eq 1 input)) (natEq_eq 1)))

testLeafA_skip : (m : Nat) (input : Term) -> NatNeqWitness m 1 ->
  Deriv (eqF (ap1 tagAidx input) (natCode m)) ->
  Deriv (eqF (ap1 testLeafA input) O)
testLeafA_skip m input w heq =
  ruleTrans (ax_C natEqF tagAidx (constN 1) input)
    (ruleTrans (congL natEqF (ap1 (constN 1) input) heq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq 1 input)) (natEqF_at_neq m 1 w)))

testSuA_fire : (input : Term) ->
  Deriv (eqF (ap1 labAidx input) (natCode 1)) ->
  Deriv (eqF (ap1 testSuA input) (ap1 s O))
testSuA_fire input heq =
  ruleTrans (ax_C natEqF labAidx (constN 1) input)
    (ruleTrans (congL natEqF (ap1 (constN 1) input) heq)
      (ruleTrans (congR natEqF (natCode 1) (constN_eq 1 input)) (natEq_eq 1)))

testSuA_skip : (m : Nat) (input : Term) -> NatNeqWitness m 1 ->
  Deriv (eqF (ap1 labAidx input) (natCode m)) ->
  Deriv (eqF (ap1 testSuA input) O)
testSuA_skip m input w heq =
  ruleTrans (ax_C natEqF labAidx (constN 1) input)
    (ruleTrans (congL natEqF (ap1 (constN 1) input) heq)
      (ruleTrans (congR natEqF (natCode m) (constN_eq 1 input)) (natEqF_at_neq m 1 w)))

-- derLF z = Fst (Snd (Snd z))  (unfold the compose1U).
derLF_eq : (z : Term) -> Deriv (eqF (ap1 derLF z) (ap1 Fst (ap1 Snd (ap1 Snd z))))
derLF_eq z =
  ruleTrans (compose1U_eq Fst (compose1U Snd Snd) z)
            (cong1 Fst (compose1U_eq Snd Snd z))

------------------------------------------------------------------------
-- SECTION 2.  Shared sub-derivations, parameterised by  input  and the
-- explicit-payload data, packaged in a local module per case.

-- the else-branch value  adElseBranch input = derAd ta tq .
adElse_val : (input ta tq : Term) ->
  Deriv (eqF (ap1 (lookupAt lIdx) input) ta) ->
  Deriv (eqF (ap1 (lookupAt rIdx) input) tq) ->
  Deriv (eqF (ap1 adElseBranch input) (derAd ta tq))
adElse_val input ta tq recA recR =
  ruleTrans (ax_C pi (constN 2) (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input)
    (ruleTrans (congL pi (ap1 (C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx))) input)
                   (constN_eq 2 input))
      (congR pi (natCode 2)
        (ruleTrans (ax_C pi (constN 2) (C pi (lookupAt lIdx) (lookupAt rIdx)) input)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt lIdx) (lookupAt rIdx)) input)
                         (constN_eq 2 input))
            (congR pi (natCode 2)
              (ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input)
                (ruleTrans (congL pi (ap1 (lookupAt rIdx) input) recA)
                           (congR pi ta recR))))))))

------------------------------------------------------------------------
-- SECTION 3.  rO critical pair:  triF (derAd derZe q) = derRO (triF q) .

triF_derAd_Ze : (q : Term) ->
  Deriv (eqF (ap1 triF (derAd derZe q)) (derRO (ap1 triF q)))
triF_derAd_Ze q =
  let payload : Term
      payload = ap2 Pair dgAd (ap2 Pair derZe q)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd derZe q np_rc
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) derZe)
      lIdx_eq = lIdxOf input_pkg dgAd derZe q np_rc
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 triF q))
      recR = np_lookup_gen rIdx q (rIdxOf input_pkg dgAd derZe q np_rc)
               (leqChildR dgAd derZe q P_outer leq_b_P)

      cell_to_ad : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 adCellTri input_pkg))
      cell_to_ad =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCellTri restROTri (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      -- a = derZe is a leaf : tagAidx = binTag derZe = 1.
      tagA_eq : Deriv (eqF (ap1 tagAidx input_pkg) (natCode 1))
      tagA_eq = ruleTrans (compose1U_eq Fst lIdx input_pkg)
                  (ruleTrans (cong1 Fst lIdx_eq) (binTag_leaf dgZe))
      ad_fires : Deriv (eqF (ap1 adCellTri input_pkg) (ap1 adZeBranch input_pkg))
      ad_fires = fork_true_to_fst adZeBranch restNodeAd testLeafA input_pkg
                   (testLeafA_fire input_pkg tagA_eq)
      -- adZeBranch = derRO (triF q).
      inner_val : Deriv (eqF (ap1 (C pi (lookupAt rIdx) cellLeafTri) input_pkg)
                             (ap2 pi (ap1 triF q) filler))
      inner_val =
        ruleTrans (ax_C pi (lookupAt rIdx) cellLeafTri input_pkg)
          (ruleTrans (congL pi (ap1 cellLeafTri input_pkg) recR)
                     (congR pi (ap1 triF q) (cellLeafTri_at input_pkg)))
      mid_val : Deriv (eqF (ap1 (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) input_pkg)
                           (ap2 pi dgRO (ap2 pi (ap1 triF q) filler)))
      mid_val =
        ruleTrans (ax_C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt rIdx) cellLeafTri) input_pkg)
                         (constN_eq 3 input_pkg))
                     (congR pi (natCode 3) inner_val))
      adZe_val : Deriv (eqF (ap1 adZeBranch input_pkg) (derRO (ap1 triF q)))
      adZe_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 3) (C pi (lookupAt rIdx) cellLeafTri)) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) mid_val))
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans cell_to_ad (ruleTrans ad_fires adZe_val))

------------------------------------------------------------------------
-- SECTION 4.  rS critical pair:  triF (derAd (derSu p) q) = derRS (triF p) (triF q) .

triF_derAd_Su : (p q : Term) ->
  Deriv (eqF (ap1 triF (derAd (derSu p) q)) (derRS (ap1 triF p) (ap1 triF q)))
triF_derAd_Su p q =
  let payload : Term
      payload = ap2 Pair dgAd (ap2 Pair (derSu p) q)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd (derSu p) q np_rc
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) (derSu p))
      lIdx_eq = lIdxOf input_pkg dgAd (derSu p) q np_rc
      recA : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF (derSu p)))
      recA = np_lookup_gen lIdx (derSu p) lIdx_eq
               (leqChildL dgAd (derSu p) q P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 triF q))
      recR = np_lookup_gen rIdx q (rIdxOf input_pkg dgAd (derSu p) q np_rc)
               (leqChildR dgAd (derSu p) q P_outer leq_b_P)

      cell_to_ad : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 adCellTri input_pkg))
      cell_to_ad =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCellTri restROTri (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      -- a = derSu p : not a leaf (tagAidx = 2), deriv-label = 1.
      tagA_eq : Deriv (eqF (ap1 tagAidx input_pkg) (natCode 2))
      tagA_eq = ruleTrans (compose1U_eq Fst lIdx input_pkg)
                  (ruleTrans (cong1 Fst lIdx_eq) (binTag_node dgSu p filler))
      labA_eq : Deriv (eqF (ap1 labAidx input_pkg) (natCode 1))
      labA_eq = ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) input_pkg)
                  (ruleTrans (cong1 Fst (compose1U_eq Snd lIdx input_pkg))
                    (ruleTrans (cong1 Fst (cong1 Snd lIdx_eq)) (binLab dgSu p filler)))
      ad_fires : Deriv (eqF (ap1 adCellTri input_pkg) (ap1 adSuBranch input_pkg))
      ad_fires =
        ruleTrans (fork_false_to_snd adZeBranch restNodeAd testLeafA input_pkg
                     (testLeafA_skip 2 input_pkg w21 tagA_eq))
                  (fork_true_to_fst adSuBranch adElseBranch testSuA input_pkg
                     (testSuA_fire input_pkg labA_eq))
      -- derL (triF (derSu p)) = triF p  (from the dSu equation + derChildL_Su).
      dL_eq : Deriv (eqF (ap1 (compose1U derLF (lookupAt lIdx)) input_pkg) (ap1 triF p))
      dL_eq =
        ruleTrans (compose1U_eq derLF (lookupAt lIdx) input_pkg)
          (ruleTrans (cong1 derLF recA)
            (ruleTrans (cong1 derLF (triF_derSu p))
              (ruleTrans (derLF_eq (derSu (ap1 triF p))) (derChildL_Su (ap1 triF p)))))
      inner_val : Deriv (eqF (ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) input_pkg)
                             (ap2 pi (ap1 triF p) (ap1 triF q)))
      inner_val =
        ruleTrans (ax_C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) dL_eq)
                     (congR pi (ap1 triF p) recR))
      mid_val : Deriv (eqF (ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) input_pkg)
                           (ap2 pi dgRS (ap2 pi (ap1 triF p) (ap1 triF q))))
      mid_val =
        ruleTrans (ax_C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx)) input_pkg)
                         (constN_eq 4 input_pkg))
                     (congR pi (natCode 4) inner_val))
      adSu_val : Deriv (eqF (ap1 adSuBranch input_pkg) (derRS (ap1 triF p) (ap1 triF q)))
      adSu_val =
        ruleTrans (ax_C pi (constN 2) (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (constN 4) (C pi (compose1U derLF (lookupAt lIdx)) (lookupAt rIdx))) input_pkg)
                         (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) mid_val))
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans cell_to_ad (ruleTrans ad_fires adSu_val))

------------------------------------------------------------------------
-- SECTION 5.  No-root-redex critical pairs:  a in {dAd, dRO, dRS} .
-- All three collapse to  derAd (triF a) (triF q)  via  adElse_val .

-- a = derAd p1 p2  (deriv-label 2).
triF_derAd_Ad : (p1 p2 q : Term) ->
  Deriv (eqF (ap1 triF (derAd (derAd p1 p2) q))
             (derAd (ap1 triF (derAd p1 p2)) (ap1 triF q)))
triF_derAd_Ad p1 p2 q =
  let a : Term
      a = derAd p1 p2
      payload : Term
      payload = ap2 Pair dgAd (ap2 Pair a q)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd a q np_rc
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) a)
      lIdx_eq = lIdxOf input_pkg dgAd a q np_rc
      recA : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF a))
      recA = np_lookup_gen lIdx a lIdx_eq (leqChildL dgAd a q P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 triF q))
      recR = np_lookup_gen rIdx q (rIdxOf input_pkg dgAd a q np_rc)
               (leqChildR dgAd a q P_outer leq_b_P)
      cell_to_ad : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 adCellTri input_pkg))
      cell_to_ad =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCellTri restROTri (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      tagA_eq : Deriv (eqF (ap1 tagAidx input_pkg) (natCode 2))
      tagA_eq = ruleTrans (compose1U_eq Fst lIdx input_pkg)
                  (ruleTrans (cong1 Fst lIdx_eq) (binTag_node dgAd p1 p2))
      labA_eq : Deriv (eqF (ap1 labAidx input_pkg) (natCode 2))
      labA_eq = ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) input_pkg)
                  (ruleTrans (cong1 Fst (compose1U_eq Snd lIdx input_pkg))
                    (ruleTrans (cong1 Fst (cong1 Snd lIdx_eq)) (binLab dgAd p1 p2)))
      ad_fires : Deriv (eqF (ap1 adCellTri input_pkg) (ap1 adElseBranch input_pkg))
      ad_fires =
        ruleTrans (fork_false_to_snd adZeBranch restNodeAd testLeafA input_pkg
                     (testLeafA_skip 2 input_pkg w21 tagA_eq))
                  (fork_false_to_snd adSuBranch adElseBranch testSuA input_pkg
                     (testSuA_skip 2 input_pkg w21 labA_eq))
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans cell_to_ad (ruleTrans ad_fires
         (adElse_val input_pkg (ap1 triF a) (ap1 triF q) recA recR)))

-- a = derRO p  (deriv-label 3).
triF_derAd_RO : (p q : Term) ->
  Deriv (eqF (ap1 triF (derAd (derRO p) q))
             (derAd (ap1 triF (derRO p)) (ap1 triF q)))
triF_derAd_RO p q =
  let a : Term
      a = derRO p
      payload : Term
      payload = ap2 Pair dgAd (ap2 Pair a q)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd a q np_rc
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) a)
      lIdx_eq = lIdxOf input_pkg dgAd a q np_rc
      recA : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF a))
      recA = np_lookup_gen lIdx a lIdx_eq (leqChildL dgAd a q P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 triF q))
      recR = np_lookup_gen rIdx q (rIdxOf input_pkg dgAd a q np_rc)
               (leqChildR dgAd a q P_outer leq_b_P)
      cell_to_ad : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 adCellTri input_pkg))
      cell_to_ad =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCellTri restROTri (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      tagA_eq : Deriv (eqF (ap1 tagAidx input_pkg) (natCode 2))
      tagA_eq = ruleTrans (compose1U_eq Fst lIdx input_pkg)
                  (ruleTrans (cong1 Fst lIdx_eq) (binTag_node dgRO p filler))
      labA_eq : Deriv (eqF (ap1 labAidx input_pkg) (natCode 3))
      labA_eq = ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) input_pkg)
                  (ruleTrans (cong1 Fst (compose1U_eq Snd lIdx input_pkg))
                    (ruleTrans (cong1 Fst (cong1 Snd lIdx_eq)) (binLab dgRO p filler)))
      ad_fires : Deriv (eqF (ap1 adCellTri input_pkg) (ap1 adElseBranch input_pkg))
      ad_fires =
        ruleTrans (fork_false_to_snd adZeBranch restNodeAd testLeafA input_pkg
                     (testLeafA_skip 2 input_pkg w21 tagA_eq))
                  (fork_false_to_snd adSuBranch adElseBranch testSuA input_pkg
                     (testSuA_skip 3 input_pkg w31 labA_eq))
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans cell_to_ad (ruleTrans ad_fires
         (adElse_val input_pkg (ap1 triF a) (ap1 triF q) recA recR)))

-- a = derRS p1 p2  (deriv-label 4).
triF_derAd_RS : (p1 p2 q : Term) ->
  Deriv (eqF (ap1 triF (derAd (derRS p1 p2) q))
             (derAd (ap1 triF (derRS p1 p2)) (ap1 triF q)))
triF_derAd_RS p1 p2 q =
  let a : Term
      a = derRS p1 p2
      payload : Term
      payload = ap2 Pair dgAd (ap2 Pair a q)
      open NP Z cellLeafTri cellNodeTri (natCode 1) payload
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      nieq : Deriv (eqF (ap1 nIdx input_pkg) dgAd)
      nieq = nIdxOf input_pkg dgAd a q np_rc
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) a)
      lIdx_eq = lIdxOf input_pkg dgAd a q np_rc
      recA : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 triF a))
      recA = np_lookup_gen lIdx a lIdx_eq (leqChildL dgAd a q P_outer leq_b_P)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 triF q))
      recR = np_lookup_gen rIdx q (rIdxOf input_pkg dgAd a q np_rc)
               (leqChildR dgAd a q P_outer leq_b_P)
      cell_to_ad : Deriv (eqF (ap1 cellNodeTri input_pkg) (ap1 adCellTri input_pkg))
      cell_to_ad =
        ruleTrans (fork_false_to_snd suNodeCell restAdTri (testEq 1) input_pkg
                     (testEq_skip 2 1 input_pkg w21 nieq))
                  (fork_true_to_fst adCellTri restROTri (testEq 2) input_pkg
                     (testEq_fire 2 input_pkg nieq))
      tagA_eq : Deriv (eqF (ap1 tagAidx input_pkg) (natCode 2))
      tagA_eq = ruleTrans (compose1U_eq Fst lIdx input_pkg)
                  (ruleTrans (cong1 Fst lIdx_eq) (binTag_node dgRS p1 p2))
      labA_eq : Deriv (eqF (ap1 labAidx input_pkg) (natCode 4))
      labA_eq = ruleTrans (compose1U_eq Fst (compose1U Snd lIdx) input_pkg)
                  (ruleTrans (cong1 Fst (compose1U_eq Snd lIdx input_pkg))
                    (ruleTrans (cong1 Fst (cong1 Snd lIdx_eq)) (binLab dgRS p1 p2)))
      ad_fires : Deriv (eqF (ap1 adCellTri input_pkg) (ap1 adElseBranch input_pkg))
      ad_fires =
        ruleTrans (fork_false_to_snd adZeBranch restNodeAd testLeafA input_pkg
                     (testLeafA_skip 2 input_pkg w21 tagA_eq))
                  (fork_false_to_snd adSuBranch adElseBranch testSuA input_pkg
                     (testSuA_skip 4 input_pkg w41 labA_eq))
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans cell_to_ad (ruleTrans ad_fires
         (adElse_val input_pkg (ap1 triF a) (ap1 triF q) recA recR)))
