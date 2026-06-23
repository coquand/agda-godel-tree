{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriSOpaque -- the OPAQUE triFSized equations: for an arbitrary code
-- p != O dispatched on dtag p (and, for Ad, on dtag (pL p)), triFSized p
-- reduces by the SAME cells as the built equations (T4.DerTriS), but unfolded
-- via the opaque harness (T4.OpaqueHarness, instantiated at triStep) and with
-- child recovery via lookup_op + the (sbf-independent) value bounds of
-- T4.WfRedExtract.  These drive the course-of-values triPresObjOpaque.
--
--   p!=O, dtag p=dgZe              => triFSized p = szDerZe
--   p!=O, dtag p=dgSu              => triFSized p = szDerSu (triFSized (pArg p))
--   p!=O, dtag p=dgRO              => triFSized p = triFSized (pArg p)
--   p!=O, dtag p=dgRS              => triFSized p = szDerSu (szDerAd (triFSized (pL p)) (triFSized (pR p)))
--
-- THIS FILE (part 1): the four non-Ad cases.  The Ad critical pairs follow.
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriSOpaque where

open import T4.Base

open import T4.DerCodeS
  using ( szDerZe ; szDerSu ; szDerAd ; szDerRO ; szDerRS ; dsize ; dtag ; pArg ; pL ; pR
        ; pArg_Su )
open import T4.DerCodeSFun
  using ( szDerSuF ; szDerROF ; szDerAdF ; szDerRSF
        ; szDerSuF_eq ; szDerROF_eq ; szDerAdF_eq ; szDerRSF_eq )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.DerTriS
  using ( triStep ; triFSized
        ; cellTriZe ; cellTriSu ; cellTriRO ; cellTriRS
        ; cellTriAdZe ; cellTriAdSu ; cellTriAdElse
        ; triRestSu ; triRestAd ; triRestRO ; triRestRS ; adCellTriS ; restAdNodeS
        ; testAdZeS ; testAdSuS ; adLeftTag ; pArgFn ; adLeftTagFrom
        ; testAdZeS_fire ; testAdZeS_skip ; testAdSuS_fire ; testAdSuS_skip
        ; cellTriZe_eq )
open import T4.WfRedSized using ( w10 ; w20 ; w30 ; w40 )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness )
open import T4.WfRedExtract using ( argValueBound ; pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 ; w41 ; w42 ; w43 )

open import BRA3.Church      using ( pi ; predecessor )
open import BRA3.PairAlgebra using ( compose1U_eq )

import T4.OpaqueHarness
open T4.OpaqueHarness.H triStep

------------------------------------------------------------------------
-- SECTION 1.  The four non-Ad opaque equations.

triFSized_op_Ze : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgZe) ->
  Deriv (eqF (ap1 triFSized p) szDerZe)
triFSized_op_Ze p ne htag =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgZe)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_fires : Deriv (eqF (ap1 triStep opk) (ap1 cellTriZe opk))
      cell_fires = fork_true_to_fst cellTriZe triRestSu (testEq 0) opk
                     (testEq_fire 0 opk nieq)
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires (cellTriZe_eq opk))

triFSized_op_Su : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (eqF (ap1 triFSized p) (szDerSu (ap1 triFSized (pArg p))))
triFSized_op_Su p ne htag =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgSu)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_fires : Deriv (eqF (ap1 triStep opk) (ap1 cellTriSu opk))
      cell_fires =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 1 0 opk w10 nieq))
                  (fork_true_to_fst cellTriSu triRestAd (testEq 1) opk
                     (testEq_fire 1 opk nieq))
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) opk) (ap1 triFSized (pArg p)))
      recArg = lookup_op Z triStep argIdx (ap1 predecessor p) (pArg p)
                 (op_argIdx p ne) (argValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriSu opk) (szDerSu (ap1 triFSized (pArg p))))
      cell_val =
        ruleTrans (compose1U_eq szDerSuF (lookupAt argIdx) opk)
          (ruleTrans (cong1 szDerSuF recArg) (szDerSuF_eq (ap1 triFSized (pArg p))))
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires cell_val)

triFSized_op_RO : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (eqF (ap1 triFSized p) (ap1 triFSized (pArg p)))
triFSized_op_RO p ne htag =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRO)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_fires : Deriv (eqF (ap1 triStep opk) (ap1 cellTriRO opk))
      cell_fires =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 3 0 opk w30 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) opk
                        (testEq_skip 3 1 opk w31 nieq))
            (ruleTrans (fork_false_to_snd adCellTriS triRestRO (testEq 2) opk
                          (testEq_skip 3 2 opk w32 nieq))
                       (fork_true_to_fst cellTriRO triRestRS (testEq 3) opk
                          (testEq_fire 3 opk nieq))))
      recArg : Deriv (eqF (ap1 (lookupAt argIdx) opk) (ap1 triFSized (pArg p)))
      recArg = lookup_op Z triStep argIdx (ap1 predecessor p) (pArg p)
                 (op_argIdx p ne) (argValueBound p ne)
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires recArg)

triFSized_op_RS : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (eqF (ap1 triFSized p)
             (szDerSu (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
triFSized_op_RS p ne htag =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgRS)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_fires : Deriv (eqF (ap1 triStep opk) (ap1 cellTriRS opk))
      cell_fires =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 4 0 opk w40 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) opk
                        (testEq_skip 4 1 opk w41 nieq))
            (ruleTrans (fork_false_to_snd adCellTriS triRestRO (testEq 2) opk
                          (testEq_skip 4 2 opk w42 nieq))
              (ruleTrans (fork_false_to_snd cellTriRO triRestRS (testEq 3) opk
                            (testEq_skip 4 3 opk w43 nieq))
                         (fork_true_to_fst cellTriRS cellTriZe (testEq 4) opk
                            (testEq_fire 4 opk nieq)))))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      innerAd : Deriv (eqF (ap1 (C szDerAdF (lookupAt lIdx) (lookupAt rIdx)) opk)
                           (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
      innerAd =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) opk) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized (pL p)) recR)
                       (szDerAdF_eq (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
      cell_val : Deriv (eqF (ap1 cellTriRS opk)
                            (szDerSu (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
      cell_val =
        ruleTrans (compose1U_eq szDerSuF (C szDerAdF (lookupAt lIdx) (lookupAt rIdx)) opk)
          (ruleTrans (cong1 szDerSuF innerAd)
                     (szDerSuF_eq (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
  in ruleTrans (opUnfold p ne) (ruleTrans cell_fires cell_val)

------------------------------------------------------------------------
-- SECTION 2.  The Ad opaque critical pairs.
-- Shared: opk, dtag p = dgAd, cascade to adCellTriS (tag 2), child recovery.

triFSized_op_Ad_Ze : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (dtag p) dgAd) -> Deriv (eqF (dtag (pL p)) dgZe) ->
  Deriv (eqF (ap1 triFSized p) (szDerRO (ap1 triFSized (pR p))))
triFSized_op_Ad_Ze p ne htag htagL =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_to_ad : Deriv (eqF (ap1 triStep opk) (ap1 adCellTriS opk))
      cell_to_ad =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 2 0 opk w20 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) opk
                        (testEq_skip 2 1 opk w21 nieq))
                     (fork_true_to_fst adCellTriS triRestRO (testEq 2) opk
                        (testEq_fire 2 opk nieq)))
      adLeft : Deriv (eqF (ap1 adLeftTag opk) (natCode 0))
      adLeft = ruleTrans (adLeftTagFrom opk (pL p) (op_pL p ne)) htagL
      ad_fires : Deriv (eqF (ap1 adCellTriS opk) (ap1 cellTriAdZe opk))
      ad_fires = fork_true_to_fst cellTriAdZe restAdNodeS testAdZeS opk
                   (testAdZeS_fire opk adLeft)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriAdZe opk) (szDerRO (ap1 triFSized (pR p))))
      cell_val =
        ruleTrans (compose1U_eq szDerROF (lookupAt rIdx) opk)
          (ruleTrans (cong1 szDerROF recR) (szDerROF_eq (ap1 triFSized (pR p))))
  in ruleTrans (opUnfold p ne)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))

triFSized_op_Ad_Su : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (dtag p) dgAd) ->
  Deriv (neg (eqF (pL p) O)) -> Deriv (eqF (dtag (pL p)) dgSu) ->
  Deriv (eqF (ap1 triFSized p)
             (szDerRS (ap1 triFSized (pArg (pL p))) (ap1 triFSized (pR p))))
triFSized_op_Ad_Su p ne htag neL htagL =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_to_ad : Deriv (eqF (ap1 triStep opk) (ap1 adCellTriS opk))
      cell_to_ad =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 2 0 opk w20 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) opk
                        (testEq_skip 2 1 opk w21 nieq))
                     (fork_true_to_fst adCellTriS triRestRO (testEq 2) opk
                        (testEq_fire 2 opk nieq)))
      adLeft : Deriv (eqF (ap1 adLeftTag opk) (natCode 1))
      adLeft = ruleTrans (adLeftTagFrom opk (pL p) (op_pL p ne)) htagL
      ad_fires : Deriv (eqF (ap1 adCellTriS opk) (ap1 cellTriAdSu opk))
      ad_fires =
        ruleTrans (fork_false_to_snd cellTriAdZe restAdNodeS testAdZeS opk
                     (testAdZeS_skip 1 opk w10 adLeft))
                  (fork_true_to_fst cellTriAdSu cellTriAdElse testAdSuS opk
                     (testAdSuS_fire opk adLeft))
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      -- recL, then the OPAQUE Su equation on the (opaque) left child.
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recL_su : Deriv (eqF (ap1 (lookupAt lIdx) opk)
                           (szDerSu (ap1 triFSized (pArg (pL p)))))
      recL_su = ruleTrans recL (triFSized_op_Su (pL p) neL htagL)
      leftRec : Deriv (eqF (ap1 (compose1U pArgFn (lookupAt lIdx)) opk)
                           (ap1 triFSized (pArg (pL p))))
      leftRec =
        ruleTrans (compose1U_eq pArgFn (lookupAt lIdx) opk)
          (ruleTrans (cong1 pArgFn recL_su)
            (ruleTrans (compose1U_eq Snd Snd (szDerSu (ap1 triFSized (pArg (pL p)))))
                       (pArg_Su (ap1 triFSized (pArg (pL p))))))
      cell_val : Deriv (eqF (ap1 cellTriAdSu opk)
                            (szDerRS (ap1 triFSized (pArg (pL p))) (ap1 triFSized (pR p))))
      cell_val =
        ruleTrans (ax_C szDerRSF (compose1U pArgFn (lookupAt lIdx)) (lookupAt rIdx) opk)
          (ruleTrans (congL szDerRSF (ap1 (lookupAt rIdx) opk) leftRec)
            (ruleTrans (congR szDerRSF (ap1 triFSized (pArg (pL p))) recR)
                       (szDerRSF_eq (ap1 triFSized (pArg (pL p))) (ap1 triFSized (pR p)))))
  in ruleTrans (opUnfold p ne)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))

triFSized_op_Ad_else : (p : Term) (m : Nat) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (dtag p) dgAd) ->
  NatNeqWitness m 0 -> NatNeqWitness m 1 ->
  Deriv (eqF (dtag (pL p)) (natCode m)) ->
  Deriv (eqF (ap1 triFSized p)
             (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
triFSized_op_Ad_else p m ne htag w0 w1 htagL =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_to_ad : Deriv (eqF (ap1 triStep opk) (ap1 adCellTriS opk))
      cell_to_ad =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 2 0 opk w20 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) opk
                        (testEq_skip 2 1 opk w21 nieq))
                     (fork_true_to_fst adCellTriS triRestRO (testEq 2) opk
                        (testEq_fire 2 opk nieq)))
      adLeft : Deriv (eqF (ap1 adLeftTag opk) (natCode m))
      adLeft = ruleTrans (adLeftTagFrom opk (pL p) (op_pL p ne)) htagL
      ad_fires : Deriv (eqF (ap1 adCellTriS opk) (ap1 cellTriAdElse opk))
      ad_fires =
        ruleTrans (fork_false_to_snd cellTriAdZe restAdNodeS testAdZeS opk
                     (testAdZeS_skip m opk w0 adLeft))
                  (fork_false_to_snd cellTriAdSu cellTriAdElse testAdSuS opk
                     (testAdSuS_skip m opk w1 adLeft))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriAdElse opk)
                            (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
      cell_val =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) opk) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized (pL p)) recR)
                       (szDerAdF_eq (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
  in ruleTrans (opUnfold p ne)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))
