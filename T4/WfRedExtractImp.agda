{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedExtractImp -- the IMP-FORM (Carneiro) child extractions:
--
--   imp (wfRedSized d = O) (wfRedSized child = O)
--
-- carrying the validity of d as the antecedent (NOT a bare meta Deriv), so the
-- internal course-of-values step (covFuel, T4.TriPresObjOpaque) can thread it
-- through with compI / sigma_both_zero_imp.  Same opaque harness + lookup as
-- T4.WfRedExtract, but the hypothesis is consumed by prependEqLeft instead of mp.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedExtractImp where

open import T4.Base

open import T4.DerCodeS using ( dtag ; pArg ; pL ; pR )
open import T4.DerCode  using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfStep ; unaryCell ; binaryCell ; chkU ; chkB ; argIdx
        ; wfRestSu ; wfRestAd ; wfRestRO ; wfRestRS ; w10 ; w30 )
open import T4.WfRedExtract
  using ( opkg ; opUnfold ; op_nIdx ; op_argIdx ; op_pL ; op_pR
        ; binCellAd ; binCellRS ; argValueBound ; pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 ; w31 ; w32 )

open import BRA3.Church      using ( sigma ; predecessor )
open import T4.SigmaZeroN    using ( sigmaZeroL ; sigmaZeroR )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.Contrapositive using ( compI )

------------------------------------------------------------------------
-- SECTION 1.  Unary cell child extraction (imp-form), given the cascade.

childU_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p))) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pArg p)) O))
childU_imp p ne cf =
  let opk : Term
      opk = opkg p
      lookupT : Term
      lookupT = ap1 (lookupAt argIdx) opk
      UE : Deriv (eqF (ap1 wfRedSized p) (ap2 sigma (ap1 chkU opk) lookupT))
      UE = ruleTrans (opUnfold p ne)
             (ruleTrans cf (ax_C sigma chkU (lookupAt argIdx) opk))
      e1 : Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap2 sigma (ap1 chkU opk) lookupT) O))
      e1 = prependEqLeft (ap2 sigma (ap1 chkU opk) lookupT) (ap1 wfRedSized p) O (ruleSym UE)
      e2 : Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF lookupT O))
      e2 = compI e1 (sigmaZeroR (ap1 chkU opk) lookupT)
      recArg : Deriv (eqF lookupT (ap1 wfRedSized (pArg p)))
      recArg = lookup_op Z wfStep argIdx (ap1 predecessor p) (pArg p)
                 (op_argIdx p ne) (argValueBound p ne)
  in compI e2 (prependEqLeft (ap1 wfRedSized (pArg p)) lookupT O (ruleSym recArg))

------------------------------------------------------------------------
-- SECTION 2.  Binary cell: inner sigma, then left / right extraction.

binInnerSig_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O)
             (eqF (ap2 sigma (ap1 (lookupAt lIdx) (opkg p)) (ap1 (lookupAt rIdx) (opkg p))) O))
binInnerSig_imp p ne cf =
  let opk : Term
      opk = opkg p
      innerT : Term
      innerT = ap1 (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk
      sigLR : Term
      sigLR = ap2 sigma (ap1 (lookupAt lIdx) opk) (ap1 (lookupAt rIdx) opk)
      UE : Deriv (eqF (ap1 wfRedSized p) (ap2 sigma (ap1 chkB opk) innerT))
      UE = ruleTrans (opUnfold p ne)
             (ruleTrans cf (ax_C sigma chkB (C sigma (lookupAt lIdx) (lookupAt rIdx)) opk))
      e1 : Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap2 sigma (ap1 chkB opk) innerT) O))
      e1 = prependEqLeft (ap2 sigma (ap1 chkB opk) innerT) (ap1 wfRedSized p) O (ruleSym UE)
      e2 : Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF innerT O))
      e2 = compI e1 (sigmaZeroR (ap1 chkB opk) innerT)
  in compI e2 (prependEqLeft sigLR innerT O
                 (ruleSym (ax_C sigma (lookupAt lIdx) (lookupAt rIdx) opk)))

binChildL_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pL p)) O))
binChildL_imp p ne cf =
  let opk : Term
      opk = opkg p
      lookupL : Term
      lookupL = ap1 (lookupAt lIdx) opk
      eL : Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF lookupL O))
      eL = compI (binInnerSig_imp p ne cf)
             (sigmaZeroL lookupL (ap1 (lookupAt rIdx) opk))
      recL : Deriv (eqF lookupL (ap1 wfRedSized (pL p)))
      recL = lookup_op Z wfStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
  in compI eL (prependEqLeft (ap1 wfRedSized (pL p)) lookupL O (ruleSym recL))

binChildR_imp : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (ap1 wfStep (opkg p)) (ap1 binaryCell (opkg p))) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pR p)) O))
binChildR_imp p ne cf =
  let opk : Term
      opk = opkg p
      lookupR : Term
      lookupR = ap1 (lookupAt rIdx) opk
      eR : Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF lookupR O))
      eR = compI (binInnerSig_imp p ne cf)
             (sigmaZeroR (ap1 (lookupAt lIdx) opk) lookupR)
      recR : Deriv (eqF lookupR (ap1 wfRedSized (pR p)))
      recR = lookup_op Z wfStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
  in compI eR (prependEqLeft (ap1 wfRedSized (pR p)) lookupR O (ruleSym recR))

------------------------------------------------------------------------
-- SECTION 3.  The unary tag cascades (Su / RO) and the tag-keyed extractions.

private
  cascadeSu : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgSu) ->
    Deriv (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p)))
  cascadeSu p ne htag =
    let opk = opkg p
        nieq = ruleTrans (op_nIdx p ne) htag
    in ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                    (testEq_skip 1 0 opk w10 nieq))
                 (fork_true_to_fst unaryCell wfRestAd (testEq 1) opk
                    (testEq_fire 1 opk nieq))

  cascadeRO : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRO) ->
    Deriv (eqF (ap1 wfStep (opkg p)) (ap1 unaryCell (opkg p)))
  cascadeRO p ne htag =
    let opk = opkg p
        nieq = ruleTrans (op_nIdx p ne) htag
    in ruleTrans (fork_false_to_snd Z wfRestSu (testEq 0) opk
                    (testEq_skip 3 0 opk w30 nieq))
         (ruleTrans (fork_false_to_snd unaryCell wfRestAd (testEq 1) opk
                       (testEq_skip 3 1 opk w31 nieq))
           (ruleTrans (fork_false_to_snd binaryCell wfRestRO (testEq 2) opk
                         (testEq_skip 3 2 opk w32 nieq))
                      (fork_true_to_fst unaryCell wfRestRS (testEq 3) opk
                         (testEq_fire 3 opk nieq))))

extractChild_Su_imp : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgSu) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pArg p)) O))
extractChild_Su_imp p ne htag = childU_imp p ne (cascadeSu p ne htag)

extractChild_RO_imp : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRO) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pArg p)) O))
extractChild_RO_imp p ne htag = childU_imp p ne (cascadeRO p ne htag)

-- binary (Ad / RS), both children, via the shared bare cascades binCellAd/binCellRS.
extractChild_Ad_L_imp : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pL p)) O))
extractChild_Ad_L_imp p ne htag = binChildL_imp p ne (binCellAd p ne htag)

extractChild_Ad_R_imp : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgAd) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pR p)) O))
extractChild_Ad_R_imp p ne htag = binChildR_imp p ne (binCellAd p ne htag)

extractChild_RS_L_imp : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pL p)) O))
extractChild_RS_L_imp p ne htag = binChildL_imp p ne (binCellRS p ne htag)

extractChild_RS_R_imp : (p : Term) -> Deriv (neg (eqF p O)) -> Deriv (eqF (dtag p) dgRS) ->
  Deriv (imp (eqF (ap1 wfRedSized p) O) (eqF (ap1 wfRedSized (pR p)) O))
extractChild_RS_R_imp p ne htag = binChildR_imp p ne (binCellRS p ne htag)
