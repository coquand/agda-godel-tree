{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriUDispatch -- the object tag dispatch for the unsized bundled CR step:
--   triUStep : imp PhiKU (qcheckU sK = O)              (sK = s (var 0))
-- Outer caseElim on the leaf marker (Fst sK = natCode 1): leaf = glue_Ze; node =
-- a 4-way caseElim on dtag sK (Su / Ad / RO / RS) gluing the per-tag glues, with
-- the junk-tag branch closed by validity (wfRed_op_reject_gam contradicts
-- wfRed sK = O).  Then PA is reassembled from PhiKU + validity and qcheckU_complete
-- closes it.  Ports T4.TriPresDispatch to the unsized leaf/node coding.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriUDispatch where

open import T4.Base

open import T4.DerCodeS using ( dtag )
open import T4.DerCode using ( dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRed using ( wfRed )
open import T4.QCheckU using ( conj3 ; qcheckU ; qcheckU_complete )
open import T4.QCheckProjU using ( PhiKU )

open import T4.TriUGlue
  using ( sK ; bigK ; Aform ; PA ; Bgoal ; negLeaf ; Hleaf ; ne_sK
        ; glue_Su ; glue_RO ; glue_RS ; glue_Ze )
open import T4.TriUGlueAd using ( glue_Ad )

open import T4.CRGlueImpU using ( sigmaBothO_imp )
open import T4.DerUOpaqueGam using ( wfRed_op_reject_gam )
open import T4.NatEqReflect using ( natEqF_complete )
open import T4.DescSndImp using ( neSucc )

open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.ChurchCM using ( caseElim )
open import T4.CountingObj using ( swapImp )
open import BRA3.Logic using ( eqSymImp )
open import BRA3.Contrapositive using ( compI ; liftP ; identP ; axExFalso )
open import T4.GammaCtx
  using ( Cnj ; cnjL ; cnjR ; cnjPair ; cnjCurry ; gWeak ; gMp ; gApply ; gTrans )

------------------------------------------------------------------------

private
  hSu hAd hRO hRS : Formula
  hSu = eqF (dtag sK) dgSu
  hAd = eqF (dtag sK) dgAd
  hRO = eqF (dtag sK) dgRO
  hRS = eqF (dtag sK) dgRS

  -- node context  GN = negLeaf /\ PA .
  GN : Formula
  GN = Cnj negLeaf PA

  pNL : Deriv (imp GN negLeaf)
  pNL = cnjL negLeaf PA
  pPAg : Deriv (imp GN PA)
  pPAg = cnjR negLeaf PA

  -- per-tag core over  Cnj GN htagX  (apply the glue to negLeaf, htagX, PA).
  tagCore : (htagX : Formula) ->
    Deriv (imp negLeaf (imp htagX (imp PA Bgoal))) -> Deriv (imp (Cnj GN htagX) Bgoal)
  tagCore htagX glueX =
    let K : Formula
        K = Cnj GN htagX
        gNL : Deriv (imp K negLeaf)
        gNL = compI (cnjL GN htagX) pNL
        gPA : Deriv (imp K PA)
        gPA = compI (cnjL GN htagX) pPAg
        gHX : Deriv (imp K htagX)
        gHX = cnjR GN htagX
    in gMp (gMp (gMp (gWeak K glueX) gNL) gHX) gPA

  -- reassociate a core over  Cnj GN TA  to  Cnj BigCtx TA  (BigCtx -> GN).
  reassocTo : (BigCtx TA : Formula) -> Deriv (imp BigCtx GN) ->
    Deriv (imp (Cnj GN TA) Bgoal) -> Deriv (imp (Cnj BigCtx TA) Bgoal)
  reassocTo BigCtx TA projGN core =
    compI (gMp (gApply (cnjPair GN TA) (compI (cnjL BigCtx TA) projGN)) (cnjR BigCtx TA)) core

  -- the junk-tag reject:  validity (wfRed sK = O) vs  wfRed sK = s O .
  rejCore : Deriv (imp (Cnj (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) (neg hRS)) Bgoal)
  rejCore =
    let K : Formula
        K = Cnj (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) (neg hRS)
        c321 : Deriv (imp K (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)))
        c321 = cnjL (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) (neg hRS)
        c32 : Deriv (imp K (Cnj (Cnj GN (neg hSu)) (neg hAd)))
        c32 = compI c321 (cnjL (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO))
        c3 : Deriv (imp K (Cnj GN (neg hSu)))
        c3 = compI c32 (cnjL (Cnj GN (neg hSu)) (neg hAd))
        gGN : Deriv (imp K GN)
        gGN = compI c3 (cnjL GN (neg hSu))
        gnSu : Deriv (imp K (neg hSu))
        gnSu = compI c3 (cnjR GN (neg hSu))
        gnAd : Deriv (imp K (neg hAd))
        gnAd = compI c32 (cnjR (Cnj GN (neg hSu)) (neg hAd))
        gnRO : Deriv (imp K (neg hRO))
        gnRO = compI c321 (cnjR (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO))
        gnRS : Deriv (imp K (neg hRS))
        gnRS = cnjR (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) (neg hRS)
        gNL : Deriv (imp K negLeaf)
        gNL = compI gGN pNL
        gNl : Deriv (imp K (eqF (ap2 natEqF (ap1 Fst sK) (natCode 1)) O))
        gNl = compI gNL (natEqF_complete (ap1 Fst sK) (natCode 1))
        gA : Deriv (imp K (eqF (ap1 wfRed sK) O))
        gA = compI (compI gGN pPAg)
               (T4.TriUGlue.pa2a)
        wfReject : Deriv (imp K (eqF (ap1 wfRed sK) (ap1 s O)))
        wfReject = wfRed_op_reject_gam K sK (gWeak K ne_sK) gNl gnSu gnAd gnRO gnRS
        soO : Deriv (imp K (eqF (ap1 s O) O))
        soO = gTrans (ap1 s O) (ap1 wfRed sK) O
                (gApply (eqSymImp (ap1 wfRed sK) (ap1 s O)) wfReject) gA
    in gMp (gApply (axExFalso (eqF (ap1 s O) O) Bgoal) soO) (gWeak K (neSucc O))

  -- fold the 4-way + reject into  imp GN Bgoal .
  e3 : Deriv (imp (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) Bgoal)
  e3 = caseElim {X = hRS} {Y = neg hRS}
         {Rf = imp (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) Bgoal}
         (identP (neg hRS))
         (swapImp (cnjCurry (reassocTo (Cnj (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO)) hRS
                    (compI (cnjL (Cnj (Cnj GN (neg hSu)) (neg hAd)) (neg hRO))
                       (compI (cnjL (Cnj GN (neg hSu)) (neg hAd)) (cnjL GN (neg hSu))))
                    (tagCore hRS glue_RS))))
         (swapImp (cnjCurry rejCore))
  e2 : Deriv (imp (Cnj (Cnj GN (neg hSu)) (neg hAd)) Bgoal)
  e2 = caseElim {X = hRO} {Y = neg hRO}
         {Rf = imp (Cnj (Cnj GN (neg hSu)) (neg hAd)) Bgoal}
         (identP (neg hRO))
         (swapImp (cnjCurry (reassocTo (Cnj (Cnj GN (neg hSu)) (neg hAd)) hRO
                    (compI (cnjL (Cnj GN (neg hSu)) (neg hAd)) (cnjL GN (neg hSu)))
                    (tagCore hRO glue_RO))))
         (swapImp (cnjCurry e3))
  e1 : Deriv (imp (Cnj GN (neg hSu)) Bgoal)
  e1 = caseElim {X = hAd} {Y = neg hAd} {Rf = imp (Cnj GN (neg hSu)) Bgoal}
         (identP (neg hAd))
         (swapImp (cnjCurry (reassocTo (Cnj GN (neg hSu)) hAd (cnjL GN (neg hSu))
                    (tagCore hAd glue_Ad))))
         (swapImp (cnjCurry e2))
  coreN : Deriv (imp GN Bgoal)
  coreN = caseElim {X = hSu} {Y = neg hSu} {Rf = imp GN Bgoal}
            (identP (neg hSu))
            (swapImp (cnjCurry (tagCore hSu glue_Su)))
            (swapImp (cnjCurry e1))

  -- node dispatch : imp negLeaf (imp PA Bgoal) .
  nodeDisp : Deriv (imp negLeaf (imp PA Bgoal))
  nodeDisp = cnjCurry coreN

  -- the full dispatch :  imp PA Bgoal  (leaf vs node).
  glueAll : Deriv (imp PA Bgoal)
  glueAll = caseElim {X = Hleaf} {Y = negLeaf} {Rf = imp PA Bgoal}
              (identP negLeaf) glue_Ze nodeDisp

------------------------------------------------------------------------
-- Convert  imp PA Bgoal  ->  imp PhiKU (qcheckU sK = O) .

triUStep : Deriv (imp PhiKU (eqF (ap1 qcheckU sK) O))
triUStep =
  let gPA : Deriv (imp (Cnj PhiKU Aform) PA)
      gPA = gMp (gApply (sigmaBothO_imp bigK (ap1 wfRed sK)) (cnjL PhiKU Aform))
                (cnjR PhiKU Aform)
      qStep : Deriv (imp PhiKU (imp Aform (eqF (ap1 conj3 sK) O)))
      qStep = cnjCurry (compI gPA glueAll)
  in compI qStep (qcheckU_complete sK)
