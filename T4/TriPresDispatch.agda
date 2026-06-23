{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriPresDispatch -- the object 5-way tag dispatch assembling the per-tag
-- glues (T4.TriPresGlue, T4.TriPresGlueAd) and the reject leaf (T4.TriPresReject)
-- into the step result of the bounded-conjunction induction:
--
--   triPresStep : imp PhiK (qcheck sK = O)            (sK = s (var 0))
--
-- Nested plain caseElim on  dtag sK = dgZe .. dgRS ; the X-branch is the glue
-- (with accumulated tag-negations pushed inside), the innermost else is the
-- reject.  Then PA is reassembled from PhiK + validity (sigBoth_ctx) and
-- qcheck_complete closes it.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriPresDispatch where

open import T4.Base

open import T4.DerCodeS using ( dtag )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized using ( wfRedSized )
open import T4.QCheck using ( qcheck ; qcheck_complete )
open import T4.QCheckProj using ( PhiK )

open import T4.TriPresGlue
  using ( sK ; bigK ; Aform ; PA ; Bform ; ne_sK ; glue_Ze ; glue_Su ; glue_RO ; glue_RS )
open import T4.TriPresGlueAd using ( glue_Ad )
open import T4.TriPresReject using ( rejectLeaf )

open import T4.WfRedBuildCtx using ( sigBoth_ctx )
open import BRA3.ChurchCM using ( caseElim )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.CtxKit using ( lift2 ; get2a ; get2b ; ap2c )

------------------------------------------------------------------------

private
  X0 : Formula
  X0 = eqF (dtag sK) dgZe
  X1 : Formula
  X1 = eqF (dtag sK) dgSu
  X2 : Formula
  X2 = eqF (dtag sK) dgAd
  X3 : Formula
  X3 = eqF (dtag sK) dgRO
  X4 : Formula
  X4 = eqF (dtag sK) dgRS

  Rf : Formula
  Rf = imp PA Bform

  -- glueAll : the 5-way dispatch result  imp PA Bform .
  glueAll : Deriv Rf
  glueAll =
    let -- accumulated-negation pushers:  imp Rf (negs.. (imp PA Bform)) .
        m2 : Deriv (imp Rf (imp (neg X1) (imp (neg X0) Rf)))
        m2 = compI (axK Rf (neg X0)) (axK (imp (neg X0) Rf) (neg X1))
        m3 : Deriv (imp Rf (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf))))
        m3 = compI m2 (axK (imp (neg X1) (imp (neg X0) Rf)) (neg X2))
        m4 : Deriv (imp Rf (imp (neg X3) (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf)))))
        m4 = compI m3 (axK (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf))) (neg X3))
        g1 : Deriv (imp X1 (imp (neg X0) Rf))
        g1 = compI glue_Su (axK Rf (neg X0))
        g2 : Deriv (imp X2 (imp (neg X1) (imp (neg X0) Rf)))
        g2 = compI glue_Ad m2
        g3 : Deriv (imp X3 (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf))))
        g3 = compI glue_RO m3
        g4 : Deriv (imp X4 (imp (neg X3) (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf)))))
        g4 = compI glue_RS m4
        e4 : Deriv (imp (neg X4) (imp (neg X3) (imp (neg X2)
               (imp (neg X1) (imp (neg X0) Rf)))))
        e4 = rejectLeaf sK bigK ne_sK
        e3 : Deriv (imp (neg X3) (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf))))
        e3 = caseElim {X = X4} {Y = neg X4}
               {Rf = imp (neg X3) (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf)))}
               (identP (neg X4)) g4 e4
        e2 : Deriv (imp (neg X2) (imp (neg X1) (imp (neg X0) Rf)))
        e2 = caseElim {X = X3} {Y = neg X3}
               {Rf = imp (neg X2) (imp (neg X1) (imp (neg X0) Rf))}
               (identP (neg X3)) g3 e3
        e1 : Deriv (imp (neg X1) (imp (neg X0) Rf))
        e1 = caseElim {X = X2} {Y = neg X2}
               {Rf = imp (neg X1) (imp (neg X0) Rf)}
               (identP (neg X2)) g2 e2
        e0 : Deriv (imp (neg X0) Rf)
        e0 = caseElim {X = X1} {Y = neg X1} {Rf = imp (neg X0) Rf}
               (identP (neg X1)) g1 e1
    in caseElim {X = X0} {Y = neg X0} {Rf = Rf}
         (identP (neg X0)) glue_Ze e0

------------------------------------------------------------------------
-- Convert  imp PA Bform  ->  imp PhiK (qcheck sK = O) .

triPresStep : Deriv (imp PhiK (eqF (ap1 qcheck sK) O))
triPresStep =
  let paFromBoth : Deriv (imp PhiK (imp Aform PA))
      paFromBoth = sigBoth_ctx PhiK Aform bigK (ap1 wfRedSized sK)
                     (get2a PhiK Aform) (get2b PhiK Aform)
      qStep : Deriv (imp PhiK (imp Aform Bform))
      qStep = ap2c (lift2 PhiK Aform glueAll) paFromBoth
  in compI qStep (qcheck_complete sK)
