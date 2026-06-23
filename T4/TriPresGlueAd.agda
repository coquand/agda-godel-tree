{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriPresGlueAd -- the Ad-tag GLUE of the object tag dispatch: a 3-way
-- sub-dispatch on dtag (pL sK) (Ze / Su / else), under the standing context
-- [H = (dtag sK = dgAd), PA] via caseElimUnderTwo.  The Su sub-case unfolds the
-- OPAQUE left child (grandchild validity via extractChild_Su_himp + the ne-form
-- Ad_Su opaque eq).  Result:  imp H (imp PA Bform) .
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriPresGlueAd where

open import T4.Base

open import T4.DerCodeS using ( szDerRO ; szDerAd ; szDerRS ; dtag ; pArg ; pL ; pR )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd )
open import T4.WfRedSized using ( wfRedSized )
open import T4.DerTriS using ( triFSized )

open import T4.WfRedExtractHtag using ( extractChild_Ad_L_H ; extractChild_Ad_R_H )
open import T4.WfRedExtractSuHtag using ( extractChild_Su_himp )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.WfRedBuildCtx using ( build_RO_ctx ; build_Ad_ctx )
open import T4.WfRedBuildCtxN using ( build_RS_ctx4 )
open import T4.DerTriSOpaqueAdImp using ( triFSized_op_Ad_Ze_imp ; triFSized_op_Ad_else_imp )
open import T4.DerTriSOpaqueAdSuImp using ( triFSized_op_Ad_Su_imp )
open import T4.QCheckProj using ( QofChild )

open import T4.TriPresGlue
  using ( sK ; Aform ; PA ; Bform ; ne_sK ; pa2a ; pa2phik ; triFvalidChild ; rebound )

open import T4.SndDescent using ( sndLe )
open import T4.LeqMono using ( leq_trans )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.ChurchStrictTrich using ( caseElimUnderTwo )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )
open import T4.CtxKit
  using ( lift2 ; ap2c ; lift3 ; get3a ; get3b ; get3c ; ap3c ; trans3c
        ; lift4 ; get4a ; get4b ; get4c ; get4d ; ap4c ; trans4c )

------------------------------------------------------------------------

H : Formula
H = eqF (dtag sK) dgAd

Y0 : Formula
Y0 = eqF (dtag (pL sK)) dgZe

Y1 : Formula
Y1 = eqF (dtag (pL sK)) dgSu

private
  wfTri : Term -> Term
  wfTri t = ap1 wfRedSized (ap1 triFSized t)

  -- pR validity (under [H,PA]), reused by Ze/Su/else.
  tvR : Deriv (imp H (imp PA (eqF (wfTri (pR sK)) O)))
  tvR = triFvalidChild H (pR sK) (extractChild_Ad_R_H sK ne_sK)
          (rebound (pR sK) (pRValueBound sK ne_sK))

------------------------------------------------------------------------
-- Ad_Ze :  cell = szDerRO (triFSized (pR sK)) .  Context [H,PA,Y0].

adZe : Deriv (imp H (imp PA (imp Y0 Bform)))
adZe =
  let cell : Term
      cell = szDerRO (ap1 triFSized (pR sK))
      opE : Deriv (imp H (imp Y0 (eqF (ap1 triFSized sK) cell)))
      opE = triFSized_op_Ad_Ze_imp sK ne_sK
      EΩ : Deriv (imp H (imp PA (imp Y0 (eqF (ap1 triFSized sK) cell))))
      EΩ = ap3c (ap3c (lift3 H PA Y0 opE) (get3a H PA Y0)) (get3c H PA Y0)
      opRw : Deriv (imp H (imp PA (imp Y0
               (eqF (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized cell)))))
      opRw = ap3c (lift3 H PA Y0 (ax_eqCong1 wfRedSized (ap1 triFSized sK) cell)) EΩ
      bld : Deriv (imp H (imp PA (eqF (ap1 wfRedSized cell) O)))
      bld = build_RO_ctx H PA (ap1 triFSized (pR sK)) tvR
      bldΩ : Deriv (imp H (imp PA (imp Y0 (eqF (ap1 wfRedSized cell) O))))
      bldΩ = ap3c (ap3c (lift3 H PA Y0 bld) (get3a H PA Y0)) (get3b H PA Y0)
  in trans3c (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized cell) O opRw bldΩ

------------------------------------------------------------------------
-- Ad_else :  cell = szDerAd (triFSized (pL sK)) (triFSized (pR sK)) .
-- Context [H,PA,nY1,nY0].

adElse : Deriv (imp H (imp PA (imp (neg Y1) (imp (neg Y0) Bform))))
adElse =
  let nY0 : Formula
      nY0 = neg Y0
      nY1 : Formula
      nY1 = neg Y1
      cell : Term
      cell = szDerAd (ap1 triFSized (pL sK)) (ap1 triFSized (pR sK))
      opE : Deriv (imp H (imp nY0 (imp nY1 (eqF (ap1 triFSized sK) cell))))
      opE = triFSized_op_Ad_else_imp sK ne_sK
      -- bring to [H,PA,nY1,nY0], feeding H=get4a, nY0=get4d, nY1=get4c.
      EΩ : Deriv (imp H (imp PA (imp nY1 (imp nY0 (eqF (ap1 triFSized sK) cell)))))
      EΩ = ap4c (ap4c (ap4c (lift4 H PA nY1 nY0 opE) (get4a H PA nY1 nY0))
                       (get4d H PA nY1 nY0))
                (get4c H PA nY1 nY0)
      opRw : Deriv (imp H (imp PA (imp nY1 (imp nY0
               (eqF (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized cell))))))
      opRw = ap4c (lift4 H PA nY1 nY0 (ax_eqCong1 wfRedSized (ap1 triFSized sK) cell)) EΩ
      -- pL validity (triF), under [H,PA].
      tvL : Deriv (imp H (imp PA (eqF (wfTri (pL sK)) O)))
      tvL = triFvalidChild H (pL sK) (extractChild_Ad_L_H sK ne_sK)
              (rebound (pL sK) (pLValueBound sK ne_sK))
      bld : Deriv (imp H (imp PA (eqF (ap1 wfRedSized cell) O)))
      bld = build_Ad_ctx H PA (ap1 triFSized (pL sK)) (ap1 triFSized (pR sK)) tvL tvR
      bldΩ : Deriv (imp H (imp PA (imp nY1 (imp nY0 (eqF (ap1 wfRedSized cell) O)))))
      bldΩ = ap4c (ap4c (lift4 H PA nY1 nY0 bld) (get4a H PA nY1 nY0))
                  (get4b H PA nY1 nY0)
  in trans4c (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized cell) O opRw bldΩ

------------------------------------------------------------------------
-- Ad_Su :  cell = szDerRS (triFSized (pArg (pL sK))) (triFSized (pR sK)) .
-- Context [H,PA,Y1,nY0].  Unfolds the OPAQUE left child.

adSu : Deriv (imp H (imp PA (imp Y1 (imp (neg Y0) Bform))))
adSu =
  let nY0 : Formula
      nY0 = neg Y0
      gl : Term
      gl = ap1 triFSized (pArg (pL sK))
      cell : Term
      cell = szDerRS gl (ap1 triFSized (pR sK))
      -- op-eq, brought to [H,PA,Y1,nY0] feeding H=get4a, Y1=get4c.
      opE : Deriv (imp H (imp Y1 (eqF (ap1 triFSized sK) cell)))
      opE = triFSized_op_Ad_Su_imp sK ne_sK
      EΩ : Deriv (imp H (imp PA (imp Y1 (imp nY0 (eqF (ap1 triFSized sK) cell)))))
      EΩ = ap4c (ap4c (lift4 H PA Y1 nY0 opE) (get4a H PA Y1 nY0)) (get4c H PA Y1 nY0)
      opRw : Deriv (imp H (imp PA (imp Y1 (imp nY0
               (eqF (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized cell))))))
      opRw = ap4c (lift4 H PA Y1 nY0 (ax_eqCong1 wfRedSized (ap1 triFSized sK) cell)) EΩ
      -- grandchild validity:  wfRedSized (pArg (pL sK)) = O .
      CVL : Formula
      CVL = eqF (ap1 wfRedSized (pL sK)) O
      CVGL : Formula
      CVGL = eqF (ap1 wfRedSized (pArg (pL sK))) O
      cvl_HPA : Deriv (imp H (imp PA CVL))
      cvl_HPA = ap2c (compI (extractChild_Ad_L_H sK ne_sK) (axK (imp Aform CVL) PA))
                     (liftP H pa2a)
      cvl_Ω : Deriv (imp H (imp PA (imp Y1 (imp nY0 CVL))))
      cvl_Ω = ap4c (ap4c (lift4 H PA Y1 nY0 cvl_HPA) (get4a H PA Y1 nY0))
                   (get4b H PA Y1 nY0)
      esh_Ω : Deriv (imp H (imp PA (imp Y1 (imp nY0 (imp CVL CVGL)))))
      esh_Ω = ap4c (lift4 H PA Y1 nY0 (extractChild_Su_himp (pL sK))) (get4c H PA Y1 nY0)
      cvgl_Ω : Deriv (imp H (imp PA (imp Y1 (imp nY0 CVGL))))
      cvgl_Ω = ap4c esh_Ω cvl_Ω
      -- grandchild leq bound (bare).
      leqGL : Deriv (leq (pArg (pL sK)) (var 0))
      leqGL =
        let leqGLpL : Deriv (leq (pArg (pL sK)) (pL sK))
            leqGLpL = leq_trans (pArg (pL sK)) (ap1 Snd (pL sK)) (pL sK)
                        (sndLe (ap1 Snd (pL sK))) (sndLe (pL sK))
            leqL : Deriv (leq (pL sK) (var 0))
            leqL = rebound (pL sK) (pLValueBound sK ne_sK)
        in leq_trans (pArg (pL sK)) (pL sK) (var 0) leqGLpL leqL
      tvgl_Ω : Deriv (imp H (imp PA (imp Y1 (imp nY0 (eqF (wfTri (pArg (pL sK))) O)))))
      tvgl_Ω =
        let q_Ω : Deriv (imp H (imp PA (imp Y1 (imp nY0 (imp CVGL (eqF (wfTri (pArg (pL sK))) O))))))
            q_Ω = ap4c (lift4 H PA Y1 nY0 (compI pa2phik (QofChild (pArg (pL sK)) leqGL)))
                       (get4b H PA Y1 nY0)
        in ap4c q_Ω cvgl_Ω
      tvR_Ω : Deriv (imp H (imp PA (imp Y1 (imp nY0 (eqF (wfTri (pR sK)) O)))))
      tvR_Ω = ap4c (ap4c (lift4 H PA Y1 nY0 tvR) (get4a H PA Y1 nY0)) (get4b H PA Y1 nY0)
      bld : Deriv (imp H (imp PA (imp Y1 (imp nY0 (eqF (ap1 wfRedSized cell) O)))))
      bld = build_RS_ctx4 H PA Y1 nY0 gl (ap1 triFSized (pR sK)) tvgl_Ω tvR_Ω
  in trans4c (ap1 wfRedSized (ap1 triFSized sK)) (ap1 wfRedSized cell) O opRw bld

------------------------------------------------------------------------
-- Assemble the 3-way sub-dispatch.

glue_Ad : Deriv (imp H (imp PA Bform))
glue_Ad =
  let inner0 : Deriv (imp H (imp PA (imp (neg Y0) Bform)))
      inner0 = caseElimUnderTwo {P1 = H} {P2 = PA} {X = Y1} {Y = neg Y1}
                 {Rf = imp (neg Y0) Bform}
                 (lift2 H PA (identP (neg Y1))) adSu adElse
  in caseElimUnderTwo {P1 = H} {P2 = PA} {X = Y0} {Y = neg Y0} {Rf = Bform}
       (lift2 H PA (identP (neg Y0))) adZe inner0
