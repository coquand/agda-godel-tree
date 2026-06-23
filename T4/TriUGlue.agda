{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriUGlue -- the per-tag GLUE for the bundled unsized CR dispatch.  Each
-- node glue proves
--   imp negLeaf (imp htag (imp PA (conj3 sK = O)))
-- where sK = s (var 0), PA = (sigma bigK (wfRed sK) = O) packs PhiKU + validity.
-- It assembles conj3 sK = O from the three facts (V, S, T) at sK, built from the
-- imp-form opaque eqs + the built per-constructor eqs + the child facts (IH),
-- all under the depth-3 context [negLeaf, htag, PA] (CtxKit).
--
-- This file: shared defs + the Su glue (validates the full assembly).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriUGlue where

open import T4.Base

open import T4.DerCode using ( derZe ; derSu ; derAd ; dgZe ; dgSu ; dgRO ; dgRS )
open import T4.DerCodeS using ( dtag ; pL ; pR )
open import T4.WfRed using ( wfRed ) renaming ( wfRed_derZe to wfRedDZe ; wfRed_derSu to wfRedDSu ; wfRed_derAd to wfRedDAd )
open import T4.DerTri using ( triF )
open import T4.DerSrc using ( srcF ) renaming ( srcF_derZe to srcFDZe ; srcF_derSu to srcFDSu ; srcF_derAd to srcFDAd )
open import T4.DerTgt using ( tgtF ) renaming ( tgtF_derZe to tgtFDZe ; tgtF_derSu to tgtFDSu ; tgtF_derAd to tgtFDAd )
open import T4.DerDev using ( devF ) renaming ( devF_ze# to devFZe ; devF_su# to devFSu ; devF_ad_ze to devFAdZe ; devF_ad_su to devFAdSu )
open import T4.QCheckU using ( conj3 ; qcheckU )
open import T4.QCheckProjU using ( PhiKU ; QofChildU )
open import T4.CRGlueU using ( conj3_unfold )
open import T4.CRGlueImpU
  using ( childV_imp ; childS_imp ; childT_imp ; eqDecO_complete_imp ; sigmaBothO_imp
        ; piBothO_imp ; piZeroL_imp ; piZeroR_imp )
open import T4.EqDecO using ( eqDecO )

open import T4.DerTriUOpaqueImp using ( triF_op_Ze_imp ; triF_op_Su_imp ; triF_op_RO_imp ; triF_op_RS_imp )
open import T4.DerSrcUOpaqueImp using ( srcF_op_Ze_imp ; srcF_op_Su_imp ; srcF_op_Ad_imp ; srcF_op_RO_imp ; srcF_op_RS_imp )
open import T4.DerTgtUOpaqueImp using ( tgtF_op_Ze_imp ; tgtF_op_Su_imp ; tgtF_op_Ad_imp ; tgtF_op_RO_imp ; tgtF_op_RS_imp )
open import T4.WfRedUOpaqueImp using ( wfRed_op_Ze_imp ; wfRed_op_Su_imp ; wfRed_op_Ad_imp ; wfRed_op_RO_imp ; wfRed_op_RS_imp )

open import T4.BoundedConj using ( bigC )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.DescSnd using ( posNeqO )

open import BRA3.Church      using ( pi ; sigma ; sub ; predecessor ; T_p_S_v0 )
open import BRA3.ChurchLeq   using ( leq ; T76 )
open import BRA3.ChurchT78   using ( T78 )
open import BRA3.RuleInst2   using ( ruleInst2 )
open import T4.SigmaZeroN    using ( sigmaZeroL ; sigmaZeroR )
open import T4.TrsCodeObj    using ( su# ; tagSu ; ze# ; ad# )
open import BRA3.Contrapositive using ( compI ; liftP ; identP )
open import T4.CtxKit using ( lift2 ; lift3 ; ap2c ; ap3c ; trans2c ; trans3c )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impCongL ; impCongR )
open import BRA3.Logic using ( eqSymImp )

------------------------------------------------------------------------
-- Shared definitions for  sK = s (var 0) .

sK : Term
sK = ap1 s (var 0)

bigK : Term
bigK = ap2 (bigC qcheckU) O (var 0)

Aform : Formula
Aform = eqF (ap1 wfRed sK) O

PA : Formula
PA = eqF (ap2 sigma bigK (ap1 wfRed sK)) O

negLeaf : Formula
negLeaf = neg (eqF (ap1 Fst sK) (natCode 1))

Bgoal : Formula
Bgoal = eqF (ap1 conj3 sK) O

ne_sK : Deriv (neg (eqF sK O))
ne_sK = posNeqO sK (mp (ruleInst2 0 O 1 (var 0) refl T78) (ruleInst 0 (var 0) T76))

pa2a : Deriv (imp PA Aform)
pa2a = sigmaZeroR bigK (ap1 wfRed sK)

pa2phik : Deriv (imp PA PhiKU)
pa2phik = sigmaZeroL bigK (ap1 wfRed sK)

rebound : (c : Term) -> Deriv (leq c (ap1 predecessor sK)) -> Deriv (leq c (var 0))
rebound c d = ruleTrans (congR sub c (ruleSym (ruleInst 0 (var 0) T_p_S_v0))) d

------------------------------------------------------------------------
-- Depth-3 [negLeaf, htag, PA] helpers.

private
  Gcong : (f : Fun1) (a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a b)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 f a) (ap1 f b)))))
  Gcong f a b htag d =
    ap3c (lift3 negLeaf htag PA (impCong1 f a b (identP (eqF a b)))) d

  GcongSu : (a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a b)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (su# a) (su# b)))))
  GcongSu a b htag d =
    ap3c (lift3 negLeaf htag PA (impCongR Pair a b tagSu (identP (eqF a b)))) d

  Gsym : (a b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a b)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF b a))))
  Gsym a b htag d = ap3c (lift3 negLeaf htag PA (eqSymImp a b)) d

  addPA : {X : Formula} (htag : Formula) ->
    Deriv (imp negLeaf (imp htag X)) ->
    Deriv (imp negLeaf (imp htag (imp PA X)))
  addPA {X} htag d = ap2c (lift2 negLeaf htag (axK X PA)) d

  -- child conj3 = O, from the (imp-form) wfRed opaque eq + validity + the IH.
  mkChildCj : (htag : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed sK) (ap1 wfRed child))))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 conj3 child) O))))
  mkChildCj htag child leqCh wfEq =
    let childValid : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed child) O))))
        childValid = trans3c (ap1 wfRed child) (ap1 wfRed sK) O
                       (Gsym (ap1 wfRed sK) (ap1 wfRed child) htag wfEq)
                       (lift2 negLeaf htag pa2a)
        Q_ctx = ap3c (lift3 negLeaf htag PA (QofChildU child leqCh))
                     (lift2 negLeaf htag pa2phik)
    in ap3c Q_ctx childValid

  -- assemble conj3 sK = O from the three facts (depth-3).
  assembleConj3 : (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed (ap1 triF sK)) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))))) ->
    Deriv (imp negLeaf (imp htag (imp PA
       (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))))) ->
    Deriv (imp negLeaf (imp htag (imp PA Bgoal)))
  assembleConj3 htag factV factS factT =
    let eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
        eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
        sO_ctx = ap3c (lift3 negLeaf htag PA
                   (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
        tO_ctx = ap3c (lift3 negLeaf htag PA
                   (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
        inner_ctx = ap3c (ap3c (lift3 negLeaf htag PA (sigmaBothO_imp eqS eqT)) sO_ctx) tO_ctx
        outer_ctx = ap3c (ap3c (lift3 negLeaf htag PA
                      (sigmaBothO_imp (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner_ctx
    in trans3c (ap1 conj3 sK) (ap2 sigma (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) O
         (lift3 negLeaf htag PA (conj3_unfold sK)) outer_ctx

------------------------------------------------------------------------
-- The Su glue.

glue_Su : Deriv (imp negLeaf (imp (eqF (dtag sK) dgSu) (imp PA Bgoal)))
glue_Su =
  let htag : Formula
      htag = eqF (dtag sK) dgSu
      ch : Term
      ch = pL sK
      leqCh : Deriv (leq ch (var 0))
      leqCh = rebound ch (pLValueBound sK ne_sK)
      ----------------------------------------------------------------
      A_ctx : Deriv (imp negLeaf (imp htag (imp PA Aform)))
      A_ctx = lift2 negLeaf htag pa2a
      wfEq : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed sK) (ap1 wfRed ch)))))
      wfEq = addPA htag (wfRed_op_Su_imp sK ne_sK)
      childValid : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed ch) O))))
      childValid =
        trans3c (ap1 wfRed ch) (ap1 wfRed sK) O
          (Gsym (ap1 wfRed sK) (ap1 wfRed ch) htag wfEq) A_ctx
      phik_ctx : Deriv (imp negLeaf (imp htag (imp PA PhiKU)))
      phik_ctx = lift2 negLeaf htag pa2phik
      Q_ctx : Deriv (imp negLeaf (imp htag (imp PA
                (imp (eqF (ap1 wfRed ch) O) (eqF (ap1 conj3 ch) O)))))
      Q_ctx = ap3c (lift3 negLeaf htag PA (QofChildU ch leqCh)) phik_ctx
      childCj : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 conj3 ch) O))))
      childCj = ap3c Q_ctx childValid
      cV = ap3c (lift3 negLeaf htag PA (childV_imp ch)) childCj
      cS = ap3c (lift3 negLeaf htag PA (childS_imp ch)) childCj
      cT = ap3c (lift3 negLeaf htag PA (childT_imp ch)) childCj
      ----------------------------------------------------------------
      triEq : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 triF sK) (derSu (ap1 triF ch))))))
      triEq = addPA htag (triF_op_Su_imp sK ne_sK)
      srcEqSK : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 srcF sK) (su# (ap1 srcF ch))))))
      srcEqSK = addPA htag (srcF_op_Su_imp sK ne_sK)
      tgtEqSK : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 tgtF sK) (su# (ap1 tgtF ch))))))
      tgtEqSK = addPA htag (tgtF_op_Su_imp sK ne_sK)
      ----------------------------------------------------------------
      factV : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed (ap1 triF sK)) O))))
      factV =
        trans3c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derSu (ap1 triF ch))) O
          (Gcong wfRed (ap1 triF sK) (derSu (ap1 triF ch)) htag triEq)
          (trans3c (ap1 wfRed (derSu (ap1 triF ch))) (ap1 wfRed (ap1 triF ch)) O
            (lift3 negLeaf htag PA (wfRedDSu (ap1 triF ch))) cV)
      factS : Deriv (imp negLeaf (imp htag (imp PA
                (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))))
      factS =
        trans3c (ap1 srcF (ap1 triF sK)) (su# (ap1 srcF (ap1 triF ch))) (ap1 tgtF sK)
          (trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (derSu (ap1 triF ch)))
              (su# (ap1 srcF (ap1 triF ch)))
            (Gcong srcF (ap1 triF sK) (derSu (ap1 triF ch)) htag triEq)
            (lift3 negLeaf htag PA (srcFDSu (ap1 triF ch))))
          (trans3c (su# (ap1 srcF (ap1 triF ch))) (su# (ap1 tgtF ch)) (ap1 tgtF sK)
            (GcongSu (ap1 srcF (ap1 triF ch)) (ap1 tgtF ch) htag cS)
            (Gsym (ap1 tgtF sK) (su# (ap1 tgtF ch)) htag tgtEqSK))
      devSrcEq : Deriv (imp negLeaf (imp htag (imp PA
                   (eqF (ap1 devF (ap1 srcF sK)) (su# (ap1 devF (ap1 srcF ch)))))))
      devSrcEq =
        trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (su# (ap1 srcF ch)))
            (su# (ap1 devF (ap1 srcF ch)))
          (Gcong devF (ap1 srcF sK) (su# (ap1 srcF ch)) htag srcEqSK)
          (lift3 negLeaf htag PA (devFSu (ap1 srcF ch)))
      factT : Deriv (imp negLeaf (imp htag (imp PA
                (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))))
      factT =
        trans3c (ap1 tgtF (ap1 triF sK)) (su# (ap1 tgtF (ap1 triF ch))) (ap1 devF (ap1 srcF sK))
          (trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derSu (ap1 triF ch)))
              (su# (ap1 tgtF (ap1 triF ch)))
            (Gcong tgtF (ap1 triF sK) (derSu (ap1 triF ch)) htag triEq)
            (lift3 negLeaf htag PA (tgtFDSu (ap1 triF ch))))
          (trans3c (su# (ap1 tgtF (ap1 triF ch))) (su# (ap1 devF (ap1 srcF ch)))
              (ap1 devF (ap1 srcF sK))
            (GcongSu (ap1 tgtF (ap1 triF ch)) (ap1 devF (ap1 srcF ch)) htag cT)
            (Gsym (ap1 devF (ap1 srcF sK)) (su# (ap1 devF (ap1 srcF ch))) htag devSrcEq))
      ----------------------------------------------------------------
      -- assemble  conj3 sK = O  from V, S, T .
      eqS : Term
      eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
      eqT : Term
      eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
      sO_ctx : Deriv (imp negLeaf (imp htag (imp PA (eqF eqS O))))
      sO_ctx = ap3c (lift3 negLeaf htag PA
                 (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
      tO_ctx : Deriv (imp negLeaf (imp htag (imp PA (eqF eqT O))))
      tO_ctx = ap3c (lift3 negLeaf htag PA
                 (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
      inner_ctx : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 sigma eqS eqT) O))))
      inner_ctx = ap3c (ap3c (lift3 negLeaf htag PA (sigmaBothO_imp eqS eqT)) sO_ctx) tO_ctx
      outer_ctx : Deriv (imp negLeaf (imp htag (imp PA
                    (eqF (ap2 sigma (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) O))))
      outer_ctx = ap3c (ap3c (lift3 negLeaf htag PA
                    (sigmaBothO_imp (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner_ctx
  in trans3c (ap1 conj3 sK)
       (ap2 sigma (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) O
       (lift3 negLeaf htag PA (conj3_unfold sK)) outer_ctx

------------------------------------------------------------------------
-- The RO glue.  triF sK = triF (pL sK) ; srcF sK = ad# ze# (srcF ch) ; tgtF sK = tgtF ch.

glue_RO : Deriv (imp negLeaf (imp (eqF (dtag sK) dgRO) (imp PA Bgoal)))
glue_RO =
  let htag : Formula
      htag = eqF (dtag sK) dgRO
      ch : Term
      ch = pL sK
      leqCh : Deriv (leq ch (var 0))
      leqCh = rebound ch (pLValueBound sK ne_sK)
      childCj = mkChildCj htag ch leqCh (addPA htag (wfRed_op_RO_imp sK ne_sK))
      cV = ap3c (lift3 negLeaf htag PA (childV_imp ch)) childCj
      cS = ap3c (lift3 negLeaf htag PA (childS_imp ch)) childCj
      cT = ap3c (lift3 negLeaf htag PA (childT_imp ch)) childCj
      triEq = addPA htag (triF_op_RO_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_RO_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_RO_imp sK ne_sK)
      factV : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed (ap1 triF sK)) O))))
      factV = trans3c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (ap1 triF ch)) O
                (Gcong wfRed (ap1 triF sK) (ap1 triF ch) htag triEq) cV
      factS : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))))
      factS = trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (ap1 triF ch)) (ap1 tgtF sK)
                (Gcong srcF (ap1 triF sK) (ap1 triF ch) htag triEq)
                (trans3c (ap1 srcF (ap1 triF ch)) (ap1 tgtF ch) (ap1 tgtF sK)
                  cS (Gsym (ap1 tgtF sK) (ap1 tgtF ch) htag tgtEqSK))
      devSrcEq : Deriv (imp negLeaf (imp htag (imp PA
                   (eqF (ap1 devF (ap1 srcF sK)) (ap1 devF (ap1 srcF ch))))))
      devSrcEq = trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# ze# (ap1 srcF ch))) (ap1 devF (ap1 srcF ch))
                   (Gcong devF (ap1 srcF sK) (ad# ze# (ap1 srcF ch)) htag srcEqSK)
                   (lift3 negLeaf htag PA (devFAdZe (ap1 srcF ch)))
      factT : Deriv (imp negLeaf (imp htag (imp PA
                (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))))
      factT = trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (ap1 triF ch)) (ap1 devF (ap1 srcF sK))
                (Gcong tgtF (ap1 triF sK) (ap1 triF ch) htag triEq)
                (trans3c (ap1 tgtF (ap1 triF ch)) (ap1 devF (ap1 srcF ch)) (ap1 devF (ap1 srcF sK))
                  cT (Gsym (ap1 devF (ap1 srcF sK)) (ap1 devF (ap1 srcF ch)) htag devSrcEq))
  in assembleConj3 htag factV factS factT

------------------------------------------------------------------------
-- The Ze (leaf) glue.  Single antecedent  Hleaf = (Fst sK = natCode 1) ;
-- depth-2 context [Hleaf, PA].  No children: all facts are built (derZe / ze#).

Hleaf : Formula
Hleaf = eqF (ap1 Fst sK) (natCode 1)

private
  addPA2 : {X : Formula} -> Deriv (imp Hleaf X) -> Deriv (imp Hleaf (imp PA X))
  addPA2 {X} d = compI d (axK X PA)

  H2cong : (f : Fun1) (a b : Term) ->
    Deriv (imp Hleaf (imp PA (eqF a b))) ->
    Deriv (imp Hleaf (imp PA (eqF (ap1 f a) (ap1 f b))))
  H2cong f a b d = ap2c (lift2 Hleaf PA (impCong1 f a b (identP (eqF a b)))) d

  H2sym : (a b : Term) ->
    Deriv (imp Hleaf (imp PA (eqF a b))) -> Deriv (imp Hleaf (imp PA (eqF b a)))
  H2sym a b d = ap2c (lift2 Hleaf PA (eqSymImp a b)) d

glue_Ze : Deriv (imp Hleaf (imp PA Bgoal))
glue_Ze =
  let triEqP : Deriv (imp Hleaf (imp PA (eqF (ap1 triF sK) derZe)))
      triEqP = addPA2 (triF_op_Ze_imp sK ne_sK)
      tgtEqP : Deriv (imp Hleaf (imp PA (eqF (ap1 tgtF sK) ze#)))
      tgtEqP = addPA2 (tgtF_op_Ze_imp sK ne_sK)
      srcEqP : Deriv (imp Hleaf (imp PA (eqF (ap1 srcF sK) ze#)))
      srcEqP = addPA2 (srcF_op_Ze_imp sK ne_sK)
      factV : Deriv (imp Hleaf (imp PA (eqF (ap1 wfRed (ap1 triF sK)) O)))
      factV = trans2c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed derZe) O
                (H2cong wfRed (ap1 triF sK) derZe triEqP)
                (lift2 Hleaf PA wfRedDZe)
      factS : Deriv (imp Hleaf (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))))
      factS = trans2c (ap1 srcF (ap1 triF sK)) ze# (ap1 tgtF sK)
                (trans2c (ap1 srcF (ap1 triF sK)) (ap1 srcF derZe) ze#
                  (H2cong srcF (ap1 triF sK) derZe triEqP)
                  (lift2 Hleaf PA srcFDZe))
                (H2sym (ap1 tgtF sK) ze# tgtEqP)
      factT : Deriv (imp Hleaf (imp PA (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))))
      factT = trans2c (ap1 tgtF (ap1 triF sK)) ze# (ap1 devF (ap1 srcF sK))
                (trans2c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF derZe) ze#
                  (H2cong tgtF (ap1 triF sK) derZe triEqP)
                  (lift2 Hleaf PA tgtFDZe))
                (H2sym (ap1 devF (ap1 srcF sK)) ze#
                  (trans2c (ap1 devF (ap1 srcF sK)) (ap1 devF ze#) ze#
                    (H2cong devF (ap1 srcF sK) ze# srcEqP)
                    (lift2 Hleaf PA devFZe)))
      eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
      eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
      sO_ctx = ap2c (lift2 Hleaf PA (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
      tO_ctx = ap2c (lift2 Hleaf PA (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
      inner_ctx = ap2c (ap2c (lift2 Hleaf PA (sigmaBothO_imp eqS eqT)) sO_ctx) tO_ctx
      outer_ctx = ap2c (ap2c (lift2 Hleaf PA
                    (sigmaBothO_imp (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner_ctx
  in trans2c (ap1 conj3 sK) (ap2 sigma (ap1 wfRed (ap1 triF sK)) (ap2 sigma eqS eqT)) O
       (lift2 Hleaf PA (conj3_unfold sK)) outer_ctx

------------------------------------------------------------------------
-- Binary helpers and the RS glue.

private
  mkChildCjV : (htag : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed child) O)))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 conj3 child) O))))
  mkChildCjV htag child leqCh childValid =
    ap3c (ap3c (lift3 negLeaf htag PA (QofChildU child leqCh))
               (lift2 negLeaf htag pa2phik)) childValid

  GpiL : (a a' b : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a a')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 pi a b) (ap2 pi a' b)))))
  GpiL a a' b htag d = ap3c (lift3 negLeaf htag PA (impCongL pi a a' b (identP (eqF a a')))) d

  GpiR : (c a a' : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a a')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 pi c a) (ap2 pi c a')))))
  GpiR c a a' htag d = ap3c (lift3 negLeaf htag PA (impCongR pi a a' c (identP (eqF a a')))) d

  -- cong  su# (ad# a b) = su# (ad# a' b')  from  a=a', b=b' .
  GcongAdSu : (a a' b b' : Term) (htag : Formula) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF a a')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF b b')))) ->
    Deriv (imp negLeaf (imp htag (imp PA (eqF (su# (ad# a b)) (su# (ad# a' b'))))))
  GcongAdSu a a' b b' htag da db =
    let innerAd : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap2 pi a b) (ap2 pi a' b')))))
        innerAd = trans3c (ap2 pi a b) (ap2 pi a' b) (ap2 pi a' b')
                    (GpiL a a' b htag da) (GpiR a' b b' htag db)
        adEq : Deriv (imp negLeaf (imp htag (imp PA (eqF (ad# a b) (ad# a' b')))))
        adEq = GpiR (natCode 2) (ap2 pi a b) (ap2 pi a' b') htag innerAd
    in GcongSu (ad# a b) (ad# a' b') htag adEq

glue_RS : Deriv (imp negLeaf (imp (eqF (dtag sK) dgRS) (imp PA Bgoal)))
glue_RS =
  let htag : Formula
      htag = eqF (dtag sK) dgRS
      cL : Term
      cL = pL sK
      cR : Term
      cR = pR sK
      leqL = rebound cL (pLValueBound sK ne_sK)
      leqR = rebound cR (pRValueBound sK ne_sK)
      wfEqRS : Deriv (imp negLeaf (imp htag (imp PA
                 (eqF (ap1 wfRed sK) (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR))))))
      wfEqRS = addPA htag (wfRed_op_RS_imp sK ne_sK)
      wfPiO : Deriv (imp negLeaf (imp htag (imp PA
                (eqF (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR)) O))))
      wfPiO = trans3c (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR)) (ap1 wfRed sK) O
                (Gsym (ap1 wfRed sK) (ap2 pi (ap1 wfRed cL) (ap1 wfRed cR)) htag wfEqRS)
                (lift2 negLeaf htag pa2a)
      cvL : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed cL) O))))
      cvL = ap3c (lift3 negLeaf htag PA (piZeroL_imp (ap1 wfRed cL) (ap1 wfRed cR))) wfPiO
      cvR : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed cR) O))))
      cvR = ap3c (lift3 negLeaf htag PA (piZeroR_imp (ap1 wfRed cL) (ap1 wfRed cR))) wfPiO
      cjL = mkChildCjV htag cL leqL cvL
      cjR = mkChildCjV htag cR leqR cvR
      cVL = ap3c (lift3 negLeaf htag PA (childV_imp cL)) cjL
      cSL = ap3c (lift3 negLeaf htag PA (childS_imp cL)) cjL
      cTL = ap3c (lift3 negLeaf htag PA (childT_imp cL)) cjL
      cVR = ap3c (lift3 negLeaf htag PA (childV_imp cR)) cjR
      cSR = ap3c (lift3 negLeaf htag PA (childS_imp cR)) cjR
      cTR = ap3c (lift3 negLeaf htag PA (childT_imp cR)) cjR
      triEq = addPA htag (triF_op_RS_imp sK ne_sK)
      tgtEqSK = addPA htag (tgtF_op_RS_imp sK ne_sK)
      srcEqSK = addPA htag (srcF_op_RS_imp sK ne_sK)
      tL : Term
      tL = ap1 triF cL
      tR : Term
      tR = ap1 triF cR
      factV : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 wfRed (ap1 triF sK)) O))))
      factV =
        trans3c (ap1 wfRed (ap1 triF sK)) (ap1 wfRed (derSu (derAd tL tR))) O
          (Gcong wfRed (ap1 triF sK) (derSu (derAd tL tR)) htag triEq)
          (trans3c (ap1 wfRed (derSu (derAd tL tR))) (ap1 wfRed (derAd tL tR)) O
            (lift3 negLeaf htag PA (wfRedDSu (derAd tL tR)))
            (trans3c (ap1 wfRed (derAd tL tR)) (ap2 pi (ap1 wfRed tL) (ap1 wfRed tR)) O
              (lift3 negLeaf htag PA (wfRedDAd tL tR))
              (ap3c (ap3c (lift3 negLeaf htag PA (piBothO_imp (ap1 wfRed tL) (ap1 wfRed tR))) cVL) cVR)))
      factS : Deriv (imp negLeaf (imp htag (imp PA (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)))))
      factS =
        trans3c (ap1 srcF (ap1 triF sK)) (su# (ad# (ap1 tgtF cL) (ap1 tgtF cR))) (ap1 tgtF sK)
          (trans3c (ap1 srcF (ap1 triF sK)) (su# (ad# (ap1 srcF tL) (ap1 srcF tR)))
              (su# (ad# (ap1 tgtF cL) (ap1 tgtF cR)))
            (trans3c (ap1 srcF (ap1 triF sK)) (ap1 srcF (derSu (derAd tL tR)))
                (su# (ad# (ap1 srcF tL) (ap1 srcF tR)))
              (Gcong srcF (ap1 triF sK) (derSu (derAd tL tR)) htag triEq)
              (trans3c (ap1 srcF (derSu (derAd tL tR))) (su# (ap1 srcF (derAd tL tR)))
                  (su# (ad# (ap1 srcF tL) (ap1 srcF tR)))
                (lift3 negLeaf htag PA (srcFDSu (derAd tL tR)))
                (GcongSu (ap1 srcF (derAd tL tR)) (ad# (ap1 srcF tL) (ap1 srcF tR)) htag
                  (lift3 negLeaf htag PA (srcFDAd tL tR)))))
            (GcongAdSu (ap1 srcF tL) (ap1 tgtF cL) (ap1 srcF tR) (ap1 tgtF cR) htag cSL cSR))
          (Gsym (ap1 tgtF sK) (su# (ad# (ap1 tgtF cL) (ap1 tgtF cR))) htag tgtEqSK)
      devSrcEq : Deriv (imp negLeaf (imp htag (imp PA
                   (eqF (ap1 devF (ap1 srcF sK))
                        (su# (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR))))))))
      devSrcEq =
        trans3c (ap1 devF (ap1 srcF sK)) (ap1 devF (ad# (su# (ap1 srcF cL)) (ap1 srcF cR)))
            (su# (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR))))
          (Gcong devF (ap1 srcF sK) (ad# (su# (ap1 srcF cL)) (ap1 srcF cR)) htag srcEqSK)
          (lift3 negLeaf htag PA (devFAdSu (ap1 srcF cL) (ap1 srcF cR)))
      factT : Deriv (imp negLeaf (imp htag (imp PA
                (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))))))
      factT =
        trans3c (ap1 tgtF (ap1 triF sK))
            (su# (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR)))) (ap1 devF (ap1 srcF sK))
          (trans3c (ap1 tgtF (ap1 triF sK)) (su# (ad# (ap1 tgtF tL) (ap1 tgtF tR)))
              (su# (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR))))
            (trans3c (ap1 tgtF (ap1 triF sK)) (ap1 tgtF (derSu (derAd tL tR)))
                (su# (ad# (ap1 tgtF tL) (ap1 tgtF tR)))
              (Gcong tgtF (ap1 triF sK) (derSu (derAd tL tR)) htag triEq)
              (trans3c (ap1 tgtF (derSu (derAd tL tR))) (su# (ap1 tgtF (derAd tL tR)))
                  (su# (ad# (ap1 tgtF tL) (ap1 tgtF tR)))
                (lift3 negLeaf htag PA (tgtFDSu (derAd tL tR)))
                (GcongSu (ap1 tgtF (derAd tL tR)) (ad# (ap1 tgtF tL) (ap1 tgtF tR)) htag
                  (lift3 negLeaf htag PA (tgtFDAd tL tR)))))
            (GcongAdSu (ap1 tgtF tL) (ap1 devF (ap1 srcF cL)) (ap1 tgtF tR) (ap1 devF (ap1 srcF cR))
               htag cTL cTR))
          (Gsym (ap1 devF (ap1 srcF sK))
             (su# (ad# (ap1 devF (ap1 srcF cL)) (ap1 devF (ap1 srcF cR)))) htag devSrcEq)
  in assembleConj3 htag factV factS factT
