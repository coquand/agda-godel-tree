{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ImpOutKdef -- the Carneiro-lifted (imp P) version of
-- T4.KdefRecog.outKdef_correct .
--
--   imp_outKdef_correct :
--     (P : Formula) (L w x' : Term) ->
--     Deriv (imp P (eqF (ap1 thmT w) (ap1 (Kcode L) x'))) ->
--     Deriv (imp P (eqF (ap1 (outKdef L) w) x'))
--
-- Mirrors  outKdef_correct  step-for-step, lifting each unconditional
-- equation to  imp P  via  T4.Thm12.ImpHelpers  ( impLift / impEqTrans
-- / impCong1 ) ;   the single hypothesis-dependent step  ( matched )
-- becomes the  imp P  input  matchedImp .   Needed at the witness-imp
-- level in the surprise-G2 inductive step (clos line 41) where the
-- subject readback  outKdef L w = x'  must hold UNDER the Carneiro
-- witness fact  Rf = eqF (ap1 thmT (var k)) (codeFormula K_rest) .

module T4.ImpOutKdef where

open import T4.Base
open import T4.ThmT        using ( thmT )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.Num         using ( num )
open import T4.Kdef        using ( Kcode ; Kcode_eval ; kdefConsts ; kdefSkel )
open import T4.KOut        using ( sndProj ; skelOf_proj )
open import T4.KdefRecog   using ( outKdef )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq )

open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 )

------------------------------------------------------------------------
-- imp_outKdef_correct :  the subject readback, lifted under  imp P .

imp_outKdef_correct :
  (P : Formula) (L w x' : Term) ->
  Deriv (imp P (eqF (ap1 thmT w) (ap1 (Kcode L) x'))) ->
  Deriv (imp P (eqF (ap1 (outKdef L) w) x'))
imp_outKdef_correct P L w x' matchedImp =
  let prj : Fun1
      prj = sndProj (kdefConsts L)

      -- e1, e2, e4 : the CLOSED structural steps of outKdef_correct .
      e1 : Deriv (eqF (ap1 (outKdef L) w)
                      (ap1 decode (ap1 (compose1U prj thmT) w)))
      e1 = compose1U_eq decode (compose1U prj thmT) w

      e2 : Deriv (eqF (ap1 (compose1U prj thmT) w) (ap1 prj (ap1 thmT w)))
      e2 = compose1U_eq prj thmT w

      e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
      e4 = decode_num_id_at x'

      -- innerImp :  thmT w = kdefSkel L (num x')  ( matched then Kcode_eval ) .
      innerImp : Deriv (imp P (eqF (ap1 thmT w) (kdefSkel L (ap1 num x'))))
      innerImp = impEqTrans (ap1 thmT w) (ap1 (Kcode L) x') (kdefSkel L (ap1 num x'))
                   matchedImp (impLift {P} (Kcode_eval L x'))

      congImp : Deriv (imp P (eqF (ap1 prj (ap1 thmT w))
                                   (ap1 prj (kdefSkel L (ap1 num x')))))
      congImp = impCong1 {P} prj (ap1 thmT w) (kdefSkel L (ap1 num x')) innerImp

      -- e3Imp :  projKdef L (thmT w) = num x'  ( cong then skelOf_proj ) .
      e3Imp : Deriv (imp P (eqF (ap1 prj (ap1 thmT w)) (ap1 num x')))
      e3Imp = impEqTrans (ap1 prj (ap1 thmT w))
                         (ap1 prj (kdefSkel L (ap1 num x'))) (ap1 num x')
                congImp (impLift {P} (skelOf_proj (kdefConsts L) (ap1 num x')))

      -- mid0Imp :  compose1U prj thmT w = num x'  ( e2 then e3Imp ) .
      mid0Imp : Deriv (imp P (eqF (ap1 (compose1U prj thmT) w) (ap1 num x')))
      mid0Imp = impEqTrans (ap1 (compose1U prj thmT) w) (ap1 prj (ap1 thmT w)) (ap1 num x')
                  (impLift {P} e2) e3Imp

      midImp : Deriv (imp P (eqF (ap1 decode (ap1 (compose1U prj thmT) w))
                                  (ap1 decode (ap1 num x'))))
      midImp = impCong1 {P} decode (ap1 (compose1U prj thmT) w) (ap1 num x') mid0Imp

      step1Imp : Deriv (imp P (eqF (ap1 (outKdef L) w) (ap1 decode (ap1 num x'))))
      step1Imp = impEqTrans (ap1 (outKdef L) w)
                            (ap1 decode (ap1 (compose1U prj thmT) w))
                            (ap1 decode (ap1 num x'))
                   (impLift {P} e1) midImp
  in impEqTrans (ap1 (outKdef L) w) (ap1 decode (ap1 num x')) x'
       step1Imp (impLift {P} e4)
