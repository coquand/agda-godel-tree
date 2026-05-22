{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedMp -- the encoded modus-ponens primitive.
--
-- Given:
--   ih_imp : thmT cPImpIdx = Pair tag_imp (Pair antPart consPart)
--   ih_a   : thmT cAIdx   = antPart
-- we derive:
--   thmT (Pair tag_mp (Pair cPImpIdx cAIdx)) = consPart .
--
-- This is the universal Term-Term form : antPart and consPart are
-- ARBITRARY Terms (no  codeFormula  constraint).  The wf_ant proof
-- uses  natEqF_self_univ  (closed-free reflexivity of natEqF on any
-- Term).
--
-- Built atop  BRA4.ThmTAtMp.thmT_at_mp .

module BRA4.Thm12.EncodedMp where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.ThmT             using ( thmT )
open import BRA4.ThmTAtMp         using ( thmT_at_mp ; imp_thmT_at_mp )

open import BRA3.Church           using ( pi )
open import BRA3.ChurchT117       using ( Fst )
open import BRA3.ChurchT116       using ( Snd )
open import BRA3.PairAlgebra      using ( axFst ; axSnd )
open import BRA3.SubT.NatEq       using ( natEqF )
open import BRA3.SubT.NatEqRefl   using ( natEqF_self_univ )

open import BRA4.Thm12.ImpHelpers
  using ( impLift ; impEqTrans )

------------------------------------------------------------------------
-- The primary encoded-mp lemma.

encoded_mp :
  (cPImpIdx cAIdx : Term)
  (antPart consPart : Term)
  (ih_imp : Deriv (eqF (ap1 thmT cPImpIdx)
                        (ap2 Pair (natCode tag_imp) (ap2 Pair antPart consPart))))
  (ih_a   : Deriv (eqF (ap1 thmT cAIdx) antPart)) ->
  Deriv (eqF (ap1 thmT (ap2 Pair (natCode tag_mp) (ap2 Pair cPImpIdx cAIdx)))
              consPart)
encoded_mp cPImpIdx cAIdx antPart consPart ih_imp ih_a =
  let cImpVal : Term
      cImpVal = ap2 Pair (natCode tag_imp) (ap2 Pair antPart consPart)

      cAVal : Term
      cAVal = antPart

      -- wf_tag : Fst cImpVal = natCode tag_imp.
      wf_tag : Deriv (eqF (ap1 Fst cImpVal) (natCode tag_imp))
      wf_tag = axFst (natCode tag_imp) (ap2 Pair antPart consPart)

      -- wf_ant : natEqF (Fst (Snd cImpVal)) cAVal = sO.
      --   Snd cImpVal = Pair antPart consPart  via axSnd.
      --   Fst (Snd cImpVal) = antPart  via cong1 Fst + axFst.
      --   natEqF antPart antPart = sO  via natEqF_self_univ.
      snd_eq : Deriv (eqF (ap1 Snd cImpVal) (ap2 Pair antPart consPart))
      snd_eq = axSnd (natCode tag_imp) (ap2 Pair antPart consPart)

      fst_snd_eq : Deriv (eqF (ap1 Fst (ap1 Snd cImpVal)) antPart)
      fst_snd_eq =
        ruleTrans (cong1 Fst snd_eq) (axFst antPart consPart)

      natEqF_lift :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)
                    (ap2 natEqF antPart antPart))
      natEqF_lift = congL natEqF antPart fst_snd_eq

      natEqF_refl_at : Deriv (eqF (ap2 natEqF antPart antPart) (ap1 s O))
      natEqF_refl_at = natEqF_self_univ antPart

      wf_ant :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal) (ap1 s O))
      wf_ant = ruleTrans natEqF_lift natEqF_refl_at

      -- Apply thmT_at_mp.
      thmT_mp :
        Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
                    (ap1 Snd (ap1 Snd cImpVal)))
      thmT_mp = thmT_at_mp cPImpIdx cAIdx cImpVal cAVal ih_imp ih_a wf_tag wf_ant

      -- Snd (Snd cImpVal) = consPart.
      snd_snd_eq :
        Deriv (eqF (ap1 Snd (ap1 Snd cImpVal)) consPart)
      snd_snd_eq =
        ruleTrans (cong1 Snd snd_eq) (axSnd antPart consPart)

  in ruleTrans thmT_mp snd_snd_eq

------------------------------------------------------------------------
-- imp_encoded_mp -- Carneiro-lifted version.
--
-- Same conclusion as encoded_mp but with imp_ih_imp / imp_ih_a as
-- imp-lifted Deriv (imp P (eqF ...)).  Closed parts (wf_tag, wf_ant,
-- snd_snd_eq) are wrapped via impLift ; the thmT_at_mp call becomes
-- imp_thmT_at_mp.  Final composition via impEqTrans.

imp_encoded_mp :
  (P : Formula)
  (cPImpIdx cAIdx : Term)
  (antPart consPart : Term)
  (imp_ih_imp : Deriv (imp P (eqF (ap1 thmT cPImpIdx)
                                   (ap2 Pair (natCode tag_imp)
                                     (ap2 Pair antPart consPart)))))
  (imp_ih_a   : Deriv (imp P (eqF (ap1 thmT cAIdx) antPart))) ->
  Deriv (imp P (eqF (ap1 thmT (ap2 Pair (natCode tag_mp) (ap2 Pair cPImpIdx cAIdx)))
                     consPart))
imp_encoded_mp P cPImpIdx cAIdx antPart consPart imp_ih_imp imp_ih_a =
  let cImpVal : Term
      cImpVal = ap2 Pair (natCode tag_imp) (ap2 Pair antPart consPart)

      cAVal : Term
      cAVal = antPart

      wf_tag : Deriv (eqF (ap1 Fst cImpVal) (natCode tag_imp))
      wf_tag = axFst (natCode tag_imp) (ap2 Pair antPart consPart)

      snd_eq : Deriv (eqF (ap1 Snd cImpVal) (ap2 Pair antPart consPart))
      snd_eq = axSnd (natCode tag_imp) (ap2 Pair antPart consPart)

      fst_snd_eq : Deriv (eqF (ap1 Fst (ap1 Snd cImpVal)) antPart)
      fst_snd_eq =
        ruleTrans (cong1 Fst snd_eq) (axFst antPart consPart)

      natEqF_lift :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal)
                    (ap2 natEqF antPart antPart))
      natEqF_lift = congL natEqF antPart fst_snd_eq

      natEqF_refl_at : Deriv (eqF (ap2 natEqF antPart antPart) (ap1 s O))
      natEqF_refl_at = natEqF_self_univ antPart

      wf_ant :
        Deriv (eqF (ap2 natEqF (ap1 Fst (ap1 Snd cImpVal)) cAVal) (ap1 s O))
      wf_ant = ruleTrans natEqF_lift natEqF_refl_at

      -- The Carneiro-lifted core.
      imp_thmT_mp :
        Deriv (imp P (eqF (ap1 thmT (ap2 pi (natCode tag_mp) (ap2 pi cPImpIdx cAIdx)))
                           (ap1 Snd (ap1 Snd cImpVal))))
      imp_thmT_mp = imp_thmT_at_mp P cPImpIdx cAIdx cImpVal cAVal
                      imp_ih_imp imp_ih_a wf_tag wf_ant

      snd_snd_eq : Deriv (eqF (ap1 Snd (ap1 Snd cImpVal)) consPart)
      snd_snd_eq =
        ruleTrans (cong1 Snd snd_eq) (axSnd antPart consPart)

  in impEqTrans _ (ap1 Snd (ap1 Snd cImpVal)) consPart
       imp_thmT_mp
       (impLift {P} snd_snd_eq)
