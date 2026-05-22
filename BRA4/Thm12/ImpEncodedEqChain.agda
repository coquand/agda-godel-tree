{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.ImpEncodedEqChain -- Hilbert-lifted (Carneiro) versions of
--  encoded_eqSym  and  encoded_eqTrans  from BRA4.Thm12.EncodedEqChain.
--
-- These are PUBLIC analogs of the  private  helpers used inside
--  BRA4.Thm12.PartRStep (for the thm12_R step proof).  They are pulled
-- out here so downstream clients (e.g. BRA4.Thm.Thm14Step3) can build
-- imp-encoded equality chains without depending on the heavy
-- PartRStep module.
--
-- Pattern : for each unconditional encoded_eq* in
--  BRA4.Thm12.EncodedEqChain , add an  imp P  wrapper around the two
-- inputs / one output.  The closed pieces (axes, refl) are lifted via
-- impLift ; the two mp applications use  imp_encoded_mp  from
--  BRA4.Thm12.EncodedMp .

module BRA4.Thm12.ImpEncodedEqChain where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.ThmT                using ( thmT )
open import BRA4.Thm12.EncodedMp     using ( imp_encoded_mp )
open import BRA4.Thm12.EncodedAxEqTrans
  using ( Df_axEqTrans ; encodedAxEqTrans )
open import BRA4.Thm12.EncodedRefl
  using ( Df_refl_meta ; encoded_refl )
open import BRA4.Thm12.EncodedEqChain
  using ( encEq ; Df_eqTrans )
open import BRA4.Thm12.ImpHelpers    using ( impLift )

------------------------------------------------------------------------
-- imp_encoded_eqSym :  Hilbert-lifted encoded_eqSym .
--
-- Given:
--   imp_ih_AB : Deriv (imp P (eqF (ap1 thmT cABProof) (encEq tA tB)))
-- Derive:
--   imp P (eqF (ap1 thmT (Df_eqSym_term cABProof tA tB)) (encEq tB tA))
--
-- where  Df_eqSym_term  matches the BRA4.Thm12.EncodedEqChain encoding :
--   ap2 Pair (natCode tag_mp)
--     (ap2 Pair
--       (ap2 Pair (natCode tag_mp)
--         (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
--       (Df_refl_meta tA))

imp_encoded_eqSym :
  (P : Formula)
  (cABProof : Term) (tA tB : Term)
  (imp_ih_AB : Deriv (imp P (eqF (ap1 thmT cABProof) (encEq tA tB)))) ->
  Deriv (imp P (eqF
    (ap1 thmT
      (ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
          (Df_refl_meta tA))))
    (encEq tB tA)))
imp_encoded_eqSym P cABProof tA tB imp_ih_AB =
  let
    ih_ax_sym_imp :
      Deriv (imp P (eqF (ap1 thmT (Df_axEqTrans tA tB tA))
                         (ap2 Pair (natCode tag_imp)
                           (ap2 Pair (encEq tA tB)
                             (ap2 Pair (natCode tag_imp)
                               (ap2 Pair (encEq tA tA) (encEq tB tA)))))))
    ih_ax_sym_imp = impLift {P} (encodedAxEqTrans tA tB tA)

    sym_antP1 : Term
    sym_antP1 = encEq tA tB

    sym_consP1 : Term
    sym_consP1 =
      ap2 Pair (natCode tag_imp) (ap2 Pair (encEq tA tA) (encEq tB tA))

    sym_mp1 :
      Deriv (imp P (eqF
        (ap1 thmT (ap2 Pair (natCode tag_mp)
                     (ap2 Pair (Df_axEqTrans tA tB tA) cABProof)))
        sym_consP1))
    sym_mp1 = imp_encoded_mp P (Df_axEqTrans tA tB tA) cABProof
                               sym_antP1 sym_consP1
                               ih_ax_sym_imp imp_ih_AB

    ih_refl_imp :
      Deriv (imp P (eqF (ap1 thmT (Df_refl_meta tA)) (encEq tA tA)))
    ih_refl_imp = impLift {P} (encoded_refl tA)

    sym_antP2 : Term
    sym_antP2 = encEq tA tA

    sym_consP2 : Term
    sym_consP2 = encEq tB tA

    sym_term : Term
    sym_term =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans tA tB tA) cABProof)

    sym_mp2 :
      Deriv (imp P (eqF
        (ap1 thmT (ap2 Pair (natCode tag_mp)
                     (ap2 Pair sym_term (Df_refl_meta tA))))
        sym_consP2))
    sym_mp2 = imp_encoded_mp P sym_term (Df_refl_meta tA)
                               sym_antP2 sym_consP2
                               sym_mp1 ih_refl_imp

  in sym_mp2

------------------------------------------------------------------------
-- imp_encoded_eqTrans : Hilbert-lifted encoded_eqTrans .
--
-- Given:
--   imp_ih_AB : Deriv (imp P (eqF (ap1 thmT cAB) (encEq tA tB)))
--   imp_ih_BC : Deriv (imp P (eqF (ap1 thmT cBC) (encEq tB tC)))
-- Derive:
--   imp P (eqF (ap1 thmT (Df_eqTrans cAB cBC tA tB tC)) (encEq tA tC))
--
-- Internal :  flip cAB to a (tB = tA) proof via imp_encoded_eqSym ,
-- then apply imp_encoded_mp twice with ax_eqTrans(tB,tA,tC) and cBC.
-- The resulting Df coincides with Df_eqTrans cAB cBC tA tB tC from
-- BRA4.Thm12.EncodedEqChain.

imp_encoded_eqTrans :
  (P : Formula)
  (cAB cBC : Term) (tA tB tC : Term)
  (imp_ih_AB : Deriv (imp P (eqF (ap1 thmT cAB) (encEq tA tB))))
  (imp_ih_BC : Deriv (imp P (eqF (ap1 thmT cBC) (encEq tB tC)))) ->
  Deriv (imp P (eqF (ap1 thmT (Df_eqTrans cAB cBC tA tB tC)) (encEq tA tC)))
imp_encoded_eqTrans P cAB cBC tA tB tC imp_ih_AB imp_ih_BC =
  let
    cBA : Term
    cBA = ap2 Pair (natCode tag_mp)
            (ap2 Pair
              (ap2 Pair (natCode tag_mp)
                (ap2 Pair (Df_axEqTrans tA tB tA) cAB))
              (Df_refl_meta tA))

    imp_ih_BA : Deriv (imp P (eqF (ap1 thmT cBA) (encEq tB tA)))
    imp_ih_BA = imp_encoded_eqSym P cAB tA tB imp_ih_AB

    ih_ax_trans_imp :
      Deriv (imp P (eqF (ap1 thmT (Df_axEqTrans tB tA tC))
                         (ap2 Pair (natCode tag_imp)
                           (ap2 Pair (encEq tB tA)
                             (ap2 Pair (natCode tag_imp)
                               (ap2 Pair (encEq tB tC) (encEq tA tC)))))))
    ih_ax_trans_imp = impLift {P} (encodedAxEqTrans tB tA tC)

    trans_antP1 : Term
    trans_antP1 = encEq tB tA

    trans_consP1 : Term
    trans_consP1 =
      ap2 Pair (natCode tag_imp) (ap2 Pair (encEq tB tC) (encEq tA tC))

    trans_mp1 :
      Deriv (imp P (eqF
        (ap1 thmT (ap2 Pair (natCode tag_mp)
                     (ap2 Pair (Df_axEqTrans tB tA tC) cBA)))
        trans_consP1))
    trans_mp1 = imp_encoded_mp P (Df_axEqTrans tB tA tC) cBA
                                 trans_antP1 trans_consP1
                                 ih_ax_trans_imp imp_ih_BA

    trans_antP2 : Term
    trans_antP2 = encEq tB tC

    trans_consP2 : Term
    trans_consP2 = encEq tA tC

    trans_term : Term
    trans_term =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans tB tA tC) cBA)

    trans_mp2 :
      Deriv (imp P (eqF
        (ap1 thmT (ap2 Pair (natCode tag_mp)
                     (ap2 Pair trans_term cBC)))
        trans_consP2))
    trans_mp2 = imp_encoded_mp P trans_term cBC
                                 trans_antP2 trans_consP2
                                 trans_mp1 imp_ih_BC

  in trans_mp2
