{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.EncodedEqChain -- encoded equality-chain primitives.
--
--   encoded_eqTrans_via_middle :
--     given enc(tB = tA) and enc(tB = tC), derive enc(tA = tC) .
--   (Direct application of ax_eqTrans schema with x:=tB, y:=tA, z:=tC.)
--
--   encoded_eqSym :
--     given enc(tA = tB) , derive enc(tB = tA) .
--   (Uses ax_eqTrans at x:=tA, y:=tB, z:=tA together with enc(tA = tA)
--   from EncodedRefl.)
--
--   encoded_eqTrans :
--     given enc(tA = tB) and enc(tB = tC) , derive enc(tA = tC) .
--   (Combines encoded_eqSym + encoded_eqTrans_via_middle.)
--
-- All in the asymmetric / universal-Term encoding ; no Closed
-- premise, no codeFormula constraint.  Parameter names use the
-- prefix  t  to avoid clashing with the BRA combinator  C .

module BRA4.Thm12.EncodedEqChain where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.ThmT                using ( thmT )
open import BRA4.SbStep              using ( InertU )
open import BRA4.Thm12.EncodedMp     using ( encoded_mp )
open import BRA4.Thm12.EncodedAxEqTrans
  using ( Df_axEqTrans ; encodedAxEqTrans ; encodedAxEqTrans_Term )
open import BRA4.Thm12.EncodedRefl
  using ( Df_refl_meta ; encoded_refl ; codedReflTerm )

------------------------------------------------------------------------
-- encEq tA tB  is the encoded form of  "tA = tB" .

encEq : Term -> Term -> Term
encEq tA tB = ap2 Pair (natCode tag_eq) (ap2 Pair tA tB)

------------------------------------------------------------------------
-- encoded_eqTrans_via_middle :
--
--   Given:
--     ih_BA : thmT cBAProof = encEq tB tA
--     ih_BC : thmT cBCProof = encEq tB tC
--   Derive:
--     thmT (mpWrap (mpWrap (Df_axEqTrans tB tA tC) cBAProof) cBCProof) = encEq tA tC

encoded_eqTrans_via_middle :
  (cBAProof cBCProof : Term)
  (tA tB tC : Term)
  (inertA : InertU tA) (inertC : InertU tC)
  (ih_BA : Deriv (eqF (ap1 thmT cBAProof) (encEq tB tA)))
  (ih_BC : Deriv (eqF (ap1 thmT cBCProof) (encEq tB tC))) ->
  Deriv (eqF
    (ap1 thmT
      (ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans tB tA tC) cBAProof))
          cBCProof)))
    (encEq tA tC))
encoded_eqTrans_via_middle cBAProof cBCProof tA tB tC inertA inertC ih_BA ih_BC =
  let
    -- thmT (Df_axEqTrans tB tA tC) = encodedAxEqTrans_Term tB tA tC
    --   = Pair tag_imp (Pair (encEq tB tA)
    --                        (Pair tag_imp (Pair (encEq tB tC) (encEq tA tC)))).
    -- encodedAxEqTrans (tA':=tB, tB':=tA, tC':=tC) needs InertU tA, InertU tC.
    ih_ax :
      Deriv (eqF (ap1 thmT (Df_axEqTrans tB tA tC))
                  (encodedAxEqTrans_Term tB tA tC))
    ih_ax = encodedAxEqTrans tB tA tC inertA inertC

    antPart1 : Term
    antPart1 = encEq tB tA

    consPart1 : Term
    consPart1 =
      ap2 Pair (natCode tag_imp)
        (ap2 Pair (encEq tB tC) (encEq tA tC))

    e_mp1 :
      Deriv (eqF
        (ap1 thmT
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans tB tA tC) cBAProof)))
        consPart1)
    e_mp1 = encoded_mp (Df_axEqTrans tB tA tC) cBAProof antPart1 consPart1
                        ih_ax ih_BA

    antPart2 : Term
    antPart2 = encEq tB tC

    consPart2 : Term
    consPart2 = encEq tA tC

    e_mp2 :
      Deriv (eqF
        (ap1 thmT
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair
              (ap2 Pair (natCode tag_mp)
                (ap2 Pair (Df_axEqTrans tB tA tC) cBAProof))
              cBCProof)))
        consPart2)
    e_mp2 = encoded_mp
              (ap2 Pair (natCode tag_mp)
                (ap2 Pair (Df_axEqTrans tB tA tC) cBAProof))
              cBCProof
              antPart2 consPart2
              e_mp1 ih_BC

  in e_mp2

------------------------------------------------------------------------
-- encoded_eqSym :
--
--   Given:
--     ih_AB : thmT cABProof = encEq tA tB
--   Derive:
--     enc(tB = tA)
--
-- Uses ax_eqTrans at x:=tA, y:=tB, z:=tA together with refl tA :
--   ax_eqTrans gives :  (tA=tB) > (tA=tA) > (tB=tA)
--   Apply mp at  enc(tA=tB) :   -> (tA=tA) > (tB=tA)
--   Apply mp at  enc(tA=tA) :   -> (tB=tA)

encoded_eqSym :
  (cABProof : Term)
  (tA tB : Term)
  (inertA : InertU tA) (inertB : InertU tB)
  (ih_AB : Deriv (eqF (ap1 thmT cABProof) (encEq tA tB))) ->
  Deriv (eqF
    (ap1 thmT
      (ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
          (Df_refl_meta tA))))
    (encEq tB tA))
encoded_eqSym cABProof tA tB inertA inertB ih_AB =
  let
    -- encodedAxEqTrans (tA':=tA, tB':=tB, tC':=tA) needs InertU tB, InertU tA.
    ih_ax :
      Deriv (eqF (ap1 thmT (Df_axEqTrans tA tB tA))
                  (encodedAxEqTrans_Term tA tB tA))
    ih_ax = encodedAxEqTrans tA tB tA inertB inertA

    antPart1 : Term
    antPart1 = encEq tA tB

    consPart1 : Term
    consPart1 =
      ap2 Pair (natCode tag_imp)
        (ap2 Pair (encEq tA tA) (encEq tB tA))

    e_mp1 :
      Deriv (eqF
        (ap1 thmT
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans tA tB tA) cABProof)))
        consPart1)
    e_mp1 = encoded_mp (Df_axEqTrans tA tB tA) cABProof antPart1 consPart1
                        ih_ax ih_AB

    -- enc(tA=tA) via encoded_refl.
    --   codedReflTerm tA = Pair tag_eq (Pair tA tA) = encEq tA tA  definitionally.
    ih_refl :
      Deriv (eqF (ap1 thmT (Df_refl_meta tA)) (encEq tA tA))
    ih_refl = encoded_refl tA

    antPart2 : Term
    antPart2 = encEq tA tA

    consPart2 : Term
    consPart2 = encEq tB tA

    e_mp2 :
      Deriv (eqF
        (ap1 thmT
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair
              (ap2 Pair (natCode tag_mp)
                (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
              (Df_refl_meta tA))))
        consPart2)
    e_mp2 = encoded_mp
              (ap2 Pair (natCode tag_mp)
                (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
              (Df_refl_meta tA)
              antPart2 consPart2
              e_mp1 ih_refl

  in e_mp2

------------------------------------------------------------------------
-- encoded_eqTrans :
--
--   Given:
--     ih_AB : thmT cABProof = encEq tA tB
--     ih_BC : thmT cBCProof = encEq tB tC
--   Derive:
--     encEq tA tC

private
  Df_eqSym : Term -> Term -> Term -> Term
  Df_eqSym cABProof tA tB =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair
        (ap2 Pair (natCode tag_mp)
          (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
        (Df_refl_meta tA))

Df_eqTrans : Term -> Term -> Term -> Term -> Term -> Term
Df_eqTrans cABProof cBCProof tA tB tC =
  ap2 Pair (natCode tag_mp)
    (ap2 Pair
      (ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans tB tA tC) (Df_eqSym cABProof tA tB)))
      cBCProof)

encoded_eqTrans :
  (cABProof cBCProof : Term)
  (tA tB tC : Term)
  (inertA : InertU tA) (inertB : InertU tB) (inertC : InertU tC)
  (ih_AB : Deriv (eqF (ap1 thmT cABProof) (encEq tA tB)))
  (ih_BC : Deriv (eqF (ap1 thmT cBCProof) (encEq tB tC))) ->
  Deriv (eqF (ap1 thmT (Df_eqTrans cABProof cBCProof tA tB tC))
              (encEq tA tC))
encoded_eqTrans cABProof cBCProof tA tB tC inertA inertB inertC ih_AB ih_BC =
  let
    cBAProof : Term
    cBAProof = Df_eqSym cABProof tA tB

    ih_BA : Deriv (eqF (ap1 thmT cBAProof) (encEq tB tA))
    ih_BA = encoded_eqSym cABProof tA tB inertA inertB ih_AB

  in encoded_eqTrans_via_middle cBAProof cBCProof tA tB tC inertA inertC ih_BA ih_BC
