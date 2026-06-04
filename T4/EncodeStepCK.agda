{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EncodeStepCK -- clos Step 2 with the antecedent in the CORRECT clos
-- shape :  the FIXED-tail  K(x0,p(r+1),..,pN)  is the single decidable
-- equation  Kr x0 = O  ( NOT a  BigConjFormula ), and ONLY the varying- p
-- consequent  Q(x1)  is a big conjunction.
--
--   encodeStepCK bridge IH :
--     Deriv (eqF (ap1 thmT w) (codeFormula (imp (eqF (ap1 Kr (var 0)) O) Q(x1))))
--
-- i.e.  Deriv thmT(w) = code ( (Kr x0 = O)  =>  Q(x1) ) .
--
-- ASSUMPTIONS ( exactly clos's :  "assume S(r)  AND fix p(r+1),..,pN" ) :
--   * IH    : StagePredF consts r          -- S(r) ;
--   * picks , bound                        -- the FIXED tail p(r+1),..,pN ;
--   * rleN  : NatLe r N .
--
-- THE ONE ISOLATED RESIDUAL ( clos's "we write K(x0,..) as Kr x0 = O" ) :
--   * bridge : Deriv (imp (Kr x0 = O) K_rest)  -- the fixed-tail characteristic
--     implies the conjunction.   This is the SOLE remaining lemma of this step ;
--     everything else ( frontEnd = clos Step 1, monoShift = monotonicity,
--     encode + thmT_complete_rec ) is shipped and composed here in one line.
--
-- Generic in an abstract  consts / Kr  ( so the concrete enumerator is never
-- normalized under  encode / thmT  here ).

module T4.EncodeStepCK where

open import T4.Base

open import BRA3.RuleInst2       using ( NatLe )
open import BRA3.Contrapositive  using ( compI )

open import T4.Tags  using ( tag_sb ; tag_mp )
open import T4.Num   using ( num )
open import T4.Code   using ( codeFormula )
open import T4.ThmT   using ( thmT )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbStep using ( sbf_step_imp )
open import T4.DefWit using ( cImp )
open import T4.Step2bInvariant using ( rightSbfInv )
open import BRA3.Church using ( pi )

open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj      using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )
open import T4.SurpriseG2.StepFrontEnd     using ( frontEnd )
open import T4.KdefBigConjFuelBridge       using ( KdefBigConjF )
open import T4.MonoShift                    using ( monoShift )

open import T4.Thm12.EncodedMp  using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift )
import T4.KrestProvCK

------------------------------------------------------------------------
-- The day- r  encode step, in clos's CK-atom-antecedent shape.

module _ (consts : SurpriseConstsConj)
  (r : Nat) (rleN : NatLe r (SurpriseConstsConj.N consts))
  (Kr : Fun1)
  (picks : Picks) (bound : PicksBound consts picks)
  where

  enum : Fun1
  enum = SurpriseConstsConj.enum consts
  M : Nat
  M = SurpriseConstsConj.M consts

  Krest : Formula
  Krest = BigConjFormula consts (suc r) picks

  -- the FIXED-tail antecedent as ONE equation  Kr x0 = O .
  charAtom : Formula
  charAtom = eqF (ap1 Kr (var zero)) O

  -- the varying- p  big-conjunction consequent at fuel  x1 .
  Qx1 : Formula
  Qx1 = KdefBigConjF enum (var (suc zero)) M (natCode r)

  encodeStepCK :
    (bridge : Deriv (imp charAtom Krest)) ->   -- the one isolated residual
    (IH : StagePredF consts r) ->              -- S(r)
    Deriv (eqF (ap1 thmT
                 (encode (compI bridge
                            (monoShift consts r picks
                               (frontEnd consts r rleN IH picks bound)))))
               (codeFormula (imp charAtom Qx1)))
  encodeStepCK bridge IH =
    thmT_complete_rec
      (compI bridge
        (monoShift consts r picks
          (frontEnd consts r rleN IH picks bound)))

  ------------------------------------------------------------------------
  -- clos Step 2, SECOND half :  substitute  x0 |-> num x0  in the code.
  -- The antecedent  code(Kr x0 = O)  becomes  sbf spec0 (code(Kr x0 = O))
  -- = code(Kr (num x0) = O) ;  the consequent  Q(x1)  is UNCHANGED ( it has
  -- only  x1 = var 1  free ), pinned by  rightSbfInv .

  S0 : Term
  S0 = ap1 num (var zero)
  spec0 : Term
  spec0 = ap2 Pair (natCode zero) S0
  charC : Term
  charC = codeFormula charAtom
  Qc : Term
  Qc = codeFormula Qx1

  -- Deriv reflexivity ( a = a ).
  eqRefl : (a : Term) -> Deriv (eqF a a)
  eqRefl a = ruleTrans (ruleSym (ax_u a)) (ax_u a)

  -- the num-installation step on ANY  d : imp charAtom Qx1 .
  subStepCK :
    (d : Deriv (imp charAtom Qx1)) ->
    Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb) (ap2 pi spec0 (encode d))))
               (cImp (ap2 sbf spec0 charC) Qc))
  subStepCK d =
    ruleTrans (thmT_at_sb spec0 (encode d))
      (ruleTrans (congR sbf spec0 (thmT_complete_rec d))
        (sbf_step_imp zero S0 charC Qc (ap2 sbf spec0 charC) Qc
          (eqRefl (ap2 sbf spec0 charC))
          (rightSbfInv enum S0 M r)))

  -- the implication  (Kr x0 = O) => Q(x1)  whose code we encode + substitute.
  dCK : (bridge : Deriv (imp charAtom Krest)) (IH : StagePredF consts r) ->
        Deriv (imp charAtom Qx1)
  dCK bridge IH =
    compI bridge
      (monoShift consts r picks
        (frontEnd consts r rleN IH picks bound))

  -- the substitution-wrapped proof code.
  wrapped : (bridge : Deriv (imp charAtom Krest)) (IH : StagePredF consts r) -> Term
  wrapped bridge IH = ap2 pi (natCode tag_sb) (ap2 pi spec0 (encode (dCK bridge IH)))

  -- the FULL clos Step 2 ( encode + substitute ) on the CK-atom shape.
  step2CK :
    (bridge : Deriv (imp charAtom Krest)) (IH : StagePredF consts r) ->
    Deriv (eqF (ap1 thmT (wrapped bridge IH)) (cImp (ap2 sbf spec0 charC) Qc))
  step2CK bridge IH = subStepCK (dCK bridge IH)

  ------------------------------------------------------------------------
  -- clos Step 3 :  encoded mp .   Combine
  --   step2CK   : thmT(wrapped) = code( (Kr(num x0)=O) => Q(x1) )      (impLifted)
  --   dKrestCK  : (Kr x0=O)  |-  thmT(w2) = code(Kr(num x0)=O)         (clos Step 4)
  -- into
  --   imp (Kr x0=O) ( thmT(mp wrapped w2) = code Q(x1) ) .

  w2CK : Term
  w2CK = T4.KrestProvCK.w2 Kr

  step3CK :
    (bridge : Deriv (imp charAtom Krest)) (IH : StagePredF consts r) ->
    Deriv (imp charAtom
               (eqF (ap1 thmT (ap2 Pair (natCode tag_mp)
                                (ap2 Pair (wrapped bridge IH) w2CK)))
                    Qc))
  step3CK bridge IH =
    imp_encoded_mp charAtom (wrapped bridge IH) w2CK
      (ap2 sbf spec0 charC) Qc
      (impLift {charAtom} (step2CK bridge IH))
      (T4.KrestProvCK.dKrestCK Kr)
