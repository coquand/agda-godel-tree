{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinStepCK -- clos Step 5 ( internalise  coverBridge ) + the ABSTRACT
-- Chaitin-GI instantiation ( Step 6 core ), GENERIC in the antecedent  P .
--
-- INPUT ( the  step3CK  output shape, "under  P ,  T  proves  Q(x1)" ) :
--   dProv : imp P (thmT W = code(Q(x1)))        Q(x1) = KdefBigConjF (big conj) .
--
-- The abstract Chaitin-GI  ( T4.ChaitinGIAbs.chaitinGI )  is
--   (w) -> imp (thmT w = KcodeAlph (out w)) (thmT (G w) = code(0=1)) ,
-- whose hypothesis is the  KdefAlph  ( = "K(_) > L*" ) shape -- NOT  Q(x1) .
-- So we FIRST bridge  Q(x1) => KdefAlph  ( coverBridge , as the  dCB  INPUT ),
-- INTERNALISE it by  encoded_mp  ( landing  thmT W'' = KcodeAlph (natCode r) ),
-- and only THEN instantiate  chaitinGI  at  W'' :
--
--   chaitinClashCK checkFires dCB W dProv :
--     Deriv (imp P (eqF (ap1 thmT (gFunAbs W'')) codeFalse))
--          where  W'' = Pair tag_mp (Pair (encode dCB) W) .
--
-- i.e.  "under  P ,  T  proves  0 = 1  ( about the diagonal  G W'' )".
-- Generic in abstract  consts  ( enum stuck => no >20s blowup ) and in  P  ;
-- instantiate  P := charAtom  ( = Kr x0 = O )  at the headline.

open import T4.Base

open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )

module T4.ChaitinStepCK
  (Lstar_meta : Nat)
  (consts     : SurpriseConstsConj)
  (P          : Formula)
  (r          : Nat)
  where

open import T4.Tags  using ( tag_mp )
open import T4.Code  using ( codeFalse ; codeFormula ; falseF )
open import T4.Counting using ( negToImpFalse )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.ThmT  using ( thmT )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )

open import T4.CheckAlphN using ( checkAlphN )
open import T4.ProgEnc using ( enc )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.KdefAlph Lstar_meta using ( KdefAlph ; KcodeAlph ; KcodeAlph_correct )
open import T4.KdefRecogAlph Lstar_meta using ( outKdefAlph )
open import T4.KdefRecogImpAlph Lstar_meta using ( imp_outKdefAlph_correct )
open import T4.ChaitinGIAbs Lstar_meta using ( chaitinGI ; gFunAbs )

open import T4.KdefBigConjFuelBridge using ( KdefBigConjF )

open import T4.Thm12.EncodedMp  using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift ; impCong1 ; impRuleSym )
open import T4.ImpExtras        using ( imp_eqTrans_imp )
open import BRA3.Contrapositive using ( compI )

------------------------------------------------------------------------
-- The two K-formulas at day  r .

enum : Fun1
enum = SurpriseConstsConj.enum consts
M : Nat
M = SurpriseConstsConj.M consts

KBCf : Formula                   -- Q(x1) = big conjunction .
KBCf = KdefBigConjF enum (var (suc zero)) M (natCode r)

KA : Formula                     -- KdefAlph (= "K(r) > L*" ) .
KA = KdefAlph (natCode r)

------------------------------------------------------------------------
-- clos Step 5 + Step 6 core, generic in  P .

chaitinClashCK :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
  (dCB : Deriv (imp KBCf KA)) ->
  (W : Term) ->
  Deriv (imp P (eqF (ap1 thmT W) (codeFormula KBCf))) ->
  Deriv (imp P (eqF (ap1 thmT (gFunAbs (ap2 Pair (natCode tag_mp) (ap2 Pair (encode dCB) W))))
                    codeFalse))
chaitinClashCK checkFires dCB W dProv =
  let wCB : Term
      wCB = encode dCB

      dCBprov : Deriv (eqF (ap1 thmT wCB) (codeFormula (imp KBCf KA)))
      dCBprov = thmT_complete_rec dCB

      W'' : Term
      W'' = ap2 Pair (natCode tag_mp) (ap2 Pair wCB W)

      -- Step 5 :  internal mp  =>  under P, T proves  KA .
      dMP : Deriv (imp P (eqF (ap1 thmT W'') (codeFormula KA)))
      dMP = imp_encoded_mp P wCB W (codeFormula KBCf) (codeFormula KA)
              (impLift {P} dCBprov) dProv

      -- bridge to the recogniser shape  KcodeAlph (natCode r) .
      bridge : Deriv (eqF (codeFormula KA) (ap1 KcodeAlph (natCode r)))
      bridge = ruleSym (KcodeAlph_correct r)

      dHit : Deriv (imp P (eqF (ap1 thmT W'') (ap1 KcodeAlph (natCode r))))
      dHit = imp_eqTrans_imp dMP (impLift {P} bridge)

      -- Step 6 core :  the ABSTRACT Chaitin-GI at  W'' .
      closerW : Deriv (imp (eqF (ap1 thmT W'') (ap1 KcodeAlph (ap1 outKdefAlph W'')))
                           (eqF (ap1 thmT (gFunAbs W'')) codeFalse))
      closerW = chaitinGI checkFires W''

      -- subject read-back  ( under P ) :  out W'' = natCode r .
      dBack : Deriv (imp P (eqF (ap1 outKdefAlph W'') (natCode r)))
      dBack = imp_outKdefAlph_correct P W'' (natCode r) dHit

      dCong : Deriv (imp P (eqF (ap1 KcodeAlph (natCode r))
                                (ap1 KcodeAlph (ap1 outKdefAlph W''))))
      dCong = impCong1 KcodeAlph (natCode r) (ap1 outKdefAlph W'') (impRuleSym dBack)

      dCloserHyp : Deriv (imp P (eqF (ap1 thmT W'')
                                     (ap1 KcodeAlph (ap1 outKdefAlph W''))))
      dCloserHyp = imp_eqTrans_imp dHit dCong
  in compI dCloserHyp closerW

------------------------------------------------------------------------
-- clos Step 6, FINISHED :  apply  ConOpenInt  ( global / open consistency )
-- at the diagonal  G W''  ( open in  x0 ), landing  imp P falseF .
--
--   clashFalseCK ... con :  Deriv (imp P falseF)        falseF = (0 = 1) .
--
-- With  P := charAtom  ( = Kr x0 = O )  this is  imp (Kr x0 = O) (0 = 1)  =
-- neg (Kr x0 = O)  ( = not (Kr x0 = O) ).

clashFalseCK :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
  (dCB : Deriv (imp KBCf KA)) ->
  (W : Term) ->
  Deriv (imp P (eqF (ap1 thmT W) (codeFormula KBCf))) ->
  ConOpenInt ->
  Deriv (imp P falseF)
clashFalseCK checkFires dCB W dProv con =
  let GW : Term
      GW = gFunAbs (ap2 Pair (natCode tag_mp) (ap2 Pair (encode dCB) W))

      dToFalseCode : Deriv (imp P (eqF (ap1 thmT GW) codeFalse))
      dToFalseCode = chaitinClashCK checkFires dCB W dProv

      conInst : Deriv (neg (eqF (ap1 thmT GW) codeFalse))
      conInst = ruleInst zero GW con

      conImp : Deriv (imp (eqF (ap1 thmT GW) codeFalse) falseF)
      conImp = negToImpFalse (eqF (ap1 thmT GW) codeFalse) conInst
  in compI dToFalseCode conImp
