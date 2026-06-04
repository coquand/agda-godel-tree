{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BuildC1 -- builds the day- r  incompressibility provability  C1  ( the
-- input  T4.KdefClashReflect.reflectFalse  consumes ) from the REFINED residual
-- dPhiProv  ( only the  K_rest  Sigma_1-part ), by INTERNALISING  coverBridge
-- as a provability step ( clos's "by enum correctness", Step 5 of the assembly ).
--
--   c1FromPhiProv :  PhiProv r picks  ->  C1 r picks
--
-- where
--   PhiProv r picks  carries a closed proof code  W1  with
--     Deriv (imp K_rest (thmT W1 = codeFormula (KdefBigConjF enum (var 1) M (natCode r)))) ,
--   i.e. "under K_rest, T proves the open-fuel- x1 incompressibility conjunction"
--   ( clos Steps 2-4 : encode the K_rest => KdefBigConjF proof, substitute
--   x0 |-> num x0 in its code, mp against the  picks  Sigma_1 run-data ).
--
-- This file does the REMAINING Step 5 :  encode  coverBridge  ( T-provable
-- KdefBigConjF => KdefAlph ),  imp_encoded_mp  to land  KdefAlph , and the
-- KcodeAlph_correct  bridge to the recogniser shape.

open import T4.Base
open import BRA3.ChurchLeq      using ( leq )
open import T4.KGodel1BridgeDef using ( Lstar )

module T4.BuildC1
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import T4.Tags  using ( tag_mp )
open import T4.Code   using ( codeFormula )
open import T4.ThmT   using ( thmT )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )

open import T4.KdefAlph Lstar_meta        using ( KdefAlph ; KcodeAlph ; KcodeAlph_correct )
open import T4.CoverBridgeAlph Lstar_meta using ( coverBridgeKdefAlph )

open import T4.SurpriseG2.ConstantsConj    using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.KdefBigConjFuelBridge       using ( KdefBigConjF )

open import T4.CKMargin Lstar_meta lstarLe using ( Bnat ; Bpos ; predEq )
open import T4.FrontToKdefAlph Lstar_meta lstarLe using ( consts )
open import T4.KdefClashAssembly Lstar_meta lstarLe using ( C1 ; N ; M ; enum )

open import T4.Thm12.EncodedMp using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift )
open import T4.ImpExtras using ( imp_eqTrans_imp )
open import BRA3.RuleInst2 using ( simSubstT )

------------------------------------------------------------------------
-- The refined residual.

-- NO closedness on  W1  ( the abstract Chaitin-GI closer takes any code ).
record PhiProv (r : Nat) (picks : Picks) : Set where
  field
    W1   : Term
    prov : Deriv (imp (BigConjFormula consts (suc r) picks)
                      (eqF (ap1 thmT W1)
                           (codeFormula (KdefBigConjF enum (var (suc zero)) M (natCode r)))))

------------------------------------------------------------------------
-- A small Pair-congruence helper.

pairCong :
  (x x' y y' : Term) -> Eq x x' -> Eq y y' ->
  Eq (ap2 Pair x y) (ap2 Pair x' y')
pairCong x x' y y' ex ey =
  eqTrans (eqCong (\ z -> ap2 Pair z y) ex) (eqCong (\ z -> ap2 Pair x' z) ey)

------------------------------------------------------------------------
-- Step 5 :  internalise  coverBridge  and land  C1 .

module _ (r : Nat) (picks : Picks) where

  Krest : Formula
  Krest = BigConjFormula consts (suc r) picks

  KBCf : Formula
  KBCf = KdefBigConjF enum (var (suc zero)) M (natCode r)

  KA : Formula
  KA = KdefAlph (natCode r)

  c1FromPhiProv : PhiProv r picks -> C1 r picks
  c1FromPhiProv pp =
    let
      dCB : Deriv (imp KBCf KA)
      dCB = coverBridgeKdefAlph M r (predEq Bnat Bpos)

      wCB : Term
      wCB = encode dCB

      -- thmT wCB = Pair tag_imp (Pair (codeFormula KBCf) (codeFormula KA)).
      dCBprov : Deriv (eqF (ap1 thmT wCB) (codeFormula (imp KBCf KA)))
      dCBprov = thmT_complete_rec dCB

      W1' : Term
      W1' = PhiProv.W1 pp

      W : Term
      W = ap2 Pair (natCode tag_mp) (ap2 Pair wCB W1')

      -- internal mp :  under K_rest, T proves  KA .
      dMP : Deriv (imp Krest (eqF (ap1 thmT W) (codeFormula KA)))
      dMP = imp_encoded_mp Krest wCB W1'
              (codeFormula KBCf) (codeFormula KA)
              (impLift {Krest} dCBprov)
              (PhiProv.prov pp)

      -- bridge  codeFormula KA = ap1 KcodeAlph (natCode r) .
      bridge : Deriv (eqF (codeFormula KA) (ap1 KcodeAlph (natCode r)))
      bridge = ruleSym (KcodeAlph_correct r)

      hit : Deriv (imp Krest (eqF (ap1 thmT W) (ap1 KcodeAlph (natCode r))))
      hit = imp_eqTrans_imp dMP (impLift {Krest} bridge)
    in record { W = W ; hit = hit }
