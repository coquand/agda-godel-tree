{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinWire2 -- clos Step 5 at the two-fuel shape ( x1 = var 1 free ).
--
-- Connects  Steps 1-4  ( frontEnd2 + DIncBC2.dInc2 , the recogniser-shape  dInc
-- at the OPEN fuel  var 1 ) to the SHIPPED Chaitin diagonal  DischargeBC /
-- ChainBC  at  fuel := var 1 .   The diagonal then chooses  x1  ( clos's point :
-- x1 stays free until the diagonal pins it ).   Outputs the two diagonal facts
--
--   dNeg_at_kmax  : thmT k_max = ap1 (KcodeBC enum (var 1) M) (outBC enum (var 1) M k_max)
--   dEval_witness : evalU (parse (enc (gLcodeBC enum (var 1) M))) nTerm = s (outBC ... k_max)
--
-- i.e.  T  proves day  x'  incompressible AND the diagonal program ( a short
-- program ) outputs  x' .   The remaining kernel ( clos Step 5's self-reference :
-- gLcodeBC = enum k_* , x' = natCode r ) turns this into the compressibility
-- proof  dComp  -- the irreducible long pole, left to the caller.
--
-- The substT-/simSubstT-closedness of  wInc  is carried as a hypothesis, exactly
-- as in the single-fuel substrate ( T4.ChaitinG1Core takes  Closed (encode d) /
-- sim_encD  as parameters ).

module T4.ChaitinWire2 where

open import T4.Base
open import BRA3.RuleInst2 using ( simSubstT )
open import T4.ThmT   using ( thmT )
open import T4.Code   using ( codeFormula )
open import T4.Encode using ( encode )
open import T4.ConInj using ( cmp )
open import T4.Code   using ( falseF ; codeFormula )
open import T4.KdefBigConjFuelBridge using ( KdefBigConjF ; numBridgeF_at )
open import T4.KdefBigConjRecog using ( KcodeBC ; outBC )
open import T4.CgiClashBC using ( provesBothToFalse )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
open import T4.KdefDiagBC using ( gLcodeBC )
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.ProgEnc using ( enc )
open import T4.DIncBC2 using ( dInc2 )
import T4.ChaitinG1DischargeBC
import T4.ChaitinG1ChainBC

module _ (enum : Fun1) (M : Nat) (r : Nat) (F0 : Term)
  (Krest : Formula)
  (D : Deriv (imp Krest (KdefBigConjF enum (var (suc zero)) M (natCode r))))
  (wKrest : Term)
  (dKrest : Deriv (eqF (ap1 thmT wKrest) (codeFormula (substF zero F0 Krest))))
  where

  wInc : Term
  wInc = cmp (encode (ruleInst zero F0 D)) wKrest

  hInc : Deriv (eqF (ap1 thmT wInc)
                    (ap1 (KcodeBC enum (var (suc zero)) M) (natCode r)))
  hInc = dInc2 enum M r F0 Krest D wKrest dKrest

  -- The closedness of the encoded proof  wInc  ( substrate hypotheses, cf.
  -- T4.ChaitinG1Core 's  Closed (encode d) / sim_encD ).
  module _
    (sub0_w : (a : Term) -> Eq (substT zero a wInc) wInc)
    (sub1_w : (a : Term) -> Eq (substT (suc zero) a wInc) wInc)
    (sim_w  : (a b : Term) -> Eq (simSubstT zero a (suc zero) b wInc) wInc)
    where

    module Disc =
      T4.ChaitinG1DischargeBC.DischargeBC enum (var (suc zero)) M wInc (natCode r)
        hInc sub0_w sub1_w sim_w
    module Chn =
      T4.ChaitinG1ChainBC.ChainBC enum (var (suc zero)) M wInc (natCode r)
        hInc sub0_w sub1_w sim_w

    -- clos Step 5 outputs ( x1 chosen by the diagonal ).   Types inferred.
    kmax = Disc.k_max
    xPrime = ap1 (outBC enum (var (suc zero)) M) Disc.k_max
    nTerm = Chn.nTerm

    -- T proves day  xPrime  is incompressible ( the recogniser-detected proof ).
    dNeg_at_kmax = Disc.dNeg_at_kmax

    -- the diagonal program ( a short program ) outputs  xPrime  in  nTerm  steps.
    dEval_witness = Chn.dEval_witness

    ----------------------------------------------------------------------
    -- The clos Step-6 BOUNDARY ( the SOLE remaining residual ).   Everything
    -- above is DERIVED ; the only thing missing is the self-referential
    -- enum-identification closer  ( gLcodeBC = enum k_* ,  outBC k_max =
    -- natCode r ) that turns the two derived diagonal facts into a
    -- contradiction.   Given that closer, the day-r clash is closed.

    clashViaClose :
      (Deriv (eqF (ap1 thmT Disc.k_max)
                  (ap1 (KcodeBC enum (var (suc zero)) M)
                       (ap1 (outBC enum (var (suc zero)) M) Disc.k_max))) ->
       Deriv (eqF (ap2 evalU (ap1 parse (enc (gLcodeBC enum (var (suc zero)) M))) Chn.nTerm)
                  (ap1 s (ap1 (outBC enum (var (suc zero)) M) Disc.k_max))) ->
       Deriv falseF) ->
      Deriv falseF
    clashViaClose close = close Disc.dNeg_at_kmax Chn.dEval_witness

    ----------------------------------------------------------------------
    -- The clos Step-6 CLASH, DERIVED from the two genuine kernel facts :
    --   * subjFix : outBC k_max = natCode r   ( the diagonal's read-off subject
    --     IS day r -- the Chaitin fixpoint ; consequence of the self-referential
    --     enum-identification ) ;
    --   * dComp   : "T proves neg Inc(r)"     ( day r compressible : the diagonal,
    --     a short enumerated program, outputs r -- a provable Sigma_1 run ).
    -- Given these, the recogniser-detected  dNeg_at_kmax  ( T proves Inc(r) )
    -- collides with  dComp  under  ConOpenInt  ->  falseF .   Everything ELSE
    -- ( dNeg_at_kmax , the numBridge ) is derived.

    clashFromFix :
      ConOpenInt ->
      Eq (ap1 (outBC enum (var (suc zero)) M) Disc.k_max) (natCode r) ->
      (wComp : Term) ->
      Deriv (eqF (ap1 thmT wComp)
                 (codeFormula (neg (KdefBigConjF enum (var (suc zero)) M (natCode r))))) ->
      Deriv falseF
    clashFromFix con subjFix wComp dComp =
      let Inc1 : Formula
          Inc1 = KdefBigConjF enum (var (suc zero)) M (natCode r)

          -- dNeg_at_kmax, subject rewritten  x' = outBC k_max  -> natCode r .
          dNegFix : Deriv (eqF (ap1 thmT Disc.k_max)
                               (ap1 (KcodeBC enum (var (suc zero)) M) (natCode r)))
          dNegFix = eqSubst (\ z -> Deriv (eqF (ap1 thmT Disc.k_max)
                                               (ap1 (KcodeBC enum (var (suc zero)) M) z)))
                            subjFix Disc.dNeg_at_kmax

          -- recogniser shape  ->  codeFormula : "T proves Inc(r)" .
          dIncCF : Deriv (eqF (ap1 thmT Disc.k_max) (codeFormula Inc1))
          dIncCF = ruleTrans dNegFix
                     (ruleSym (numBridgeF_at enum (var (suc zero)) M r))
      in provesBothToFalse Inc1 con Disc.k_max dIncCF wComp dComp
