{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefClash2 -- the TWO-FUEL day-r Chaitin clash ( handoff
-- T4/SURPRISE-GII-TWOVAR-HANDOFF.md section 4 ).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- Wires  T4.StepFrontEnd2.frontEnd2 's two-fuel object implication
--
--   D : imp K_rest (KdefBigConjF enum (var 1) M (natCode r))        ( K_rest @ x0 , phi @ x1 )
--
-- into the consistency barrier  T4.CgiClashBC.provesBothToFalse  with the two
-- fuels instantiated INDEPENDENTLY :
--   * the antecedent  K_rest 's fuel  x0 = var 0  := F0  ( the common  picks
--     halting bound ) , so the Sigma_1-lift  dKrest  ( "T proves K_rest[F0]" )
--     is honest ;
--   * the consequent  phi 's fuel  x1 = var 1  := F1  ( the diagonal's halt
--     time  nTerm ) , so the day-incompressibility  Inc[F1]  is the formula the
--     diagonal refutes.
-- This is exactly the independence the single-fuel  frontEnd  could not give
-- (`ruleInst 0 F` there pins BOTH fuels).
--
--   kdefClash2 K_rest con D wKrest dKrest wComp dComp : Deriv (imp K_rest falseF)
--
-- reducing the per-step clash to exactly the two genuinely-EXTERNAL facts ( the
-- repo hypothesis-first STOP rule ) :
--   * dKrest : "T proves K_rest[var0:=F0, var1:=F1]"   ( Kritchman-Raz Eq. 2 :
--     each closed run  runProg (enum (picks d)) F0 = s (natCode d)  is provable
--     -- T4.CompressComp.dPosComp + the SHIPPED formula-level fuel pin
--     T4.RunProgMono.runProgMonoPlus -- aggregated by  encoded_and ) ;
--   * dComp  : "T proves neg Inc[F1]"   ( the diagonal program, an enumerated
--     short program, outputs day r : the enum-identification long pole, via
--     T4.ChaitinG1DischargeBC / *ChainBC  fed by  dInc ).
-- Everything BETWEEN them ( produce  dInc  from  D + dKrest , then clash ) is
-- DERIVED here, no holes/postulates.

module T4.KdefClash2 where

open import T4.Base
open import T4.Code            using ( codeFormula ; falseF )
open import T4.Kdef            using ( runProg )
open import T4.ThmT            using ( thmT )
open import T4.Encode          using ( encode )
open import T4.ConInj          using ( cmp )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.SubstNoVar      using ( substT_NoVar )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; NoVar_natCode )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF )
open import T4.CgiClashBC      using ( provesBothToFalse ; weakenToImp )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )

module _ (enum : Fun1) (M : Nat) (r : Nat) (F0 F1 : Term) (nvF1 : NoVar F1) where

  ----------------------------------------------------------------------
  -- The two fuel formulae.

  phiOpen : Formula                       -- phi @ x1 = var 1  ( frontEnd2 output )
  phiOpen = KdefBigConjF enum (var (suc zero)) M (natCode r)

  phiF1 : Formula                         -- phi @ F1  ( the diagonal's target )
  phiF1 = KdefBigConjF enum F1 M (natCode r)

  ----------------------------------------------------------------------
  -- SECTION 1.  Distribution :  substF 0 F0 (substF 1 F1 phiOpen) = phiF1 .
  --   The fuel slot  var 1  becomes  F1  ( reduction ) ; then  substF 0 F0
  --   is vacuous on the result ( var 0 absent ; the  natCode  leaves and  F1
  --   are  NoVar ).   By induction on  M , using  substT_NoVar  on the stuck
  --   closed sub-terms.

  -- per-conjunct, step 1 :  var 1 -> F1 .
  dist1_pp : (k : Nat) ->
    Eq (substF (suc zero) F1 (perProgNegF enum (var (suc zero)) (natCode r) k))
       (perProgNegF enum F1 (natCode r) k)
  dist1_pp k =
    eqTrans
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum z) F1)
                               (ap1 s (substT (suc zero) F1 (natCode r)))))
              (substT_NoVar (suc zero) F1 (natCode k) (NoVar_natCode k)))
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum (natCode k)) F1) (ap1 s z)))
              (substT_NoVar (suc zero) F1 (natCode r) (NoVar_natCode r)))

  -- per-conjunct, step 2 :  substF 0 F0  vacuous ( var 0 absent ;  F1 ,  natCode  NoVar ).
  dist0_pp : (k : Nat) ->
    Eq (substF zero F0 (perProgNegF enum F1 (natCode r) k))
       (perProgNegF enum F1 (natCode r) k)
  dist0_pp k =
    eqTrans
      (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum z) (substT zero F0 F1))
                               (ap1 s (substT zero F0 (natCode r)))))
              (substT_NoVar zero F0 (natCode k) (NoVar_natCode k)))
      (eqTrans
        (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum (natCode k)) z)
                                 (ap1 s (substT zero F0 (natCode r)))))
                (substT_NoVar zero F0 F1 nvF1))
        (eqCong (\ z -> neg (eqF (ap2 runProg (ap1 enum (natCode k)) F1) (ap1 s z)))
                (substT_NoVar zero F0 (natCode r) (NoVar_natCode r))))

  dist1 : (m : Nat) ->
    Eq (substF (suc zero) F1 (KdefBigConjF enum (var (suc zero)) m (natCode r)))
       (KdefBigConjF enum F1 m (natCode r))
  dist1 zero    = dist1_pp zero
  dist1 (suc m) =
    eqTrans
      (eqCong (\ H -> neg (imp H
                            (neg (substF (suc zero) F1
                                    (KdefBigConjF enum (var (suc zero)) m (natCode r))))))
              (dist1_pp (suc m)))
      (eqCong (\ T -> neg (imp (perProgNegF enum F1 (natCode r) (suc m)) (neg T)))
              (dist1 m))

  dist0 : (m : Nat) ->
    Eq (substF zero F0 (KdefBigConjF enum F1 m (natCode r)))
       (KdefBigConjF enum F1 m (natCode r))
  dist0 zero    = dist0_pp zero
  dist0 (suc m) =
    eqTrans
      (eqCong (\ H -> neg (imp H
                            (neg (substF zero F0 (KdefBigConjF enum F1 m (natCode r))))))
              (dist0_pp (suc m)))
      (eqCong (\ T -> neg (imp (perProgNegF enum F1 (natCode r) (suc m)) (neg T)))
              (dist0 m))

  distPhi :
    Eq (substF zero F0 (substF (suc zero) F1 phiOpen)) phiF1
  distPhi = eqTrans (eqCong (substF zero F0) (dist1 M)) (dist0 M)

  ----------------------------------------------------------------------
  -- SECTION 2.  The clash.   D ( frontEnd2 ) instantiated at BOTH fuels gives
  --   "T proves (K_rest[F0,F1] -> phi[F1])" ; encoded_mp vs  dKrest  gives
  --   "T proves phi[F1]" = dInc ; the barrier collides it with  dComp .

  kdefClash2 :
    (K_rest : Formula) ->
    ConOpenInt ->
    Deriv (imp K_rest phiOpen) ->                                  -- D  ( frontEnd2 )
    (wKrest : Term) ->
    Deriv (eqF (ap1 thmT wKrest)
               (codeFormula (substF zero F0 (substF (suc zero) F1 K_rest)))) ->  -- dKrest
    (wComp : Term) ->
    Deriv (eqF (ap1 thmT wComp) (codeFormula (neg phiF1))) ->       -- dComp
    Deriv (imp K_rest falseF)
  kdefClash2 K_rest con D wKrest dKrest wComp dComp =
    let KrestFF : Formula
        KrestFF = substF zero F0 (substF (suc zero) F1 K_rest)
        phiSub : Formula
        phiSub = substF zero F0 (substF (suc zero) F1 phiOpen)

        -- D instantiated at  var 1 := F1  then  var 0 := F0 .
        D2 : Deriv (imp KrestFF phiSub)
        D2 = ruleInst zero F0 (ruleInst (suc zero) F1 D)

        -- "T proves (K_rest[F0,F1] -> phi[F0,F1])" .
        dImp : Deriv (eqF (ap1 thmT (encode D2))
                          (codeFormula (imp KrestFF phiSub)))
        dImp = thmT_complete_rec D2

        -- "T proves phi[F0,F1]" .
        wInc : Term
        wInc = cmp (encode D2) wKrest
        mpd : Deriv (eqF (ap1 thmT wInc) (codeFormula phiSub))
        mpd = encoded_mp (encode D2) wKrest (codeFormula KrestFF) (codeFormula phiSub)
                dImp dKrest

        -- identify  phi[F0,F1] = phiF1  ( distribution ) :  dInc .
        dInc : Deriv (eqF (ap1 thmT wInc) (codeFormula phiF1))
        dInc = eqSubst (\ C -> Deriv (eqF (ap1 thmT wInc) C))
                       (eqCong codeFormula distPhi) mpd
    in weakenToImp K_rest (provesBothToFalse phiF1 con wInc dInc wComp dComp)
