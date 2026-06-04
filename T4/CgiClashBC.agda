{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashBC -- the Chaitin barrier (clash to falseF) at the framework's
-- KdefBigConj  shape.   The KdefBigConj analog of
-- T4.CompressComp.chaitinBarrierFinishComp , re-pointed from the single
-- computation-naming atom  atomComp  to the day-incompressibility formula
--
--   Inc = KdefBigConj M enum (natCode r)   ( "no enumerated short program
--   outputs day r" = K(r) > L ).
--
-- =====================================================================
-- THE CLASH (Kritchman-Raz, the two provabilities that collide).
-- =====================================================================
--
-- The recogniser/diagonal stack (T4.KdefBigConjRecog / *DischargeBC /
-- *ChainBC) detects T proving  Inc  ( the dNeg / incompressibility side ).
-- Eq. 2 ( compressibility is provable ) gives T proving  neg Inc  ( day r
-- IS compressible : the diagonal program -- being one of the enumerated
-- short programs -- outputs day r, a provable Sigma_1 run ).   The two
-- provabilities clash :
--
--   dExFGen Inc          :  T proves  Inc -> (neg Inc -> false)
--   dInc                 :  T proves  Inc                     [recogniser / input D]
--   mp1 = encoded_mp     :  T proves  (neg Inc -> false)
--   dComp                :  T proves  neg Inc                 [Eq. 2 / enum-id]
--   mp2 = encoded_mp     :  T proves  false
--   ConOpenInt           :  T does NOT prove  false           -> contradiction -> falseF .
--
-- This file ships the barrier  cgiClashConj  ( the final two-mp + axExFalso
-- + ConOpenInt step ) taking the two thmT-provability facts as typed
-- hypotheses ( the repo STOP-rule, hypothesis-first ).   It is the
-- KdefBigConj analog of  chaitinBarrierFinishComp , VERIFIED, reducing
-- kdefClash to exactly:
--   * dInc  ( "T proves Inc" ) -- producible from the input
--     D : imp K_rest Inc via  thmT_complete_rec + encoded_mp  against a
--     Sigma_1-lift  dKrest : "T proves K_rest[var0:=F]"  ( the Eq. 2
--     aggregation, T4.CompressComp.dPosComp + encoded_and + RunMono fuel-pin ),
--     AFTER instantiating  var 0 := F  ( the common halting fuel ) ;
--   * dComp ( "T proves neg Inc" ) -- the diagonal + enum-identification
--     ( gLcodeBC = enum k_* , outBC k_max = natCode r , RunMono/MaxFun ).
-- See  T4/SURPRISE-GII-BC-STACK-SHIPPED.md  for the var0/fuel entanglement.

module T4.CgiClashBC where

open import T4.Base
open import T4.Code           using ( codeFormula ; codeFalse ; falseF )
open import T4.ThmT           using ( thmT )
open import T4.Encode         using ( encode )
open import T4.DefWit         using ( cImp ; dExFGen )
open import T4.ConInj         using ( cmp )
open import T4.NegAtomCode    using ( NoVar_codeFormula )
open import T4.SubstNoVar     using ( substT_NoVar )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.SurpriseG2.KdefBigConj    using ( KdefBigConj )
open import T4.SurpriseG2.ConOpenIntDef  using ( ConOpenInt )

open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- The GENERAL consistency clash :  T proves P  +  T proves neg P  +  Con
-- ==>  falseF .   Shape-agnostic in  P  ( so it applies at the open-fuel
-- Inc, the fuel-instantiated  Inc[var0:=F], or any formula ) -- this is
-- the honest primitive ( T cannot prove a formula and its negation under
-- ConOpenInt ).   The KdefBigConj analog of  chaitinBarrierFinishComp 's
-- Stage-3 skeleton.

provesBothToFalse :
  (P : Formula) ->
  ConOpenInt ->
  (wP : Term) ->
  Deriv (eqF (ap1 thmT wP) (codeFormula P)) ->          -- T proves P
  (wNP : Term) ->
  Deriv (eqF (ap1 thmT wNP) (codeFormula (neg P))) ->    -- T proves neg P
  Deriv falseF
provesBothToFalse P con wP dP wNP dNP =
  let cExF : Term
      cExF = encode (axExFalso P falseF)

      -- T proves  P -> (neg P -> false) .
      dExF : Deriv (eqF (ap1 thmT cExF)
                        (cImp (codeFormula P)
                          (cImp (codeFormula (neg P)) codeFalse)))
      dExF = dExFGen P

      -- mp1 : T proves  (neg P -> false) .
      consImp : Term
      consImp = cImp (codeFormula (neg P)) codeFalse

      mp1 : Deriv (eqF (ap1 thmT (cmp cExF wP)) consImp)
      mp1 = encoded_mp cExF wP (codeFormula P) consImp dExF dP

      -- mp2 : T proves  false .
      finalProof : Term
      finalProof = cmp (cmp cExF wP) wNP

      mp2 : Deriv (eqF (ap1 thmT finalProof) codeFalse)
      mp2 = encoded_mp (cmp cExF wP) wNP
              (codeFormula (neg P)) codeFalse mp1 dNP

      -- Con refutes it.
      con_raw : Deriv (neg (eqF (ap1 thmT finalProof)
                                 (substT zero finalProof codeFalse)))
      con_raw = ruleInst zero finalProof con

      con_inst : Deriv (neg (eqF (ap1 thmT finalProof) codeFalse))
      con_inst = eqSubst (\ z -> Deriv (neg (eqF (ap1 thmT finalProof) z)))
                         (substT_NoVar zero finalProof codeFalse
                           (NoVar_codeFormula falseF))
                         con_raw
  in mp (mp (axExFalso (eqF (ap1 thmT finalProof) codeFalse) falseF) mp2) con_inst

------------------------------------------------------------------------
-- Weakening :  Deriv falseF  yields  imp K_rest falseF  for ANY antecedent.

weakenToImp : (K_rest : Formula) -> Deriv falseF -> Deriv (imp K_rest falseF)
weakenToImp K_rest dFalse = mp (axK falseF K_rest) dFalse

module _ (enum : Fun1) (M : Nat) (r : Nat) where

  ----------------------------------------------------------------------
  -- Inc = the day-r incompressibility formula ( open fuel  var 0 ).

  Inc : Formula
  Inc = KdefBigConj M enum (natCode r)

  -- The barrier at  Inc  : an instance of  provesBothToFalse .   dInc is
  -- "T proves Inc" ( the recogniser-detected provability, ultimately from
  -- the input  D : imp K_rest Inc  + the Sigma_1-lift of K_rest ) ; dComp
  -- is "T proves neg Inc" ( day r compressible : the diagonal program, an
  -- enumerated short program, outputs r -- a provable run ).
  cgiClashConj :
    ConOpenInt ->
    (wInc : Term) ->
    Deriv (eqF (ap1 thmT wInc) (codeFormula Inc)) ->
    (wComp : Term) ->
    Deriv (eqF (ap1 thmT wComp) (codeFormula (neg Inc))) ->
    Deriv falseF
  cgiClashConj con wInc dInc wComp dComp =
    provesBothToFalse Inc con wInc dInc wComp dComp
