{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageStepCGI --
--
-- The CGI / consistency core of the surprise-G2 inductive step
-- (T4/clos lines 33-45), witness-imp-lifted at the free Carneiro slot
-- var 2 .   Given  S(r)  (front end), the size-exhaustiveness bridge
-- and the open-consistency hypothesis ConOpenInt, produce
--
--   Deriv (imp Rf falseF)         where  Rf = eqF (thmT (var 2)) (codeFormula K_rest)
--
-- with  K_rest = BigConjFormula consts (suc r) picks .
--
-- Chain (only enum [= abstract consts] + sizeExhaust assumed; everything
-- else SHIPPED):
--   C  impTrans frontEnd (sizeExhaust r) :  imp K_rest (Kdef Lstar (natCode r))
--   D  thmT_complete_rec                 :  thmT (encode dC) = code (imp K_rest (Kdef Lstar (natCode r)))
--   E  imp_encoded_mp under Rf           :  imp Rf (thmT W = code (Kdef Lstar (natCode r)))
--   F  ruleInst-closeW + Kcode_correct + imp_outKdef_correct
--                                        :  imp Rf (thmT (closeW W) = Kcode Lstar (outKdef Lstar (closeW W)))
--   G  cgFalseImp                        :  imp Rf (thmT (cgFun W) = codeFalse)
--   H  ConOpenInt (ruleInst) + impTrans  :  imp Rf falseF

module T4.SurpriseG2.StageStepCGI where

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; simSubstF ; simSubstT )
open import BRA3.Logic              using ( impTrans )
open import BRA3.Contrapositive     using ( axExFalso ; liftP ; bComb )

open import T4.Code               using ( codeFalse ; falseF ; codeFormula )
open import T4.Tags               using ( tag_imp ; tag_mp )
open import T4.ThmT               using ( thmT )
open import T4.Kdef               using ( Kdef ; Kcode ; Kcode_correct )
open import T4.KdefRecog          using ( outKdef )
open import T4.KGodel1BridgeDef   using ( Lstar )
open import T4.CgFun              using ( cgFun )
open import T4.CloseW             using ( closeW )
open import T4.CgFalseImp         using ( cgFalseImp )
open import T4.Encode             using ( encode )
open import T4.ThmTCompleteRec    using ( thmT_complete_rec )
open import T4.ImpOutKdef         using ( imp_outKdef_correct )
open import T4.SubstNoVar         using ( substT_NoVar )
open import T4.NegAtomCode        using ( NoVar_codeFormula )
open import T4.Thm12.EncodedMp    using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers
  using ( impRefl ; impLift ; impEqTrans ; impCong1 ; impRuleSym )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; mkAnd )

open import T4.SurpriseG2.ConstantsConj  using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj    using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( StagePredF ; Picks ; PicksBound )
open import T4.SurpriseG2.StepFrontEnd    using ( frontEnd )

------------------------------------------------------------------------
-- simSubstT is the identity on closed (NoVar) Terms (mirror of
-- T4.SubstNoVar.substT_NoVar ).

simSubstT_NoVar :
  (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term) (s : Term) ->
  NoVar s -> Eq (simSubstT k1 t1 k2 t2 s) s
simSubstT_NoVar k1 t1 k2 t2 O           _             = refl
simSubstT_NoVar k1 t1 k2 t2 (var m)     ()
simSubstT_NoVar k1 t1 k2 t2 (ap1 f a)   nv            =
  eqCong (ap1 f) (simSubstT_NoVar k1 t1 k2 t2 a nv)
simSubstT_NoVar k1 t1 k2 t2 (ap2 g a b) (mkAnd na nb) =
  eqTrans (eqCong (\ z -> ap2 g z (simSubstT k1 t1 k2 t2 b))
                  (simSubstT_NoVar k1 t1 k2 t2 a na))
          (eqCong (\ z -> ap2 g a z) (simSubstT_NoVar k1 t1 k2 t2 b nb))

------------------------------------------------------------------------
-- The Carneiro witness fact  Rf  for a given  K_rest .

RfOf : Formula -> Formula
RfOf Krest = eqF (ap1 thmT (var (suc (suc zero)))) (codeFormula Krest)

------------------------------------------------------------------------
-- Force closure of the thmT witness via two  ruleInst -s at  O  ( = the
-- num-raw closeW trick), rewriting the closed spectators  Rf  and  C  back.

closeWitnessImp :
  (Rf : Formula) (t Ctm : Term) ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a : Term) -> Eq (substT zero a Ctm) Ctm) ->
  ((a : Term) -> Eq (substT (suc zero) a Ctm) Ctm) ->
  Deriv (imp Rf (eqF (ap1 thmT t) Ctm)) ->
  Deriv (imp Rf (eqF (ap1 thmT (closeW t)) Ctm))
closeWitnessImp Rf t Ctm sub0R sub1R sub0C sub1C d =
  let d1raw : Deriv (substF (suc zero) O (imp Rf (eqF (ap1 thmT t) Ctm)))
      d1raw = ruleInst (suc zero) O d
      d1a : Deriv (imp (substF (suc zero) O Rf)
                        (eqF (ap1 thmT (substT (suc zero) O t)) Ctm))
      d1a = eqSubst (\ cc -> Deriv (imp (substF (suc zero) O Rf)
                                         (eqF (ap1 thmT (substT (suc zero) O t)) cc)))
                    (sub1C O) d1raw
      d1 : Deriv (imp Rf (eqF (ap1 thmT (substT (suc zero) O t)) Ctm))
      d1 = eqSubst (\ G -> Deriv (imp G (eqF (ap1 thmT (substT (suc zero) O t)) Ctm)))
                   (sub1R O) d1a

      d2raw : Deriv (substF zero O (imp Rf (eqF (ap1 thmT (substT (suc zero) O t)) Ctm)))
      d2raw = ruleInst zero O d1
      d2a : Deriv (imp (substF zero O Rf)
                        (eqF (ap1 thmT (substT zero O (substT (suc zero) O t))) Ctm))
      d2a = eqSubst (\ cc -> Deriv (imp (substF zero O Rf)
                                         (eqF (ap1 thmT (substT zero O (substT (suc zero) O t))) cc)))
                    (sub0C O) d2raw
  in eqSubst (\ G -> Deriv (imp G (eqF (ap1 thmT (substT zero O (substT (suc zero) O t))) Ctm)))
             (sub0R O) d2a

------------------------------------------------------------------------
-- neg X  ->  imp X falseF  ( axExFalso + bComb ) .

negToImpFalse : (X : Formula) -> Deriv (neg X) -> Deriv (imp X falseF)
negToImpFalse X dn = bComb (axExFalso X falseF) (liftP X dn)

------------------------------------------------------------------------
-- The CGI/consistency core .

cgiClashImpRf :
  (consts : SurpriseConstsConj) (r : Nat) ->
  NatLe r (SurpriseConstsConj.N consts) ->
  StagePredF consts r ->
  ((rr : Nat) -> Deriv (imp (KdefBigConj (SurpriseConstsConj.M consts)
                                          (SurpriseConstsConj.enum consts) (natCode rr))
                             (Kdef Lstar (natCode rr)))) ->
  Deriv (neg (eqF (ap1 thmT (var zero)) codeFalse)) ->
  (picks : Picks) (bound : PicksBound consts picks) ->
  Deriv (imp (RfOf (BigConjFormula consts (suc r) picks)) falseF)
cgiClashImpRf consts r rleN Sr sizeExhaust conInt picks bound =
  let M : Nat
      M = SurpriseConstsConj.M consts
      enum : Fun1
      enum = SurpriseConstsConj.enum consts

      Krest : Formula
      Krest = BigConjFormula consts (suc r) picks

      Rf : Formula
      Rf = RfOf Krest

      -- C : imp K_rest (Kdef Lstar (natCode r)) .
      dC : Deriv (imp Krest (Kdef Lstar (natCode r)))
      dC = impTrans (frontEnd consts r rleN Sr picks bound) (sizeExhaust r)

      consPart : Term
      consPart = codeFormula (Kdef Lstar (natCode r))

      -- D : encode dC .
      w0 : Term
      w0 = encode dC

      dD : Deriv (eqF (ap1 thmT w0)
                       (codeFormula (imp Krest (Kdef Lstar (natCode r)))))
      dD = thmT_complete_rec dC

      -- E : encoded mp under Rf .   imp_ih_a = impRefl Rf .
      W : Term
      W = ap2 Pair (natCode tag_mp) (ap2 Pair w0 (var (suc (suc zero))))

      dE : Deriv (imp Rf (eqF (ap1 thmT W) consPart))
      dE = imp_encoded_mp Rf w0 (var (suc (suc zero)))
                          (codeFormula Krest) consPart
                          (impLift {Rf} dD) (impRefl Rf)

      -- Rf-closedness witnesses ( var 2 untouched ;  codeFormula Krest closed ) .
      sub0_Rf : (a : Term) -> Eq (substF zero a Rf) Rf
      sub0_Rf a =
        eqCong (\ z -> eqF (ap1 thmT (var (suc (suc zero)))) z)
               (substT_NoVar zero a (codeFormula Krest) (NoVar_codeFormula Krest))
      sub1_Rf : (a : Term) -> Eq (substF (suc zero) a Rf) Rf
      sub1_Rf a =
        eqCong (\ z -> eqF (ap1 thmT (var (suc (suc zero)))) z)
               (substT_NoVar (suc zero) a (codeFormula Krest) (NoVar_codeFormula Krest))
      sim_Rf : (a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf
      sim_Rf a b =
        eqCong (\ z -> eqF (ap1 thmT (var (suc (suc zero)))) z)
               (simSubstT_NoVar zero a (suc zero) b (codeFormula Krest)
                                (NoVar_codeFormula Krest))

      -- consPart closedness ( for closeWitnessImp ) .
      sub0_C : (a : Term) -> Eq (substT zero a consPart) consPart
      sub0_C a = substT_NoVar zero a consPart (NoVar_codeFormula (Kdef Lstar (natCode r)))
      sub1_C : (a : Term) -> Eq (substT (suc zero) a consPart) consPart
      sub1_C a = substT_NoVar (suc zero) a consPart (NoVar_codeFormula (Kdef Lstar (natCode r)))

      -- F : close the witness and bridge to the Kcode / outKdef shape .
      dE_closed : Deriv (imp Rf (eqF (ap1 thmT (closeW W)) consPart))
      dE_closed = closeWitnessImp Rf W consPart sub0_Rf sub1_Rf sub0_C sub1_C dE

      dE2 : Deriv (imp Rf (eqF (ap1 thmT (closeW W)) (ap1 (Kcode Lstar) (natCode r))))
      dE2 = impEqTrans (ap1 thmT (closeW W)) consPart (ap1 (Kcode Lstar) (natCode r))
              dE_closed
              (impLift {Rf} (ruleSym (Kcode_correct Lstar r)))

      readback : Deriv (imp Rf (eqF (ap1 (outKdef Lstar) (closeW W)) (natCode r)))
      readback = imp_outKdef_correct Rf Lstar (closeW W) (natCode r) dE2

      congKcode :
        Deriv (imp Rf (eqF (ap1 (Kcode Lstar) (natCode r))
                            (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW W)))))
      congKcode =
        impCong1 {Rf} (Kcode Lstar) (natCode r) (ap1 (outKdef Lstar) (closeW W))
                 (impRuleSym {Rf} readback)

      dF : Deriv (imp Rf (eqF (ap1 thmT (closeW W))
                               (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW W)))))
      dF = impEqTrans (ap1 thmT (closeW W)) (ap1 (Kcode Lstar) (natCode r))
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW W)))
             dE2 congKcode

      -- G : the Berry clash .
      dG : Deriv (imp Rf (eqF (ap1 thmT (cgFun W)) codeFalse))
      dG = cgFalseImp Rf W sub0_Rf sub1_Rf sim_Rf dF

      -- H : consistency at  cgFun W .
      conAt_raw : Deriv (neg (eqF (ap1 thmT (cgFun W)) (substT zero (cgFun W) codeFalse)))
      conAt_raw = ruleInst zero (cgFun W) conInt

      conAt : Deriv (neg (eqF (ap1 thmT (cgFun W)) codeFalse))
      conAt = eqSubst (\ z -> Deriv (neg (eqF (ap1 thmT (cgFun W)) z)))
                      (substT_NoVar zero (cgFun W) codeFalse (NoVar_codeFormula falseF))
                      conAt_raw

      conImp : Deriv (imp (eqF (ap1 thmT (cgFun W)) codeFalse) falseF)
      conImp = negToImpFalse (eqF (ap1 thmT (cgFun W)) codeFalse) conAt
  in impTrans dG conImp
