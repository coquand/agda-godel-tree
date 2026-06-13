{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.LobProvable -- Loeb's theorem stated with the OBJECT-LEVEL provability
-- predicate  Provable A = E (provFun A)  ( T4.Provable ) instead of the open
-- thmT-atom :
--
--   lobProvable A (nf1 : notFreeF 1 A) :
--     Deriv (imp (Provable A) A)  ->  Deriv A
--
-- "if  T  proves  Provable A => A , then  T  proves  A " -- Loeb's rule with the
-- genuine closed Sigma-1 provability sentence  Provable A  ( = "exists x. thmT x
-- = code A" ).
--
-- Derived from the existing thmT-atom Loeb  T4.Lob.lobThm1  by the bridge
--   ( thmT(var 1) = code A )  =>  Provable A
-- ( provFun A (var 1) = O  iff  thmT(var 1) = code A , then the object
-- exists-introduction axiom  eIntroAx ), which converts an  imp (Provable A) A
-- hypothesis into the open-atom Loeb hypothesis  lobThm1  consumes.

module T4.LobProvable where

open import T4.Base
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula )
open import T4.NegAtomCode using ( NoVar_codeFormula )
open import T4.CodeCantorCollapse using ( natEqF_codeF_refl )
open import T4.Thm12.ConstTermFun1 using ( constTermFun1 ; constTermFun1_eq )
open import T4.NotFree using ( notFree_above_F )
open import T4.Provable using ( provFun ; Provable )
open import T4.Lob using ( lobThmK )

open import BRA3.RuleInst2 using ( maxVarF ; le-refl )

open import T4.Thm12.ImpHelpers
  using ( impRefl ; impLift ; impEqTrans ; impCongL ; impCongR )

open import BRA3.Church using ( sub )
open import BRA3.SubT.NatEq using ( natEqF )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.Logic using ( impTrans )

------------------------------------------------------------------------
-- The arithmetic of  provFun :  ( thmT x = code A )  =>  ( provFun A x = O ) .
-- ( The necessitation computation, lifted to an object implication. )

provFun_imp_O :
  (A : Formula) (x : Term) ->
  Deriv (imp (eqF (ap1 thmT x) (codeFormula A))
             (eqF (ap1 (provFun A) x) O))
provFun_imp_O A x =
  let cA : Term
      cA = codeFormula A
      P : Formula
      P = eqF (ap1 thmT x) cA
      h2 : Fun1
      h2 = C natEqF thmT (constTermFun1 cA)

      -- provFun A x = sub (s O) (natEqF (thmT x) cA)   ( unconditional ).
      e2 : Deriv (eqF (ap1 (provFun A) x)
                      (ap2 sub (ap1 s O) (ap2 natEqF (ap1 thmT x) cA)))
      e2 =
        let e1 = ax_C sub (constTermFun1 (ap1 s O)) h2 x
            h1_eq = constTermFun1_eq (ap1 s O) tt x
            h2_eq = ruleTrans (ax_C natEqF thmT (constTermFun1 cA) x)
                      (congR natEqF (ap1 thmT x)
                        (constTermFun1_eq cA (NoVar_codeFormula A) x))
        in ruleTrans e1
             (ruleTrans (congL sub (ap1 h2 x) h1_eq) (congR sub (ap1 s O) h2_eq))

      -- under P :  natEqF (thmT x) cA = s O .
      natEqF_imp : Deriv (imp P (eqF (ap2 natEqF (ap1 thmT x) cA) (ap1 s O)))
      natEqF_imp =
        impEqTrans (ap2 natEqF (ap1 thmT x) cA) (ap2 natEqF cA cA) (ap1 s O)
          (impCongL natEqF (ap1 thmT x) cA cA (impRefl P))
          (impLift {P} (natEqF_codeF_refl A))
  in impEqTrans (ap1 (provFun A) x)
       (ap2 sub (ap1 s O) (ap2 natEqF (ap1 thmT x) cA)) O
       (impLift {P} e2)
       (impEqTrans (ap2 sub (ap1 s O) (ap2 natEqF (ap1 thmT x) cA))
         (ap2 sub (ap1 s O) (ap1 s O)) O
         (impCongR sub (ap2 natEqF (ap1 thmT x) cA) (ap1 s O) (ap1 s O) natEqF_imp)
         (impLift {P} (sub_self (ap1 s O))))

------------------------------------------------------------------------
-- The bridge  ( thmT(var k) = code A )  =>  Provable A  ( exists-intro ),
-- at ANY proof-variable index  k .

provBridge :
  (A : Formula) (k : Nat) ->
  Deriv (imp (eqF (ap1 thmT (var k)) (codeFormula A)) (Provable A))
provBridge A k =
  impTrans (provFun_imp_O A (var k))
           (eIntroAx (provFun A) (var k))

------------------------------------------------------------------------
-- LOEB'S THEOREM with  Provable -- NO freshness hypothesis on  A  ( Provable A
-- is CLOSED ).   The proof variable is taken FRESH ( k = maxVarF A , so
-- notFreeF k A holds automatically ), and  lobThmK  needs nothing more.

lobProvable :
  (A : Formula) ->
  Deriv (imp (Provable A) A) ->
  Deriv A
lobProvable A hNew =
  let k : Nat
      k = maxVarF A
  in lobThmK A k (notFree_above_F k A (le-refl k))
       (impTrans (provBridge A k) hNew)
