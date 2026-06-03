{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BuildC1Gen -- GENERIC ( abstract  consts ) version of  T4.BuildC1 , so the
-- concrete enumerator is NEVER normalized under  encode / thmT_complete_rec
-- ( the sole cause of the >20s blowup in  T4.BuildC1 / T4.KdefClashAssembly ).
--
-- The module is parametrised by an ABSTRACT  consts : SurpriseConstsConj , so
--   enum := SurpriseConstsConj.enum consts  stays a stuck projection and
--   codeFun1 enum  ( inside  codeFormula KBCf ) never unfolds.
--
-- It supplies clos Steps 3-5 generically :
--   * buildPhiProv  ( Steps 3-4 :  encoded_mp of  Step2  against  KrestProv ) ;
--   * c1FromPhiProv ( Step 5 : internalise  coverBridge , the  dCB  INPUT ) ;
--   * buildC1       ( their composition ) .
--
-- IMPORTANT : the  C1 / PhiProv / KrestProv  "records" are  Sigma  ALIASES, NOT
-- dependent records.   A dependent record with a  Deriv (... thmT ...)  FIELD
-- makes Agda normalize  thmT 's giant value during record elaboration ( >20s,
-- enum-INDEPENDENT ) ;  a generic  Sg  keeps the  thmT -laden type under the  B
-- lambda, checked lazily ( cf.  T4.CgiClashImp.ImpSomeProof ,
-- feedback_specialised_record_typecheck_blowup ).
--
-- The concrete enumerator only enters when this module is instantiated at the
-- CKMargin  consts  in  T4.SurpriseGIIDone  ( the ONE >20s headline file ).

open import T4.Base

open import T4.SurpriseG2.ConstantsConj using ( SurpriseConstsConj )

module T4.BuildC1Gen
  (Lstar_meta : Nat)
  (consts     : SurpriseConstsConj)
  where

open import T4.Tags  using ( tag_mp )
open import T4.Num   using ( num )
open import T4.Code  using ( codeFormula )
open import T4.ThmT  using ( thmT )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.SbF   using ( sbf )
open import T4.DefWit using ( cImp )
open import T4.Step2  using ( step2 ; wrapped )

open import T4.KdefAlph Lstar_meta using ( KdefAlph ; KcodeAlph ; KcodeAlph_correct )

open import T4.SurpriseG2.BigConjFormula   using ( BigConjFormula )
open import T4.SurpriseG2.KdefBigConj      using ( KdefBigConj )
open import T4.SurpriseG2.StagePredFormula using ( Picks )
open import T4.KdefBigConjFuelBridge       using ( KdefBigConjF )

open import T4.Thm12.EncodedMp  using ( imp_encoded_mp )
open import T4.Thm12.ImpHelpers using ( impLift )
open import T4.ImpExtras        using ( imp_eqTrans_imp )

------------------------------------------------------------------------
-- A generic dependent pair ( NOT a thmT-laden record -- see header ).

record Sg (A : Set) (B : A -> Set) : Set where
  constructor mkSg
  field
    pr1 : A
    pr2 : B pr1

------------------------------------------------------------------------
-- The abstract constants ( stuck projections ).

enum : Fun1
enum = SurpriseConstsConj.enum consts
M : Nat
M = SurpriseConstsConj.M consts
N : Nat
N = SurpriseConstsConj.N consts

------------------------------------------------------------------------
-- The fixed num-installation spec  ( clos "replace x0 by num x0" ) and the
-- code of the day- r  K_rest .

spec0 : Term
spec0 = ap2 Pair (natCode zero) (ap1 num (var zero))

Kc : (r : Nat) (picks : Picks) -> Term
Kc r picks = codeFormula (BigConjFormula consts (suc r) picks)

------------------------------------------------------------------------
-- The honest Sigma_1 residual ( STOP-rule ) : "under K_rest, T proves the
-- num-installed K_rest-code at proof index  w2 " -- the per-day  picks  run-data.
--    pr1 = w2 (the proof index) ,  pr2 = the provability .

KrestProv : (r : Nat) (picks : Picks) -> Set
KrestProv r picks =
  Sg Term (\ w2 ->
    Deriv (imp (BigConjFormula consts (suc r) picks)
               (eqF (ap1 thmT w2) (ap2 sbf spec0 (Kc r picks)))))

------------------------------------------------------------------------
-- The Steps-3-4 output ( = the old  T4.BuildC1.PhiProv ).
--    pr1 = W1 ,  pr2 = the provability of the open-fuel- x1 conjunction.

PhiProv : (r : Nat) (picks : Picks) -> Set
PhiProv r picks =
  Sg Term (\ W1 ->
    Deriv (imp (BigConjFormula consts (suc r) picks)
               (eqF (ap1 thmT W1)
                    (codeFormula (KdefBigConjF enum (var (suc zero)) M (natCode r))))))

------------------------------------------------------------------------
-- The Step-5 output ( the input  T4.KdefClashReflect.reflectFalse  consumes ).
--    pr1 = W ,  pr2 = the recogniser-shape hit.

C1 : (r : Nat) (picks : Picks) -> Set
C1 r picks =
  Sg Term (\ W ->
    Deriv (imp (BigConjFormula consts (suc r) picks)
               (eqF (ap1 thmT W) (ap1 KcodeAlph (natCode r)))))

------------------------------------------------------------------------
-- The day- r  build.

module _ (r : Nat) (picks : Picks)
  (dComp : Deriv (imp (BigConjFormula consts (suc r) picks)
                      (KdefBigConj M enum (natCode r))))
  where

  Krest : Formula
  Krest = BigConjFormula consts (suc r) picks

  KBCf : Formula
  KBCf = KdefBigConjF enum (var (suc zero)) M (natCode r)

  Qc : Term
  Qc = codeFormula KBCf

  KA : Formula
  KA = KdefAlph (natCode r)

  wrp : Term
  wrp = wrapped consts r picks dComp

  -- clos Step 2  ( encode + x0 |-> num x0 ), generic in  consts .
  step2D : Deriv (eqF (ap1 thmT wrp) (cImp (ap2 sbf spec0 (Kc r picks)) Qc))
  step2D = step2 consts r picks dComp

  ------------------------------------------------------------------------
  -- Steps 3-4 :  encoded_mp  of  Step2  against the  K_rest  Sigma_1 run-data.

  buildPhiProv : KrestProv r picks -> PhiProv r picks
  buildPhiProv kp =
    mkSg (ap2 Pair (natCode tag_mp) (ap2 Pair wrp (Sg.pr1 kp)))
         (imp_encoded_mp Krest wrp (Sg.pr1 kp)
            (ap2 sbf spec0 (Kc r picks)) Qc
            (impLift {Krest} step2D)
            (Sg.pr2 kp))

  ------------------------------------------------------------------------
  -- Step 5 :  internalise  coverBridge  ( the  dCB  INPUT, kept abstract so
  -- the concrete enumerator is never normalized here ) and land  C1 .

  c1FromPhiProv : Deriv (imp KBCf KA) -> PhiProv r picks -> C1 r picks
  c1FromPhiProv dCB pp =
    let wCB : Term
        wCB = encode dCB

        dCBprov : Deriv (eqF (ap1 thmT wCB) (codeFormula (imp KBCf KA)))
        dCBprov = thmT_complete_rec dCB

        W1' : Term
        W1' = Sg.pr1 pp

        W : Term
        W = ap2 Pair (natCode tag_mp) (ap2 Pair wCB W1')

        dMP : Deriv (imp Krest (eqF (ap1 thmT W) (codeFormula KA)))
        dMP = imp_encoded_mp Krest wCB W1'
                (codeFormula KBCf) (codeFormula KA)
                (impLift {Krest} dCBprov)
                (Sg.pr2 pp)

        bridge : Deriv (eqF (codeFormula KA) (ap1 KcodeAlph (natCode r)))
        bridge = ruleSym (KcodeAlph_correct r)

        hit : Deriv (imp Krest (eqF (ap1 thmT W) (ap1 KcodeAlph (natCode r))))
        hit = imp_eqTrans_imp dMP (impLift {Krest} bridge)
    in mkSg W hit

  ------------------------------------------------------------------------
  -- The full day- r  build :  Steps 3-5 .

  buildC1 : Deriv (imp KBCf KA) -> KrestProv r picks -> C1 r picks
  buildC1 dCB kp = c1FromPhiProv dCB (buildPhiProv kp)
