{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Step2CK -- surprise-GII task (c): Step 2 = encode (both vars CODED) then
-- install the num-raw subject by selective object substitution.
-- (clos-corrected.md §"Step 2", the corrected encode-then-substitute.)
--
-- The CK-route Step-1 output is the OPEN implication ( x0 = subject , x1 =
-- run-length , BOTH bare arguments of the closed characteristic sections ) :
--
--   d : Deriv (imp (eqF (ap2 CKa (var x0) (var x1)) O)
--                  (eqF (ap2 CKc (var x0) (var x1)) O))
--
-- ( CKa = K_{r+1} 's section , CKc = C_r 's section ; both  ap2 CK u x = O  in
--   characteristic-function form, subject a BARE argument -- clos's "one
--   definitional condition", so  num  is NOT baked in before encoding ).
--
-- Step 2a ( uniform completeness encode ).   w0 := encode d , and
-- thmT_complete_rec  gives  thmT w0 = codeFormula (stepFormula)  which is
-- DEFINITIONALLY the open code  cImp (cEqTm (cAp2f CKa (cVarc x0) (cVarc x1)) O)
-- (...CKc...)  -- both variables are bare  cVarc  leaves ( codeTerm (var k) =
-- cVarc k ), NO asymmetry.
--
-- Step 2b ( install num-raw subject ).   wrap  w := pi tag_sb (pi spec0 w0)
-- with  spec0 = Pair (natCode x0) (ap1 num (var x0)) , and reduce by
-- thmT_at_sb + sbt_at_var_match  ( cVarc x0 -> ap1 num (var x0) , in BOTH the
-- antecedent and the consequent ) + sbt_at_var_nomatch  ( cVarc x1 untouched ) :
--
--   thmT w = cImp (cEqTm (cAp2f CKa (ap1 num (var x0)) (cVarc x1)) O)
--                 (cEqTm (cAp2f CKc (ap1 num (var x0)) (cVarc x1)) O)
--
-- the subject now num-raw ( recogniser-readable by  decode (ap1 num x0) = x0 ;
-- cf.  T4.CKRecog.outCK_correct ) , the run-length still the coded  cVarc x1 .
-- Precedent: the single-atom  T4.CgiClash  does the identical wrap-and-
-- substitute ( passK / thmT_at_sb ) for its program/fuel slots.

module T4.Step2CK where

open import T4.Base
open import T4.Tags using ( tag_sb ; tag_var )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.Encode using ( encode )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.SbStep using
  ( sbf_step_imp ; sbf_step_atomic ; sbt_step_ap2 ; ncO ; sbt_inert_NumCode )
open import T4.DefWit using ( cEqTm ; cImp )
open import T4.CgiClash using ( cAp2f ; cVarc )

open import BRA3.Church using ( pi )
open import BRA3.Base   using ( natEq )

-- CKa = K_{r+1} 's section ;  CKc = C_r 's section ;  x0 = subject var index ;
-- x1 = run-length var index ;  x0x1 :  x0 /= x1  ( so the run-length slot is
-- left coded by  sbt_at_var_nomatch ).
module _ (CKa CKc : Fun2) (x0 x1 : Nat)
         (x0x1 : Eq (natEq x0 x1) false)
  where

  ------------------------------------------------------------------------
  -- SECTION 0.  The Step-1 formula, the substituent, and the code targets.

  stepFormula : Formula
  stepFormula =
    imp (eqF (ap2 CKa (var x0) (var x1)) O)
        (eqF (ap2 CKc (var x0) (var x1)) O)

  -- the num-raw subject installed by the substitution.
  S0 : Term
  S0 = ap1 num (var x0)

  spec0 : Term
  spec0 = ap2 Pair (natCode x0) S0

  -- one atom's open / num-subject code ( for a given section  CKf ).
  atomOpen : Fun2 -> Term
  atomOpen CKf = cEqTm (cAp2f CKf (cVarc x0) (cVarc x1)) O

  atomNum : Fun2 -> Term -> Term
  atomNum CKf subjT = cEqTm (cAp2f CKf subjT (cVarc x1)) O

  impOpenCode : Term
  impOpenCode = cImp (atomOpen CKa) (atomOpen CKc)

  impNumCode : Term -> Term
  impNumCode subjT = cImp (atomNum CKa subjT) (atomNum CKc subjT)

  ------------------------------------------------------------------------
  -- SECTION 1.  The selective substitution pass over one atom.
  --   sbf spec0 (atomOpen CKf) = atomNum CKf S0   ( subject  cVarc x0 -> S0 ,
  --   run-length  cVarc x1  kept , O inert ).

  passAtom :
    (CKf : Fun2) ->
    Deriv (eqF (ap2 sbf spec0 (atomOpen CKf)) (atomNum CKf S0))
  passAtom CKf =
    let eSubj : Deriv (eqF (ap2 sbt spec0 (cVarc x0)) S0)
        eSubj = sbt_at_var_match x0 S0

        eRun : Deriv (eqF (ap2 sbt spec0 (cVarc x1)) (cVarc x1))
        eRun = sbt_at_var_nomatch x0 x1 S0 x0x1

        eAtomL : Deriv (eqF (ap2 sbt spec0 (cAp2f CKf (cVarc x0) (cVarc x1)))
                             (cAp2f CKf S0 (cVarc x1)))
        eAtomL = sbt_step_ap2 x0 S0 CKf (cVarc x0) (cVarc x1) S0 (cVarc x1)
                   eSubj eRun

        eO : Deriv (eqF (ap2 sbt spec0 O) O)
        eO = sbt_inert_NumCode O ncO x0 S0
    in sbf_step_atomic x0 S0 (cAp2f CKf (cVarc x0) (cVarc x1)) O
         (cAp2f CKf S0 (cVarc x1)) O eAtomL eO

  ------------------------------------------------------------------------
  -- SECTION 2.  The substitution pass over the whole implication.

  passImp :
    Deriv (eqF (ap2 sbf spec0 impOpenCode) (impNumCode S0))
  passImp =
    sbf_step_imp x0 S0 (atomOpen CKa) (atomOpen CKc)
      (atomNum CKa S0) (atomNum CKc S0) (passAtom CKa) (passAtom CKc)

  ------------------------------------------------------------------------
  -- SECTION 3.  Step 2 = encode + wrap + reduce.
  --   wStep2 d = pi tag_sb (pi spec0 (encode d)) ;
  --   thmT (wStep2 d) = impNumCode S0   ( the corrected Step-2 conclusion ).

  wStep2 : Deriv stepFormula -> Term
  wStep2 d = ap2 pi (natCode tag_sb) (ap2 pi spec0 (encode d))

  step2 :
    (d : Deriv stepFormula) ->
    Deriv (eqF (ap1 thmT (wStep2 d)) (impNumCode S0))
  step2 d =
    let w0 : Term
        w0 = encode d

        -- 2a:  thmT w0 = codeFormula stepFormula  ==  impOpenCode  (by refl).
        dOpen : Deriv (eqF (ap1 thmT w0) impOpenCode)
        dOpen = thmT_complete_rec d
    -- 2b:  wrap and reduce by  thmT_at_sb  then the substitution pass.
    in ruleTrans (thmT_at_sb spec0 w0)
         (ruleTrans (congR sbf spec0 dOpen) passImp)
