{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.CGIConjBody -- the top-level WIRED CGIConjSpec body
-- for the conjunction-shape chain ( per
-- T4/NEXT-SESSION-ENUMRUNPROG-REFACTOR.md ) .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- 1.  `BerryDataConj M enum`  -- the META data pack that supplies the
--     diagonal-program enumeration index  kStar  +  NatLe  bound  +
--     the  enumPin  meta-pin  enum (natCode kStar) = enc (gLcodeDefConj
--     M enum) .   Replaces the single-field skeleton  BerryDataConj
--     of the previous session ; that field's body is now derived
--     INLINE in this file by composing the chain pieces .
--
-- 2.  `cgiConjBody M enum bData`  --  builds a complete
--     CGIConjSpec thmT (KcodeConj M enum)  from a  BerryDataConj M enum .
--     Body in 5 stages :
--      ( i )   close the user's  (w , x)  via  T4.CloseW  +
--              ruleInst  twice  ( neutralises  var 0 / var 1 ) ;
--      ( ii )  open the conj-shape  DischargeKdefConj  module to get
--              k_max , dNeg_at_kmax , x' ;
--      ( iii ) open the conj-shape  ChainKdefConj  module to get
--              nTerm , dEval_witness  ( for  enc (gLcodeDefConj M enum) ) ;
--      ( iv )  bridge  dEval_witness  to the NEW
--              ` enumRunProgOf enum (natCode kStar) nTerm = s x' `
--              shape  via  enumPin  +  enumRunProgOf_eq  +  runProg_eq ;
--      ( v )   call  cgiClashConj  ( T4.SurpriseG2.CgiClashConjMain ) .
--
-- 3.  `cgiConjBodyFromBerry`  --  the previous-session skeleton
--     wrapper , preserved for compatibility but largely subsumed by
--     `cgiConjBody`  ( which produces the same CGIConjSpec from the
--     FACTORED  BerryDataConj  meta-pack ) .

module T4.SurpriseG2.CGIConjBody where

open import T4.Base
open import T4.Code                       using ( codeFalse )
open import T4.ThmT                       using ( thmT )
open import T4.Num                        using ( num )
open import T4.Kdef                       using ( runProg ; runProg_eq )
open import T4.ProgEnc                    using ( enc )
open import T4.ProgParse                  using ( parse )
open import T4.EvalUEval                  using ( evalU )
open import T4.CloseW                     using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )

open import T4.SurpriseG2.EnumRunProg     using ( enumRunProgOf ; enumRunProgOf_eq )
open import T4.SurpriseG2.KcodeConj       using ( KcodeConj )
open import T4.SurpriseG2.KdefDiagConj    using ( gLcodeDefConj )
open import T4.SurpriseG2.CGIConjSpec
  using ( CGIConjSpec ; Sigma ; mkSigma )
open import T4.SurpriseG2.CgiClashConj    using ( SomeProof )
open import T4.SurpriseG2.CgiClashConjMain using ( cgiClashConj )

import T4.SurpriseG2.DischargeKdefConj
import T4.SurpriseG2.ChainKdefConj

open import BRA3.RuleInst2                  using ( NatLe )

------------------------------------------------------------------------
-- The META Berry-data pack .   Three pieces :   the enumeration index
-- of the diagonal program , its  NatLe  bound to  M , and the
-- enumerator's pin to the diagonal program code .
--
-- DEFINED AS A NESTED  Sigma  ALIAS  ( not a fresh record ) for the
-- SAME slow-typecheck reason as  SomeProof  in  CgiClashConj.agda :
-- a specialised record with field  enumPin : Deriv (eqF (ap1 enum
-- (natCode kStar)) (enc (gLcodeDefConj M enum)))  forces Agda to
-- elaborate  enc (gLcodeDefConj M enum)  at the record definition
-- site -- a single record alone takes 20s+ to typecheck .   Using the
-- generic  Sigma  with the type-level dependency expressed as a
-- function  ( kStar -> Sigma (NatLe ...) (\ _ -> Deriv ...) )
-- bypasses the record-field elaboration entirely .

BerryDataConj : Nat -> Fun1 -> Set
BerryDataConj M enum =
  Sigma Nat (\ kStar ->
    Sigma (NatLe kStar M) (\ _ ->
      Deriv (eqF (ap1 enum (natCode kStar))
                  (enc (gLcodeDefConj M enum)))))

-- Selectors  for the nested Sigma  ( convenience for callers ) .

berryKStar : (M : Nat) (enum : Fun1) -> BerryDataConj M enum -> Nat
berryKStar M enum bData = Sigma.fst bData

berryKStarBound :
  (M : Nat) (enum : Fun1) (bData : BerryDataConj M enum) ->
  NatLe (berryKStar M enum bData) M
berryKStarBound M enum bData = Sigma.fst (Sigma.snd bData)

berryEnumPin :
  (M : Nat) (enum : Fun1) (bData : BerryDataConj M enum) ->
  Deriv (eqF (ap1 enum (natCode (berryKStar M enum bData)))
              (enc (gLcodeDefConj M enum)))
berryEnumPin M enum bData = Sigma.snd (Sigma.snd bData)

------------------------------------------------------------------------
-- The wireup .   Build  CGIConjSpec thmT (KcodeConj M enum)  from a
-- BerryDataConj M enum  by composing the chain pieces .

cgiConjBody :
  (M : Nat) (enum : Fun1) ->
  BerryDataConj M enum ->
  CGIConjSpec thmT (KcodeConj M enum)
cgiConjBody M enum bData =
  let kStar      : Nat
      kStar      = berryKStar M enum bData

      kStarBound : NatLe kStar M
      kStarBound = berryKStarBound M enum bData

      enumPin    :
        Deriv (eqF (ap1 enum (natCode kStar))
                    (enc (gLcodeDefConj M enum)))
      enumPin    = berryEnumPin M enum bData

      gLname : Term
      gLname = enc (gLcodeDefConj M enum)

      body :
        (w x : Term) ->
        Deriv (eqF (ap1 thmT w) (ap1 (KcodeConj M enum) x)) ->
        Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
      body w x h =
        let -- (i) close  w , x  at vars 0/1 via two  ruleInst  passes .
            h1 :
              Deriv (eqF (ap1 thmT (substT (suc zero) O w))
                          (ap1 (KcodeConj M enum) (substT (suc zero) O x)))
            h1 = ruleInst (suc zero) O h

            h2 :
              Deriv (eqF (ap1 thmT (closeW w)) (ap1 (KcodeConj M enum) (closeW x)))
            h2 = ruleInst zero O h1

            -- (ii)  Open the conj-shape Discharge module .
            open T4.SurpriseG2.DischargeKdefConj.DischargeKdefConj
                   M enum (closeW w) (closeW x) h2
                   (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
              using ( k_max ; x' ; dNeg_at_kmax )

            -- (iii) Open the conj-shape Chain module .
            open T4.SurpriseG2.ChainKdefConj.ChainKdefConj
                   M enum (closeW w) (closeW x) h2
                   (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
              using ( nTerm ; dEval_witness )

            -- (iv)  Bridge  dEval_witness  to the  enumRunProgOf  shape .
            --
            --   dEval_witness :
            --     eqF (ap2 evalU (ap1 parse gLname) nTerm) (ap1 s x') .
            --
            --   Chain :
            --     enumRunProgOf enum (natCode kStar) nTerm
            --       = runProg (enum (natCode kStar)) nTerm   (enumRunProgOf_eq)
            --       = runProg gLname nTerm                    (congL via enumPin)
            --       = evalU (parse gLname) nTerm              (runProg_eq)
            --       = s x'                                    (dEval_witness) .
            e1 :
              Deriv (eqF (ap2 (enumRunProgOf enum) (natCode kStar) nTerm)
                          (ap2 runProg (ap1 enum (natCode kStar)) nTerm))
            e1 = enumRunProgOf_eq enum (natCode kStar) nTerm

            e2 :
              Deriv (eqF (ap2 runProg (ap1 enum (natCode kStar)) nTerm)
                          (ap2 runProg gLname nTerm))
            e2 = congL runProg nTerm enumPin

            e3 :
              Deriv (eqF (ap2 runProg gLname nTerm)
                          (ap2 evalU (ap1 parse gLname) nTerm))
            e3 = runProg_eq gLname nTerm

            runEnumForm :
              Deriv (eqF (ap2 (enumRunProgOf enum) (natCode kStar) nTerm)
                          (ap1 s x'))
            runEnumForm = ruleTrans e1 (ruleTrans e2 (ruleTrans e3 dEval_witness))

            -- (v)   The integrated clash .
            proof : SomeProof
            proof = cgiClashConj M enum kStar kStarBound
                      gLname nTerm x' k_max
                      dNeg_at_kmax runEnumForm
        in proof
  in record { cgiConj = body }

------------------------------------------------------------------------
-- LEGACY SKELETON  wrapper  ( previous session's  cgiConjOf  field
-- form ;  preserved as a thin adapter for callers that already build
-- the inner CGIConjSpec body manually ) .

record BerryDataConjLegacy (thmT : Fun1) (kCode : Fun1) : Set where
  field
    cgiConjOf :
      (w x : Term) ->
      Deriv (eqF (ap1 thmT w) (ap1 kCode x)) ->
      Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))

cgiConjBodyFromBerry :
  (thmT' kCode : Fun1) ->
  BerryDataConjLegacy thmT' kCode ->
  CGIConjSpec thmT' kCode
cgiConjBodyFromBerry thmT' kCode bdata =
  record { cgiConj = BerryDataConjLegacy.cgiConjOf bdata }
