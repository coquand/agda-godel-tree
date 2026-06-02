{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.dLenStarDef -- the size atom for the Kdef-shape diagonal program
-- gLcodeDef Lstar  at the canonical Kdef threshold  Lstar  (Kdef-shape).
--
-- Discharges the only genuine residual of  CGI_core_num_raw_parametric
-- (T4.ChaitinG1CoreNumRaw):  Deriv (eqF (szLeqApp Lstar (enc (gLcodeDef
-- Lstar))) (ap1 s O)) .
--
-- Same skeleton as  T4.KGodel1Canon.dLenStar  for the Kgt-shape: feed
-- dLen_gen the program-as-encoded, its lenR=natCode(nodes) fact, and the
-- NatLe-bound (transported via  bridgeDef  through  nodes ).

module T4.dLenStarDef where

open import T4.Base
open import T4.KFormula      using ( szLeqApp )
open import T4.KdefDiag      using ( gLcodeDef )
open import T4.ProgEnc       using ( nodes ; enc ; lenR_enc )
open import T4.KGodel1BridgeDef using ( Lstar ; CmcodebDef ; boundDef ; dLen_gen ; bridgeDef )
open import T4.GLCodeNodes   using ( H )
open import T4.NatExp        using ( fst ; snd )
open import T4.ProgNodes     using ( plug )
open import T4.Exp           using ( powN )

open import BRA3.RuleInst2     using ( NatLe )

------------------------------------------------------------------------
-- GENERIC + SEALED transport (parallel to KGodel1Canon.transportNodes):
-- with the two programs as VARIABLES X, Y, the eqSubst body type-checks
-- with  nodes X / nodes Y  NEUTRAL; sealed, so at the concrete instan-
-- tiation it is a NEUTRAL application -- nodes is never reduced.

abstract
  transportNodesDef :
    (X Y : Term) (c : Nat) -> Eq X Y -> NatLe (nodes X) c -> NatLe (nodes Y) c
  transportNodesDef X Y c eq le = eqSubst (\ m -> NatLe m c) (eqCong nodes eq) le

------------------------------------------------------------------------
-- The size bound, transported to the Kdef diagonal  gLcodeDef Lstar :
--   nodes (gLcodeDef Lstar)  <=  powN (fst boundDef)  =  Lstar (as Nat).

domBDef : NatLe (nodes (gLcodeDef Lstar)) (powN (fst boundDef))
domBDef =
  transportNodesDef (plug CmcodebDef (H (fst boundDef)))
                    (gLcodeDef Lstar)
                    (powN (fst boundDef))
                    (eqSym bridgeDef) (snd boundDef)

------------------------------------------------------------------------
-- dLenStarDef : the size atom at the canonical Kdef threshold + Kdef
-- program, via the generic  dLen_gen  applied at
--   e := enc (gLcodeDef Lstar) ,  n := nodes (gLcodeDef Lstar) ,
--   k := fst boundDef .

dLenStarDef :
  Deriv (eqF (szLeqApp Lstar (enc (gLcodeDef Lstar))) (ap1 s O))
dLenStarDef =
  dLen_gen (nodes (gLcodeDef Lstar)) (fst boundDef) (enc (gLcodeDef Lstar))
           (lenR_enc (gLcodeDef Lstar)) domBDef
