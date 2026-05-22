{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm11 -- Goedel's First Incompleteness Theorem in the
-- BRA4 Pair-encoding, parametric on:
--
--   sb   : Fun2  satisfying  SbContract   sb     (BRA4.SbContract)
--   prov : Fun1  satisfying  ProvContract prov   (BRA4.Provability)
--
-- The numeral coding  num : Fun1  is the concrete one shipped in
-- BRA4.Num  (BRA4.NumContract.numContract), so it is NOT a module
-- parameter.
--
-- STATEMENT.  For the unprovability formula
--   F (x) := neg ( prov (x) = natCode 1 )
-- and  G = "I am not provable" produced by the diagonal lemma at F,
-- the user-stated target reads:
--
--   godelI : Deriv G -> Deriv falseF
--          (where falseF = atomic (eqn O (ap1 s O)) = " 0 = 1 ")
--
-- Proof.  Assume  dG : Deriv G .
--   * provInternalize G dG : Deriv (eqF (ap1 prov (natCode codeG_Nat)) (natCode 1))
--     where codeG_Nat = codeFormulaNat G.
--   * codeFormula_eq G  bridges natCode codeG_Nat  with  codeFormula G ,
--     letting us recast the above as
--          Deriv (eqF (ap1 prov (codeFormula G)) (natCode 1))
--     i.e.  Deriv (provFormula prov (codeFormula G)) .
--   * bicond_fwd from the diagonal gives  Deriv (imp G F_at_codeG)
--     where  F_at_codeG = neg (provFormula prov (codeFormula G)) .
--   * mp gives Deriv (neg (provFormula prov (codeFormula G))) .
--   * exFalso (provFormula prov (codeFormula G)) falseF  --> Deriv falseF .

module BRA4.Thm.Thm11 where

open import BRA4.Base
open import BRA4.Code
open import BRA4.Num using ( num )
open import BRA4.NumContract using ( numContract )
open import BRA4.NatBridge using ( codeFormulaNat ; codeFormula_eq )
open import BRA4.SbContract using ( SbContract ; module SbContract )
open import BRA4.Provability using ( provFormula ; ProvContract ; module ProvContract )
open import BRA4.ExFalso using ( exFalso )
open import BRA4.Diagonal using ( module Diagonal )

------------------------------------------------------------------------
-- The "I am not provable" formula schema.

unprovFormula : (prov : Fun1) -> Formula
unprovFormula prov = neg (provFormula prov (var 0))

------------------------------------------------------------------------
-- Full statement, parametric on  sb  and  prov  and their contracts.

module GoedelI
  (sbt sbf : Fun2)
  (sbC   : SbContract sbt sbf)
  (prov  : Fun1)
  (provC : ProvContract prov)
  where

  open ProvContract provC

  ----------------------------------------------------------------------
  -- The unprovability formula and its diagonal instance.

  F : Formula
  F = unprovFormula prov

  module D = Diagonal sbt sbf sbC num numContract F
  open D

  ----------------------------------------------------------------------
  -- Re-export for convenience.

  GSentence : Formula
  GSentence = G

  codeG_Nat : Nat
  codeG_Nat = codeFormulaNat G

  ----------------------------------------------------------------------
  -- F_at_codeG = substF 0 (codeFormula G) F .
  --
  -- F = neg (eqF (ap1 prov (var 0)) (natCode 1)) , so substituting
  -- codeFormula G at var 0 (which appears only inside  ap1 prov ; the
  -- (natCode 1) constant has no var 0) gives
  --
  --   F_at_codeG = neg (eqF (ap1 prov (codeFormula G)) (natCode 1))
  --              = neg (provFormula prov (codeFormula G)) .
  --
  -- The equation below is definitional ( refl ).

  F_at_codeG_eq :
    Eq F_at_codeG (neg (provFormula prov (codeFormula G)))
  F_at_codeG_eq = refl

  ----------------------------------------------------------------------
  -- Goedel I.

  godelI : Deriv G -> Deriv falseF
  godelI dG =
    let
      -- (1)  Internalisation:  prov(natCode codeG_Nat) = natCode 1 .
      dProvAtNatCode :
        Deriv (provFormula prov (natCode codeG_Nat))
      dProvAtNatCode = provInternalize G dG

      -- (2)  Bridge:  natCode codeG_Nat =Deriv= codeFormula G .
      bridge_eq : Deriv (eqF (natCode codeG_Nat) (codeFormula G))
      bridge_eq = ruleSym (codeFormula_eq G)

      -- (3)  ap1 prov (natCode codeG_Nat) =Deriv= ap1 prov (codeFormula G) .
      prov_bridge :
        Deriv (eqF (ap1 prov (natCode codeG_Nat))
                    (ap1 prov (codeFormula G)))
      prov_bridge = cong1 prov bridge_eq

      -- (4)  ruleSym then ruleTrans:
      --      Deriv (eqF (ap1 prov (codeFormula G)) (natCode 1))
      --   from  Deriv (eqF (ap1 prov (natCode codeG_Nat)) (natCode 1))
      --   via  prov_bridge ( = LHS-of-target =Deriv= LHS-of-input ).
      dProvAtCodeFormula :
        Deriv (provFormula prov (codeFormula G))
      dProvAtCodeFormula = ruleTrans (ruleSym prov_bridge) dProvAtNatCode

      -- (5)  Diagonal forward:  G --> F_at_codeG .
      --      mp gives Deriv F_at_codeG .
      dF_at_codeG : Deriv F_at_codeG
      dF_at_codeG = mp bicond_fwd dG

      -- (6)  Rewrite via F_at_codeG_eq.
      dNotProvAtCodeFormula :
        Deriv (neg (provFormula prov (codeFormula G)))
      dNotProvAtCodeFormula =
        eqSubst (\ Phi -> Deriv Phi) F_at_codeG_eq dF_at_codeG

      -- (7)  Ex falso.
    in exFalso (provFormula prov (codeFormula G)) falseF
          dProvAtCodeFormula
          dNotProvAtCodeFormula
