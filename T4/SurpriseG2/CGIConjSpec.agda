{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.CGIConjSpec -- Piece 2c ( architectural form ) of
-- the KdefConj reformulation per  T4/NEXT-SESSION-KDEFCONJ.md .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- `CGIConjSpec  thmT kCode`  --  the TYPE of the CGI-Conj theorem
-- ( the Berry-chain retarget at the new K-formula shape ) , as a
-- record parametric on  (thmT : Fun1)  +  (kCode : Fun1) .   The
-- concrete proof body is a SEPARATE residual ;  this file makes the
-- spec a first-class parameter of the framework, so the surprise-G2
-- wireup can compose without waiting for the full Berry-chain rewrite
-- of DischargeKdef / ChainKdef / CgiClash .
--
-- =====================================================================
-- WHY  thmT  AND  kCode  ARE BOTH PARAMETERS.
-- =====================================================================
--
-- 1.  `kCode`  is intended to be  KcodeConj M enum  at instantiation
--     time .  Keeping it abstract avoids importing  T4.SurpriseG2.KcodeConj
--     ( whose transitive  T4.Kdef + T4.NegAtomCode  chain is heavy ) .
--
-- 2.  `thmT`  is intended to be  T4.ThmT.thmT  at instantiation
--     time .   ANY direct import of  T4.ThmT  in this file triggers
--     a > 30s typecheck ( WITHOUT actually depending on  ThmT 's
--     concrete definition ) -- see
--     `memory/feedback_slow_typecheck_means_abstract_constants` .
--     Parametrising  thmT  drops the typecheck to ~ 1.5s .   The
--     framework user supplies  thmT := T4.ThmT.thmT  at the call
--     site .
--
-- =====================================================================
-- THE SPEC.
-- =====================================================================
--
-- For abstract  (thmT : Fun1)  +  (kCode : Fun1)  ( intended to be
-- T4.ThmT.thmT  +  KcodeConj M enum  respectively ) , a
-- CGIConjSpec thmT kCode  carries :
--
--   * `cgiConj`  : the Berry-clash function
--       (w x : Term) ->
--       Deriv (eqF (ap1 thmT w) (ap1 kCode x)) ->
--       Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
--
-- mirroring the OLD  CGI_core_num_raw  signature ( which is
-- specialised to  thmT := T4.ThmT.thmT  and  kCode := Kcode Lstar ) .
-- The framework's user closes this by supplying an implementation
-- specialised at  kCode := KcodeConj M enum .
--
-- =====================================================================
-- WHAT IS DEFERRED.
-- =====================================================================
--
-- The CONCRETE proof body of  cgiConj  at  kCode := KcodeConj M enum
-- ( i.e. ,  the Berry-chain rewrite ) , estimated ~200-400 LoC
-- across parallels of  DischargeKdef , ChainKdef , CgiClash ,
-- KdefDiag , dLenStarDef , predFlipDef , hitKdef , outKdef .
-- The implementation chooses the Berry diagonal as
-- ap1 enum (natCode kStar)  for some meta-witness  kStar  in
-- [0..M] , then runs the same Berry argument that  CGI_core_num_raw
-- does for the OLD  Kcode Lstar  shape -- with the size-atom
-- replaced by the leq-natCode-bound atom .

module T4.SurpriseG2.CGIConjSpec where

open import T4.Base
open import T4.Code using ( codeFalse )

------------------------------------------------------------------------
-- Local Sigma  ( avoids importing  T4.ChaitinG1CoreNumRaw ) .

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- The Berry-clash spec , parametric on  thmT  and  kCode .
--
-- At instantiation :
--   thmT  :=  T4.ThmT.thmT
--   kCode :=  T4.SurpriseG2.KcodeConj.KcodeConj M enum
-- for some  M : Nat  and  enum : Fun1  ( from  SurpriseConstsConj ) .

record CGIConjSpec (thmT : Fun1) (kCode : Fun1) : Set where
  field
    cgiConj :
      (w x : Term) ->
      Deriv (eqF (ap1 thmT w) (ap1 kCode x)) ->
      Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
