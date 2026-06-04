{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StageBaseSizeN -- the surprise day/program counts tied to the Chaitin
-- threshold  NthrN , and the resulting hypothesis-free  S(0)  +  size identity.
--
-- clos "build N big enough from L*": the program count is the number-code finite
-- set  { p < NthrN } ,  NthrN = 3^(L*+1)  ( = the  p <= NthrN  bound of
-- chaitinGI_imp's  KdefN ).   As a  Nat  this is
--
--   Mcount = pow3 (suc (powN kk))        ( kk = fst boundDefN ; = NthrN-as-Nat ),
--   Ncount = suc Mcount                  ( one more day than program slots ),
--
-- so the pigeonhole margin  Lt Mcount Ncount  is  ltSelf  ( NO  Bnat , NO
-- hypothesis ), and the SIZE IDENTITY
--
--   sizeId : Deriv (eqF (natCode Mcount) NthrN)
--
-- ( = ruleSym  T4.dLenStarDefN.NthrN_eval ) lets  coverBridgeN 's guard
-- leq (var 0) (natCode Mcount)  meet  chaitinGI_imp 's  leq (var 0) NthrN .
-- Hence  stageBase0Size : StagePredFN Ncount Mcount zero  =  S(0)  at the
-- Chaitin-aligned counts, with no hypothesis.

open import T4.Base
open import T4.TreeDigitsSize using ( pow3 )
open import T4.Exp using ( powN )
open import T4.KGodel1BridgeDefN using ( NthrN )
open import T4.dLenStarDefN using ( kk ; NthrN_eval )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltSelf )
open import T4.StagePredFN using ( StagePredFN )
open import T4.StageBaseFN using ( stageBaseFN )

module T4.StageBaseSizeN where

Mcount : Nat
Mcount = pow3 (suc (powN kk))

-- Ncount is SEALED abstract :  the surprise day-count  N  must stay an inert
-- symbol so the general arithmetic ( countDays / countDays_step ) never unfolds
-- it ( unfolding  N = suc Mcount  tangles  countAux 's recursion-on-N with the
-- per-day index, blowing up typechecking ).   Ncount = suc Mcount only via the
-- sealed  ltMN  ( the pigeonhole margin proven inside the block ).
abstract
  Ncount : Nat
  Ncount = suc Mcount

  -- the pigeonhole margin, hypothesis-free ( inside the seal,  Ncount = suc Mcount ).
  ltMN : Lt Mcount Ncount
  ltMN = ltSelf Mcount

-- the size identity :  natCode Mcount = NthrN  ( Chaitin guard alignment ).
sizeId : Deriv (eqF (natCode Mcount) NthrN)
sizeId = ruleSym NthrN_eval

-- S(0) at the Chaitin-aligned counts.
stageBase0Size : StagePredFN Ncount Mcount zero
stageBase0Size = stageBaseFN Ncount Mcount ltMN
