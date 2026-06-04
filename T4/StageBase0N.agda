{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StageBase0N -- the hypothesis-free base case  S(0) , with the day-count  N
-- and program-margin  M  the CHAITIN-ALIGNED counts ( clos "build N big enough
-- from L*" ) :   N = Ncount = suc Mcount ,  M = Mcount = NthrN-as-a-Nat
-- ( T4.StageBaseSizeN ).   So the pigeonhole margin  Lt M N  is  ltSelf  ( no
-- Bnat , no hypothesis ), and  natCode M = NthrN  ( T4.StageBaseSizeN.sizeId )
-- aligns  coverBridgeN 's guard with  chaitinGI_imp 's.
--
-- ( The  Lstar  parameter is kept only so the downstream step modules
--   T4.Step*N , which open  StageBase0N Lstar , compile unchanged ; the counts
--   no longer depend on it -- the number-code finite set is  { p < NthrN } ,
--   not the old  EnumProg  table. )
--
--   stageBase0 : StagePredFN N M zero       ( = S(0) , no hypothesis )

open import T4.Base
open import T4.StagePredFN using ( StagePredFN )

module T4.StageBase0N (Lstar : Nat) where

open import T4.StageBaseSizeN
  using ( Mcount ; Ncount ; stageBase0Size ) public

N : Nat
N = Ncount

M : Nat
M = Mcount

stageBase0 : StagePredFN N M zero
stageBase0 = stageBase0Size
