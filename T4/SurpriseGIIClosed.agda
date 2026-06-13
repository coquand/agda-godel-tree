{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseGIIClosed -- THE CLEAN SURPRISE-GOEDEL-II STATEMENT.
--
--   surpriseGII : ConOpenInt -> Deriv falseF
--
-- The ONLY hypothesis is  ConOpenInt  ( the open-consistency sentence
--   ConOpenInt = Deriv (neg (eqF (ap1 thmT (var zero)) codeFalse))
--   = "T |- ~ (thmT(x) = code(0=1))  for every x" ,  i.e. T proves its own
--   open consistency ) ;  the conclusion is  Deriv falseF  ( = T |- 0 = 1 ).
-- So : if T proves its own consistency then T is inconsistent -- Goedel II, via
-- the Chaitin-Goedel-I diagonal and the Kritchman-Raz surprise-examination
-- descent ( T4.SurpriseGIINum ).
--
-- This is the closed corollary of  T4.SurpriseGIINum.surpriseGII_num , which
-- carries a SECOND, VESTIGIAL parameter  Lstar : Nat .   That parameter is NOT a
-- hypothesis : the day-count  N  and threshold  M  are the Chaitin-aligned counts
--  N = Ncount , M = Mcount = NthrN-as-a-Nat  ( T4.StageBase0N / T4.StageBaseSizeN ),
-- which do NOT depend on  Lstar  ( it is kept only so the downstream  T4.Step*N
-- modules compile unchanged ).   The genuine description-length budget is the
-- INTERNAL Chaitin fixed point  NthrN = predNof (fst boundDefN)  ( = 3^(L*+1) with
--  L* = 2^kk ,  kk = fst boundDefN  the diagonal's own  affine_dom  size bound ),
-- computed from the diagonal, not supplied.   Hence instantiating  Lstar := 0
-- below loses nothing : the proof is the same for any  Lstar , so the clean
-- statement correctly shows  ConOpenInt  as the SOLE input.
--
-- Constructive, Agda-checked, no postulates / holes / extra hypotheses :
--   agda --safe T4/SurpriseGIIClosed.agda

module T4.SurpriseGIIClosed where

open import T4.Base
open import T4.Code using ( falseF )
open import T4.SurpriseG2.ConOpenIntDef using ( ConOpenInt )
import T4.SurpriseGIINum

surpriseGII : ConOpenInt -> Deriv falseF
surpriseGII con = T4.SurpriseGIINum.surpriseGII_num 0 con
