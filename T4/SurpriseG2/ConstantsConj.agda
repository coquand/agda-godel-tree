{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.ConstantsConj -- the external abstract constants for
-- the surprise-G2 framework in the NEW conjunction-shape K-formula
-- formulation ( see  T4/NEXT-SESSION-KDEFCONJ.md  for the design ).
--
-- =========================================================
-- WHAT CHANGES vs the original  SurpriseConsts  record.
-- =========================================================
--
--   * shortProgs : Nat -> Term         REPLACED by  enum : Fun1 .
--                                       The k-th short program is now
--                                       ap1 enum (natCode k) -- a BRA-
--                                       internal application , not a
--                                       meta-function value .
--   * shortProgs_noVar                 DROPPED -- not needed (enum is
--                                       a closed Fun1 ;  ap1 enum (natCode k)
--                                       is automatically NoVar at any index).
--   * shortProgs_size                  DROPPED -- the size predicate is
--                                       no longer in the K-formula ;  M+1
--                                       carries the size info as META .
--   * sizeExhaust                      DROPPED -- KdefConj's universal-to-
--                                       conjunction equivalence is BRA-
--                                       provable directly (kdefConjFromNegs
--                                       in T4.SurpriseG2.KdefConj ).
--   * Lstar : Term                     OPTIONALLY KEPT as a META-coupling
--                                       reference ( needed if later
--                                       framework pieces want to bridge
--                                       to KGodel1BridgeDef.Lstar via a
--                                       LstarPin ;  for Piece 1 alone
--                                       it is not used and we just keep
--                                       LstarMeta : Nat ).
--
-- =========================================================
-- WHAT STAYS.
-- =========================================================
--
--   * N : Nat              -- meta-Nat surprise-exam day count .
--   * M : Nat              -- M+1 = number of enumerated short programs .
--   * pigeonhole shape  M < N  -- still the framework's combinatorial
--                                 seed ( provided externally per
--                                 DescFam in the StageZeroNegs path ).
--
-- The new record is intentionally MINIMAL : the framework's K-formula
-- assembly + per-program-neg supply use only  M  +  enum  ;  no extra
-- hypotheses about the enumeration's coverage ( those were sizeExhaust ,
-- now BRA-provable from the conjunction shape ) .
--
-- The Berry-diagonal index witness ( diagIndex : Sigma k_*. Eq (ap1 enum
-- (natCode k_*)) g_L ) is NOT in this record because the diagonal  g_L
-- only enters at the CGI level ( Piece 2 ) ;  we add it as a separate
-- residual when CGI is retargeted at  KcodeConj .

module T4.SurpriseG2.ConstantsConj where

open import T4.Base

------------------------------------------------------------------------
-- The minimal surprise-G2 constants in the conjunction-shape framework.

record SurpriseConstsConj : Set where
  field
    N    : Nat              -- meta-Nat:  N+1 = days [0..N] .
    M    : Nat              -- meta-Nat:  M+1 = number of enumerated short progs .
    enum : Fun1             -- enumerator :  ap1 enum (natCode k)  is the k-th short prog .
