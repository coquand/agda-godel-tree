{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Base -- re-exports of the shared Term / Formula / Deriv
-- system from BRA3.  BRA4 keeps the same syntax of Terms and
-- the same rule system as BRA3 (Theorems and Deriv data type are
-- unchanged).  Only the coding scheme  code  and the verifier
-- thmT  are redesigned in BRA4 to follow Guard 1963 more closely.

module BRA4.Base where

open import BRA3.Base       public
open import BRA3.Term       public
open import BRA3.Formula    public
open import BRA3.Deriv      public
open import BRA3.Equational public

-- The Guard-style pair / projection algebra.
open import BRA3.PairAlgebra public using
  ( Pair ; Fst ; Snd ; axFst ; axSnd
  ; Fan ; Lift1 ; Lift2 ; compose1U
  ; axFan ; axLift ; axLift2 ; axComp ; axComp2 ; axI ; axZ ; axConst
  ; I ; Z ; Const ; Post ; IfLf
  ; axPost ; IfLf_unfold ; axIfLfL ; axIfLfN_nc )

-- Cantor coding (Tree -> Nat, used by Guard).  Reused as-is.
open import BRA3.Code.Tree     public using ( Tree ; Leaf ; Node ; encodeTree )
open import BRA3.Code.TreeToNat public using ( treeToNat )

-- Closed predicate (basic Term-closure infrastructure).
open import BRA3.Dispatch   public using
  ( Closed ; closed_O ; closed_natCode
  ; condFork ; condFork_true ; condFork_true_nc ; condFork_false
  ; constN ; constN_eq )
