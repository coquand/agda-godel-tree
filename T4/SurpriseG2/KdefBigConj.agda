{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.KdefBigConj --
--
-- Per T4/NEXT-SESSION-SURPRISEG2-BIGCONJ.md  Piece A : the BIG-CONJ
-- K-formula shape used end-to-end by the headline  surpriseG2 .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * `KdefBigConj M enum subject : Formula`
--     KdefBigConj zero    enum subject =
--       neg (eqF (ap2 runProg (ap1 enum (natCode zero)) (var zero))
--                 (ap1 s subject))
--     KdefBigConj (suc M) enum subject =
--       neg (imp (negTop) (neg (KdefBigConj M enum subject)))
--       where  negTop = neg (eqF (ap2 runProg (ap1 enum (natCode (suc M)))
--                                  (var zero)) (ap1 s subject)) .
--
--   I.e., the right-associated BIG-AND over the M+1 per-program negs ,
--   each at the bare  runProg  shape ( NO  enumRunProgOf , NO leq-bound ,
--   NO size predicate ) , using BRA's standard And-encoding
--   `A /\ B := neg (imp A (neg B))` .
--
-- * `kdefBigConjFromNegs :
--      (M : Nat) (enum : Fun1) (subject : Term) ->
--      ((k : Nat) -> NatLe k M ->
--        Deriv (neg (eqF (ap2 runProg (ap1 enum (natCode k)) (var zero))
--                         (ap1 s subject)))) ->
--      Deriv (KdefBigConj M enum subject)`
--
--   Mechanical induction on  M  using  T4.CompressCanonical.andIntro
--   ( the standard BRA  And-introduction primitive ) .
--
-- =====================================================================
-- WHY THIS SHAPE
-- =====================================================================
--
-- The OLD  Kdef L x  ( size-predicate, see  T4.Kdef ) needs
-- sizeExhaust to aggregate per-program negs into the universal form ;
-- sizeExhaust is NOT directly BRA-provable per
-- [[feedback_sizeexhaust_obstruction]] .
--
-- The NEW  KdefConj M enum x  ( T4.SurpriseG2.KdefConj , enumRunProgOf
-- shape ) AGGREGATES fine via  kdefConjFromNegs , but the downstream
-- CGI body requires  BerryDataConj 's enumPin which depends on
-- enc (gLcodeDefConj M enum)  -- a SELF-REFERENTIAL artifact whose
-- closed-form construction needs ~500-1000 LoC of bit-list machinery
-- ( see  [[project_bra4_surpriseG2_concrete_wireup_shipped]] ) .
--
-- KdefBigConj bypasses BOTH blockers by aggregating at the bare
-- runProg  shape : no leq-bound to bridge ( so no sizeExhaust ) , and
-- no  enumRunProgOf  wrapping ( so the per-program neg's subject IS
-- the codeable enum-Term directly, no enc-of-self ) .   For our chosen
-- enum-by-construction in  T4.SurpriseG2.EnumBuiltIn  ( gL at slot 0 ,
-- M = 0 ) , the aggregation is a one-liner .

module T4.SurpriseG2.KdefBigConj where

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; le-zero ; le-suc
                                          ; le-refl ; le-suc-right )
open import T4.Kdef               using ( runProg )
open import T4.CompressCanonical  using ( andIntro )

------------------------------------------------------------------------
-- The per-program negation at index  k .

perProgNeg : Fun1 -> Term -> Nat -> Formula
perProgNeg enum subject k =
  neg (eqF (ap2 runProg (ap1 enum (natCode k)) (var zero))
            (ap1 s subject))

------------------------------------------------------------------------
-- The big-conj K-formula at index range [0..M] .   Right-associated
-- And-chain  topNeg /\ KdefBigConj M' enum subject  via the standard
-- BRA And-encoding  A /\ B := neg (imp A (neg B)) .

KdefBigConj : (M : Nat) (enum : Fun1) (subject : Term) -> Formula
KdefBigConj zero    enum subject =
  perProgNeg enum subject zero
KdefBigConj (suc M) enum subject =
  neg (imp (perProgNeg enum subject (suc M))
            (neg (KdefBigConj M enum subject)))

------------------------------------------------------------------------
-- Aggregation : from per-program negs at every  k <= M , derive the
-- big-conj K-formula .   Mechanical induction on  M  .
--
-- Base  M = 0  :  the K-formula is a single per-program neg ;  return
--                  negs zero (le-zero zero)  verbatim .
-- Step  M = suc M' :  IH at  M'  gives  Deriv (KdefBigConj M' enum subject) ;
--                  the topmost per-prog neg  is at  k = suc M' ;  combine
--                  via  andIntro  to get the And of the two .

kdefBigConjFromNegs :
  (M : Nat) (enum : Fun1) (subject : Term) ->
  ((k : Nat) -> NatLe k M -> Deriv (perProgNeg enum subject k)) ->
  Deriv (KdefBigConj M enum subject)
kdefBigConjFromNegs zero    enum subject negs =
  negs zero (le-zero zero)
kdefBigConjFromNegs (suc M) enum subject negs =
  let topNeg : Deriv (perProgNeg enum subject (suc M))
      topNeg = negs (suc M) (le-refl (suc M))

      negsBelow : (k : Nat) -> NatLe k M -> Deriv (perProgNeg enum subject k)
      negsBelow k le = negs k (le-suc-right le)

      ih : Deriv (KdefBigConj M enum subject)
      ih = kdefBigConjFromNegs M enum subject negsBelow
  in andIntro (perProgNeg enum subject (suc M))
              (KdefBigConj M enum subject)
              topNeg ih
