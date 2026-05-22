{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.SbtAtFresh -- prototype of the freshness lemma for  sbt .
--
--   Frv : Nat -> Term -> Set
--
--   Frv k a  is the structural witness that  a  is in codeTerm-shape
--   (built from  O / Pair tag_var (natCode j) [with j /= k] /
--    Pair tag_ap1 (Pair (codeFun1 f) ct) / Pair tag_ap2 (Pair (codeFun2 g)
--                                                              (Pair ca cb)))
--   AND contains no occurrence of  Pair tag_var (natCode k)  as a subterm.
--
-- The freshness lemma :
--
--   sbt_at_fresh :
--     (k : Nat) (S a : Term) ->
--     Frv k a ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) a) a)
--
-- Proved by induction on the  Frv  witness using the four sbt closures
-- from  SbContract :  sbt_at_O ,  sbt_at_var_nomatch ,  sbt_at_ap1 ,
--  sbt_at_ap2 .
--
-- This is the foundation of the "freshness composition" rewriting:
--
--   sbt2 (a/x0, b/x1)  =  sbt (b/x_k) o sbt (a/x0) o sbt (encoded x_k / x1)
--
-- with  k = m b  (chosen fresh in  a  via Frv k a).

module BRA4.Thm12.SbtAtFresh where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.SbContract
open import BRA4.SbT               using ( sbt )
open import BRA4.SbF               using ( sbf )
open import BRA4.SbfAtClosures     using ( sbContract )

open SbContract sbContract

------------------------------------------------------------------------
-- The Frv predicate : structural witness that  a  is in codeTerm
-- shape and contains no  Pair tag_var (natCode k)  subterm.

data Frv (k : Nat) : Term -> Set where
  frvO   : Frv k O
  frvVar : (j : Nat) -> Eq (natEq k j) false ->
           Frv k (ap2 Pair (natCode tag_var) (natCode j))
  frvAp1 : (f : Fun1) (ct : Term) -> Frv k ct ->
           Frv k (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct))
  frvAp2 : (g : Fun2) (ca cb : Term) -> Frv k ca -> Frv k cb ->
           Frv k (ap2 Pair (natCode tag_ap2)
                  (ap2 Pair (codeFun2 g) (ap2 Pair ca cb)))

------------------------------------------------------------------------
-- The freshness lemma.

sbt_at_fresh :
  (k : Nat) (S a : Term) ->
  Frv k a ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) a) a)
sbt_at_fresh k S .O frvO =
  sbt_at_O (ap2 Pair (natCode k) S)
sbt_at_fresh k S .(ap2 Pair (natCode tag_var) (natCode j)) (frvVar j neq) =
  sbt_at_var_nomatch k j S neq
sbt_at_fresh k S .(ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct))
              (frvAp1 f ct frv_ct) =
  let e_step :
        Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
                     (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
                    (ap2 Pair (natCode tag_ap1)
                      (ap2 Pair (codeFun1 f)
                        (ap2 sbt (ap2 Pair (natCode k) S) ct))))
      e_step = sbt_at_ap1 k S f ct
      ih : Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ct) ct)
      ih = sbt_at_fresh k S ct frv_ct
  in ruleTrans e_step
       (congR Pair (natCode tag_ap1) (congR Pair (codeFun1 f) ih))
sbt_at_fresh k S .(ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g) (ap2 Pair ca cb)))
              (frvAp2 g ca cb frv_ca frv_cb) =
  let e_step :
        Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
                     (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
                    (ap2 Pair (natCode tag_ap2)
                      (ap2 Pair (codeFun2 g)
                        (ap2 Pair
                          (ap2 sbt (ap2 Pair (natCode k) S) ca)
                          (ap2 sbt (ap2 Pair (natCode k) S) cb)))))
      e_step = sbt_at_ap2 k S g ca cb
      ih_a : Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ca) ca)
      ih_a = sbt_at_fresh k S ca frv_ca
      ih_b : Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) cb) cb)
      ih_b = sbt_at_fresh k S cb frv_cb
      inner_pair :
        Deriv (eqF (ap2 Pair (ap2 sbt (ap2 Pair (natCode k) S) ca)
                              (ap2 sbt (ap2 Pair (natCode k) S) cb))
                    (ap2 Pair ca cb))
      inner_pair =
        ruleTrans (congL Pair (ap2 sbt (ap2 Pair (natCode k) S) cb) ih_a)
                  (congR Pair ca ih_b)
  in ruleTrans e_step
       (congR Pair (natCode tag_ap2)
         (congR Pair (codeFun2 g) inner_pair))

------------------------------------------------------------------------
-- Convenience constructor :  Frv k (codeFun1 f's leaf positions) for
-- any  k  -- the  codeFun1 f  Term is built from O and ap1 s only, no
-- Pair tag_var subterm anywhere.
--
-- This will be useful for proving Frv k for codeFun1-shaped substituents.

------------------------------------------------------------------------
-- The sbf analog : same structural shape but covers tag_eq / tag_neg /
-- tag_imp instead.  We define a separate predicate FrvF and lemma
-- sbf_at_fresh, using the corresponding sbf closures.

data FrvF (k : Nat) : Term -> Set where
  frvFatomic : (ca cb : Term) -> Frv k ca -> Frv k cb ->
               FrvF k (ap2 Pair (natCode tag_eq) (ap2 Pair ca cb))
  frvFneg    : (cP : Term) -> FrvF k cP ->
               FrvF k (ap2 Pair (natCode tag_neg) cP)
  frvFimp    : (cP cQ : Term) -> FrvF k cP -> FrvF k cQ ->
               FrvF k (ap2 Pair (natCode tag_imp) (ap2 Pair cP cQ))

sbf_at_fresh :
  (k : Nat) (S a : Term) ->
  FrvF k a ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) a) a)
sbf_at_fresh k S .(ap2 Pair (natCode tag_eq) (ap2 Pair ca cb))
              (frvFatomic ca cb frv_ca frv_cb) =
  let e_step :
        Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
                     (ap2 Pair (natCode tag_eq) (ap2 Pair ca cb)))
                    (ap2 Pair (natCode tag_eq)
                      (ap2 Pair
                        (ap2 sbt (ap2 Pair (natCode k) S) ca)
                        (ap2 sbt (ap2 Pair (natCode k) S) cb))))
      e_step = sbf_at_atomic k S ca cb
      ih_a : Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ca) ca)
      ih_a = sbt_at_fresh k S ca frv_ca
      ih_b : Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) cb) cb)
      ih_b = sbt_at_fresh k S cb frv_cb
      inner_pair :
        Deriv (eqF (ap2 Pair (ap2 sbt (ap2 Pair (natCode k) S) ca)
                              (ap2 sbt (ap2 Pair (natCode k) S) cb))
                    (ap2 Pair ca cb))
      inner_pair =
        ruleTrans (congL Pair (ap2 sbt (ap2 Pair (natCode k) S) cb) ih_a)
                  (congR Pair ca ih_b)
  in ruleTrans e_step
       (congR Pair (natCode tag_eq) inner_pair)
sbf_at_fresh k S .(ap2 Pair (natCode tag_neg) cP)
              (frvFneg cP frv_cP) =
  let e_step :
        Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
                     (ap2 Pair (natCode tag_neg) cP))
                    (ap2 Pair (natCode tag_neg)
                      (ap2 sbf (ap2 Pair (natCode k) S) cP)))
      e_step = sbf_at_neg k S cP
      ih_P : Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) cP) cP)
      ih_P = sbf_at_fresh k S cP frv_cP
  in ruleTrans e_step
       (congR Pair (natCode tag_neg) ih_P)
sbf_at_fresh k S .(ap2 Pair (natCode tag_imp) (ap2 Pair cP cQ))
              (frvFimp cP cQ frv_cP frv_cQ) =
  let e_step :
        Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
                     (ap2 Pair (natCode tag_imp) (ap2 Pair cP cQ)))
                    (ap2 Pair (natCode tag_imp)
                      (ap2 Pair
                        (ap2 sbf (ap2 Pair (natCode k) S) cP)
                        (ap2 sbf (ap2 Pair (natCode k) S) cQ))))
      e_step = sbf_at_imp k S cP cQ
      ih_P : Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) cP) cP)
      ih_P = sbf_at_fresh k S cP frv_cP
      ih_Q : Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) cQ) cQ)
      ih_Q = sbf_at_fresh k S cQ frv_cQ
      inner_pair :
        Deriv (eqF (ap2 Pair (ap2 sbf (ap2 Pair (natCode k) S) cP)
                              (ap2 sbf (ap2 Pair (natCode k) S) cQ))
                    (ap2 Pair cP cQ))
      inner_pair =
        ruleTrans (congL Pair (ap2 sbf (ap2 Pair (natCode k) S) cQ) ih_P)
                  (congR Pair cP ih_Q)
  in ruleTrans e_step
       (congR Pair (natCode tag_imp) inner_pair)

------------------------------------------------------------------------
-- Demonstration : simulating sbt2 via three nested sbt wraps.
--
-- Goal :  sbt2 (a/x0, b/x1)  =  sbt (b/x_k) o sbt (a/x0) o sbt (encX_k/x1)
--
-- We capture the Deriv-level statement.  The user supplies an Frv-witness
-- for  a  at index  k  (i.e.  k  is fresh in  a 's pair-tree), and an
-- Frv-witness for the schema at index 1 (allowing the renaming step).
--
-- Specifically, given a CODED schema  c  that contains  Pair tag_var
-- (natCode 1)  occurrences (i.e.  encoded  x1  positions) but no
-- Pair tag_var (natCode k)  occurrences :
--
--   sbt (b/xk) (sbt (a/x0) (sbt (encXk / x1) c))
--     simulates the simultaneous substitution sbt2 (a/x0, b/x1) c .
--
-- This module ships the building block ; the full simulation theorem
-- would require a precise statement of  "sbt2 c"  (which we have via
--  BRA4.SbT2.sbt2) and is left for the consumer.
--
-- One small concrete fact :  Frv k  is monotone under  Pair-encoded
-- structure ; specifically the freshness lemma reduces walking over
-- the schema 's structure to leaving its  codeFun1 / codeFun2
-- sub-positions untouched.

------------------------------------------------------------------------
-- Concrete Frv constructors.

frv_codeVar_neq :
  (k j : Nat) -> Eq (natEq k j) false ->
  Frv k (ap2 Pair (natCode tag_var) (natCode j))
frv_codeVar_neq k j neq = frvVar j neq

-- An ap1-leaf : when the sub-position is just  O ,  Frv  holds
-- regardless of which functor wraps it.
frv_ap1_O :
  (k : Nat) (f : Fun1) ->
  Frv k (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) O))
frv_ap1_O k f = frvAp1 f O frvO
