{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.NumInertCode -- compositional inertness of  sbt  on  num-based
-- code shapes.
--
-- The substituents that  sb2 / sb3  plant in Thm 12 are codes built from
--  num-leaves  (ap1 num x)  wrapped in  codeFun-tagged  ap1 / ap2  Pair
-- nodes -- e.g.
--
--   encH_at  h X      = Pair tag_ap1 (Pair (codeFun1 h) (num X))
--   encV / encH2 / encR(num X, num Y)
--                     = Pair tag_ap2 (Pair (codeFun2 g) (Pair (num X) (num Y)))
--   encR(num X, s_enc(num Y))
--                     = Pair tag_ap2 (Pair (codeFun2 G)
--                         (Pair (num X) (Pair tag_ap1 (Pair (codeFun1 s) (num Y)))))
--
-- To eliminate  sb2 / sb3  in favour of nested single  sbf / sbt  (see
--  BRA4/NEXT-SESSION-ELIMINATE-SBT2-SBT3.md ) we must show: when single
--  sbt  re-scans an already-planted substituent of this kind, it leaves
-- it UNCHANGED.  That is exactly inertness, lifted through the ap1 / ap2
-- wrappers.
--
-- Rather than an inductive predicate (cf. the rejected  Frv  witness of
-- the dead  BRA4/Thm12/SbtAtFresh.agda ), this file ships COMBINATORS
-- that take the inertness of the sub-positions as  Deriv  hypotheses and
-- conclude the inertness of the wrapped node.  Composed with the
--  num-leaf  base  sbt_num_inert  (BRA4.NumInert), they discharge
-- inertness for ANY num-based composite -- to any nesting depth -- with
-- no predicate and no enumeration of fixed shapes.
--
-- Base case  O  : sbt_at_O .
-- Base leaf  num x : sbt_inert_num  ( = sbt_num_inert , re-exported).
-- ap1 wrap : sbt_inert_ap1 .
-- ap2 wrap : sbt_inert_ap2 .
--
-- All universal in  k : Nat , S : Term  (the substitution spec
--  Pair (natCode k) S ); no Closed / freshness premise.

module BRA4.NumInertCode where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code   using ( codeFun1 ; codeFun2 )
open import BRA4.Num    using ( num )
open import BRA4.SbT    using ( sbt ; sbt_at_O )
open import BRA4.SbtAtAp using ( sbt_at_ap1 ; sbt_at_ap2 )
open import BRA4.NumInert using ( sbt_num_inert )

------------------------------------------------------------------------
-- Inert on the empty leaf  O .

sbt_inert_O :
  (k : Nat) (S : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) O) O)
sbt_inert_O k S = sbt_at_O (ap2 Pair (natCode k) S)

------------------------------------------------------------------------
-- Inert on a  num-leaf .  (Re-export of the numeral-inertness lemma; it
-- is the base case of every num-based composite.)

sbt_inert_num :
  (k : Nat) (S : Term) (x : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (ap1 num x)) (ap1 num x))
sbt_inert_num = sbt_num_inert

------------------------------------------------------------------------
-- ap1 wrapper-lift.
--
--   sbt spec ct = ct      (hypothesis ih)
--   ==>
--   sbt spec (Pair tag_ap1 (Pair (codeFun1 f) ct))
--      = Pair tag_ap1 (Pair (codeFun1 f) ct) .

sbt_inert_ap1 :
  (k : Nat) (S : Term) (f : Fun1) (ct : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ct) ct) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
              (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
sbt_inert_ap1 k S f ct ih =
  let spec : Term
      spec = ap2 Pair (natCode k) S

      -- sbt spec (ap1-wrap) = ap1-wrap with the sub-position re-scanned.
      e1 :
        Deriv (eqF (ap2 sbt spec
                     (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
                    (ap2 Pair (natCode tag_ap1)
                      (ap2 Pair (codeFun1 f) (ap2 sbt spec ct))))
      e1 = sbt_at_ap1 k S f ct

      -- ih restores the sub-position.
      e2 :
        Deriv (eqF (ap2 Pair (natCode tag_ap1)
                      (ap2 Pair (codeFun1 f) (ap2 sbt spec ct)))
                    (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
      e2 = congR Pair (natCode tag_ap1) (congR Pair (codeFun1 f) ih)
  in ruleTrans e1 e2

------------------------------------------------------------------------
-- ap2 wrapper-lift.
--
--   sbt spec ca = ca  ,  sbt spec cb = cb   (hypotheses ih_a , ih_b)
--   ==>
--   sbt spec (Pair tag_ap2 (Pair (codeFun2 g) (Pair ca cb)))
--      = Pair tag_ap2 (Pair (codeFun2 g) (Pair ca cb)) .

sbt_inert_ap2 :
  (k : Nat) (S : Term) (g : Fun2) (ca cb : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ca) ca) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) cb) cb) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap2)
                 (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
sbt_inert_ap2 k S g ca cb ih_a ih_b =
  let spec : Term
      spec = ap2 Pair (natCode k) S

      e1 :
        Deriv (eqF (ap2 sbt spec
                     (ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
                    (ap2 Pair (natCode tag_ap2)
                      (ap2 Pair (codeFun2 g)
                        (ap2 Pair (ap2 sbt spec ca) (ap2 sbt spec cb)))))
      e1 = sbt_at_ap2 k S g ca cb

      -- restore ca (left), then cb (right).
      p1 :
        Deriv (eqF (ap2 Pair (ap2 sbt spec ca) (ap2 sbt spec cb))
                    (ap2 Pair ca (ap2 sbt spec cb)))
      p1 = congL Pair (ap2 sbt spec cb) ih_a

      p2 :
        Deriv (eqF (ap2 Pair ca (ap2 sbt spec cb))
                    (ap2 Pair ca cb))
      p2 = congR Pair ca ih_b

      pair_eq :
        Deriv (eqF (ap2 Pair (ap2 sbt spec ca) (ap2 sbt spec cb))
                    (ap2 Pair ca cb))
      pair_eq = ruleTrans p1 p2

      e2 :
        Deriv (eqF (ap2 Pair (natCode tag_ap2)
                      (ap2 Pair (codeFun2 g)
                        (ap2 Pair (ap2 sbt spec ca) (ap2 sbt spec cb))))
                    (ap2 Pair (natCode tag_ap2)
                      (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
      e2 = congR Pair (natCode tag_ap2) (congR Pair (codeFun2 g) pair_eq)
  in ruleTrans e1 e2

------------------------------------------------------------------------
-- Worked compositions for the concrete substituent shapes of Thm 12.
-- (Convenience; the combinators above already suffice for any nesting.)

-- encH_at f X = Pair tag_ap1 (Pair (codeFun1 f) (num X)).
sbt_inert_encH :
  (k : Nat) (S : Term) (f : Fun1) (X : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) (ap1 num X))))
              (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) (ap1 num X))))
sbt_inert_encH k S f X =
  sbt_inert_ap1 k S f (ap1 num X) (sbt_num_inert k S X)

-- encG g (num X) (num Y) = Pair tag_ap2 (Pair (codeFun2 g) (Pair (num X) (num Y))).
-- Covers encV (g = v), encH2 (g = h2), encR (g = R ...).
sbt_inert_encG :
  (k : Nat) (S : Term) (g : Fun2) (X Y : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap2)
                 (ap2 Pair (codeFun2 g) (ap2 Pair (ap1 num X) (ap1 num Y)))))
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair (codeFun2 g) (ap2 Pair (ap1 num X) (ap1 num Y)))))
sbt_inert_encG k S g X Y =
  sbt_inert_ap2 k S g (ap1 num X) (ap1 num Y)
    (sbt_num_inert k S X) (sbt_num_inert k S Y)

-- encR(num X, s_enc(num Y))
--   = Pair tag_ap2 (Pair (codeFun2 G)
--       (Pair (num X) (Pair tag_ap1 (Pair (codeFun1 s) (num Y))))) .
-- Demonstrates nesting (ap1-wrapped num inside an ap2 wrap).
sbt_inert_encR_sEnc :
  (k : Nat) (S : Term) (g : Fun2) (X Y : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap2)
                 (ap2 Pair (codeFun2 g)
                   (ap2 Pair (ap1 num X)
                     (ap2 Pair (natCode tag_ap1)
                       (ap2 Pair (codeFun1 s) (ap1 num Y)))))))
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair (codeFun2 g)
                  (ap2 Pair (ap1 num X)
                    (ap2 Pair (natCode tag_ap1)
                      (ap2 Pair (codeFun1 s) (ap1 num Y)))))))
sbt_inert_encR_sEnc k S g X Y =
  sbt_inert_ap2 k S g
    (ap1 num X)
    (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num Y)))
    (sbt_num_inert k S X)
    (sbt_inert_ap1 k S s (ap1 num Y) (sbt_num_inert k S Y))
