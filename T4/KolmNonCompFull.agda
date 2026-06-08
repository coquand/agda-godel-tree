{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmNonCompFull -- brick E, the HEADLINE of #4: Kolmogorov complexity is
-- NOT computable.
--
-- "Kf computes K" is the exact characterization  Kf x <= L  <=>  x is describable
-- within length L  ( KSound + RealizesAt :  Kf decides the  Kle  predicate ).  No
-- such total BRA function exists, on pain of inconsistency.  The Berry program:
--
--   * sizeFits  (brick D) picks an  L  with  size (berry Kf L) <= L ;
--   * berryRun  (brick C) runs  berry Kf L , describing  bfun Kf L  within that
--     size, so  Kle (size) (bfun Kf L) ;
--   * bfun_hit  (brick A/B) -- using RealizesAt + incompressibility -- shows
--     bfun Kf L  is incompressible above L:  L < Kf (bfun Kf L) ;
--   * nonComputable_clash  (the core): describable within  size <= L  yet
--     Kf-value  > L  contradicts soundness.

module T4.KolmNonCompFull where

open import T4.Base
open import T4.EvalUCorrect using ( evalN1 )
open import T4.ProgEnc      using ( nodes )
open import T4.EvalU        using ( mcode1 )
open import BRA3.RuleInst2  using ( NatLe )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt )
open import T4.SurpriseG2.NumNeq using ( Not )
open import T4.Code         using ( falseF )
open import T4.NatExp       using ( Sg )
open import T4.KolmCount    using ( Kle )
open import T4.KolmNonComp  using ( KSound ; nonComputable_clash )
open import T4.KolmBoundedSearch using ( bfun ; bfun_hit ; RealizesAt )
open import T4.KolmBerry    using ( berry ; berryRun )
open import T4.KolmExpLinear using ( sizeFits )

------------------------------------------------------------------------
-- "Kf computes Kolmogorov complexity":  Kf x <= L  iff  Kle L x .
--   kSound    :  Kle L x  ->  Kf x <= L      (no over-estimate)
--   kRealizes :  Kf x <= L  ->  Kle L x      (Kf's value is realized)

record KComputes (Kf : Fun1) : Set where
  constructor mkKComputes
  field
    kSound    : KSound Kf
    kRealizes : RealizesAt Kf

open KComputes public

------------------------------------------------------------------------
-- THE HEADLINE.

nonComputable :
  Not (Deriv falseF) -> (Kf : Fun1) -> KComputes Kf -> Empty
nonComputable con Kf kc =
  let sf : Sg Nat (\ L -> NatLe (nodes (mcode1 (berry Kf L))) L)
      sf = sizeFits Kf
      L : Nat
      L = Sg.fst sf
      bL : Nat
      bL = bfun Kf L
      mLeL : NatLe (nodes (mcode1 (berry Kf L))) L
      mLeL = Sg.snd sf
      hit : Lt L (evalN1 Kf bL)
      hit = bfun_hit con Kf (kRealizes kc) L
      kleMbL : Kle (nodes (mcode1 (berry Kf L))) bL
      kleMbL = berryRun con Kf L
  in nonComputable_clash Kf (kSound kc) L
       (nodes (mcode1 (berry Kf L))) bL mLeL hit kleMbL
