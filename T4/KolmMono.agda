{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmMono -- Kle is monotone in the complexity level:
--   Kle a x  ->  a <= b  ->  Kle b x .
-- ( If x is describable within length a, it is describable within any larger
--   length b -- the same program still fits.  Needed for the Berry / non-
--   computability clash. )

module T4.KolmMono where

open import T4.Base
open import T4.TreeDigitsSize  using ( pow3 )
open import T4.KolmLog         using ( pow3_mono )
open import BRA3.RuleInst2      using ( NatLe ; le-suc )
open import T4.KolmNumReflect  using ( Sg ; mkSg )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS )
open import T4.KolmCount       using ( And ; and ; Kle )

------------------------------------------------------------------------
-- Lt / NatLe bridge:  p < K1  and  K1 <= K2  give  p < K2 .

ltLeTrans : {p K1 K2 : Nat} -> Lt p K1 -> NatLe K1 K2 -> Lt p K2
ltLeTrans (ltZ n)       (le-suc h)   = ltZ _
ltLeTrans (ltS p' n hp) (le-suc hle) = ltS p' _ (ltLeTrans hp hle)

------------------------------------------------------------------------
-- monotonicity of Kle in the level.

kle_mono : (a b x : Nat) -> Kle a x -> NatLe a b -> Kle b x
kle_mono a b x w h =
  mkSg (Sg.fst w)
    (and (ltLeTrans (And.p1 (Sg.snd w)) (pow3_mono (le-suc h)))
         (And.p2 (Sg.snd w)))
