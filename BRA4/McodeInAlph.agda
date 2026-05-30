{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.McodeInAlph -- Phase E4, step R4: every program code  mcode f  lies in
-- the  {O, ap1 s, ap2 pi}  fragment  InAlph  (BRA4.ProgParse), so the decoder
-- round-trip  parse (enc (mcode f)) = mcode f  applies.
--
--   inAlph_mcode1 : (f : Fun1) -> InAlph (mcode1 f)
--   inAlph_mcode2 : (g : Fun2) -> InAlph (mcode2 g)
--   inAlph_mcodeMu : InAlph gc -> InAlph (mcodeMu gc)
--
-- These are the GENERAL "mcode is in the fragment" lemmas; applied to the
-- diagonal  ⌜g_L⌝  they discharge the abstract round-trip  dRT  of
-- BRA4.KGodel1 / BRA4.KDiag.  Note: an application like  inAlph_mcode1 thmT  is
-- a small term -- it is the GENERAL lemma instantiated, NOT a traversal of
-- thmT's combinator tree (Agda does not normalise it during type-checking).

module BRA4.McodeInAlph where

open import BRA4.Base
open import BRA4.Tags  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )
open import BRA4.EvalU using ( mcode1 ; mcode2 ; mcodeMu ; tag_mu )
open import BRA4.ProgParse using ( InAlph ; iaO ; iaS ; iaPi )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- Numeral codes (s-chains over O) are in the fragment.

inAlph_natCode : (n : Nat) -> InAlph (natCode n)
inAlph_natCode zero    = iaO
inAlph_natCode (suc n) = iaS (natCode n) (inAlph_natCode n)

------------------------------------------------------------------------
-- mcode is in the fragment (mutual structural recursion on Fun1 / Fun2).

inAlph_mcode1 : (f : Fun1) -> InAlph (mcode1 f)
inAlph_mcode2 : (g : Fun2) -> InAlph (mcode2 g)

inAlph_mcode1 s = iaPi (natCode tag_s) O (inAlph_natCode tag_s) iaO
inAlph_mcode1 o = iaPi (natCode tag_o) O (inAlph_natCode tag_o) iaO
inAlph_mcode1 u = iaPi (natCode tag_u) O (inAlph_natCode tag_u) iaO
inAlph_mcode1 (C g h1 h2) =
  iaPi (natCode tag_C) (ap2 pi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2)))
    (inAlph_natCode tag_C)
    (iaPi (mcode2 g) (ap2 pi (mcode1 h1) (mcode1 h2))
      (inAlph_mcode2 g)
      (iaPi (mcode1 h1) (mcode1 h2) (inAlph_mcode1 h1) (inAlph_mcode1 h2)))

inAlph_mcode2 v = iaPi (natCode tag_v) O (inAlph_natCode tag_v) iaO
inAlph_mcode2 (R g h1 h2) =
  iaPi (natCode tag_R) (ap2 pi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2)))
    (inAlph_natCode tag_R)
    (iaPi (mcode1 g) (ap2 pi (mcode2 h1) (mcode2 h2))
      (inAlph_mcode1 g)
      (iaPi (mcode2 h1) (mcode2 h2) (inAlph_mcode2 h1) (inAlph_mcode2 h2)))

------------------------------------------------------------------------
-- The mu-wrapper:  mcodeMu gc = pi (natCode tag_mu) gc .

inAlph_mcodeMu : (gc : Term) -> InAlph gc -> InAlph (mcodeMu gc)
inAlph_mcodeMu gc iagc = iaPi (natCode tag_mu) gc (inAlph_natCode tag_mu) iagc
