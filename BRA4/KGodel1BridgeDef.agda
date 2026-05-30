{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KGodel1BridgeDef -- the Kdef-shape parallel of BRA4.KGodel1Bridge .
--
-- KGodel1Bridge pins the Size module's tc-checker to  tc := thmT  and
-- exports the canonical Kgt-shape threshold  Lstar := exp2 (natCode
-- (fst bound)) , with  bridge : gLcode Lstar == plug Cmcodeb (H (fst bound))
-- a sealed refl.
--
-- This file does the same for the Kdef-shape:
--   SzDef := SizeDef thmT  (so  gLcodeDefP thmT  is  KdefDiag.gLcodeDef ),
--   LstarDef := exp2 (natCode (fst boundDef)) ,
--   bridgeDef : gLcodeDef LstarDef == plug CmcodebDef (H (fst boundDef)) .
--
-- The Discharge/Chain modules (and CGI_core_num_raw_parametric -> the
-- residual-less version) import Lstar FROM HERE instead of from
-- KGodel1Bridge, so the same name binds to the Kdef-shape threshold.

module BRA4.KGodel1BridgeDef where

open import BRA4.Base
open import BRA4.ThmT        using ( thmT )
open import BRA4.KdefDiag    using ( gLcodeDef )
open import BRA4.ProgNodes   using ( plug )
open import BRA4.Exp         using ( exp2 )
open import BRA4.GLCodeNodes using ( H )
open import BRA4.NatExp      using ( Sg ; fst )

import BRA4.GLCodePDef

-- ONE shared instantiation of the SizeDef module, re-exported.
module SzDef = BRA4.GLCodePDef.SizeDef thmT
open SzDef public using ( CmcodebDef ; boundDef ; dLen_gen ; dLenDef )

Lstar : Term
Lstar = ap1 exp2 (natCode (fst boundDef))

abstract
  bridgeDef : Eq (gLcodeDef Lstar) (plug CmcodebDef (H (fst boundDef)))
  bridgeDef = refl
