{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTContract -- the bundled contract module re-exporting all
-- 17 closures of the thmT verifier :
--
--   * thmT_at_O           -- base case  ap1 thmT O = codeTriv.
--   * thmT_at_sb          -- sb closure (universal form).
--   * thmT_at_mp          -- mp closure (universal form).
--   * thmT_at_mp_codeF    -- mp corollary (codeFormula-specialised).
--   * thmT_at_ind         -- ind closure (universal form).
--   * thmT_at_ind_codeF   -- ind corollary (codeFormula-specialised).
--   * thmT_at_axN0..N13   -- 14 ax sub-closures.
--
-- All closures in UNIVERSAL form (sub-proof values are arbitrary Terms,
-- well-formedness witnesses are separate Deriv hyps, outputs are raw
-- Term expressions).  Per
-- [[feedback-bra4-closures-universal-form]] : no codeFormula assumptions
-- are baked in at the closure-type level.
--
-- Consumers (e.g.  BRA4.ThmTComplete  's  encode + thmT_complete
-- implementation) just `open import BRA4.ThmTContract` and have all 17
-- closures + base case in scope.

module BRA4.ThmTContract where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.SbF        using ( sbf )
open import BRA4.ThmT       public using ( thmT ; thmT_at_O )

open import BRA4.ThmTAtSb   public using ( thmT_at_sb )
open import BRA4.ThmTAtMp   public using ( thmT_at_mp ; thmT_at_mp_codeF )
open import BRA4.ThmTAtInd  public using ( thmT_at_ind ; thmT_at_ind_codeF )
open import BRA4.ThmTAtAx0  public using ( thmT_at_axN0 )
open import BRA4.ThmTAtAx1  public using ( thmT_at_axN1 )
open import BRA4.ThmTAtAx2  public using ( thmT_at_axN2 )
open import BRA4.ThmTAtAx3  public using ( thmT_at_axN3 )
open import BRA4.ThmTAtAx4  public using ( thmT_at_axN4 )
open import BRA4.ThmTAtAx5  public using ( thmT_at_axN5 )
open import BRA4.ThmTAtAx6  public using ( thmT_at_axN6 )
open import BRA4.ThmTAtAx7  public using ( thmT_at_axN7 )
open import BRA4.ThmTAtAx8  public using ( thmT_at_axN8 )
open import BRA4.ThmTAtAx9  public using ( thmT_at_axN9 )
open import BRA4.ThmTAtAx10 public using ( thmT_at_axN10 )
open import BRA4.ThmTAtAx11 public using ( thmT_at_axN11 )
open import BRA4.ThmTAtAx12 public using ( thmT_at_axN12 )
open import BRA4.ThmTAtAx13 public using ( thmT_at_axN13 )
