{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ChaitinG1CoreNumRawSelf -- the  x -free, self-referential form of
-- CGI_core_num_raw .
--
-- Whether  thmT w  is of the form  ap1 (Kcode Lstar) _  is decided by the
--  outKdef Lstar  read-back ( decode . projKdef . thmT , BRA4.KdefRecog ).
-- When  Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))  holds, the subject
-- slot reads off as  ap1 (outKdef Lstar) w = x  (an internal Deriv).  So
-- the original  (x : Term)  parameter is redundant -- we can absorb it by
-- demanding the hypothesis already in self-referential form
--
--   Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w))) .
--
-- The derivation is one line:  call  CGI_core_num_raw  with
--  x := ap1 (outKdef Lstar) w .

module BRA4.ChaitinG1CoreNumRawSelf where

open import BRA4.Base
open import BRA4.Code             using ( codeFalse )
open import BRA4.ThmT             using ( thmT )
open import BRA4.Kdef             using ( Kcode )
open import BRA4.KdefRecog        using ( outKdef )
open import BRA4.KGodel1BridgeDef using ( Lstar )
open import BRA4.ChaitinG1CoreNumRaw
  using ( CGI_core_num_raw ; Sigma ; mkSigma ; fst ; snd )

------------------------------------------------------------------------
-- CGI_core_num_raw_self -- the  x -free form.

CGI_core_num_raw_self :
  (w : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w))) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
CGI_core_num_raw_self w h =
  CGI_core_num_raw w (ap1 (outKdef Lstar) w) h
