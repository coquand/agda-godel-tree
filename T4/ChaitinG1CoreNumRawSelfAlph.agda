{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1CoreNumRawSelfAlph -- the x-free, self-referential form of
-- CGI_core_num_raw_Alph  ( analog of  T4.ChaitinG1CoreNumRawSelf ).

open import T4.Base

module T4.ChaitinG1CoreNumRawSelfAlph (Lstar_meta : Nat) where

open import T4.Code             using ( codeFalse )
open import T4.ThmT             using ( thmT )
open import T4.KdefAlph Lstar_meta using ( KcodeAlph )
open import T4.KdefRecogAlph Lstar_meta using ( outKdefAlph )
open import T4.KdefDiagAlph Lstar_meta using ( gLcodeDefAlph )
open import T4.CheckAlphN       using ( checkAlphN )
open import T4.ProgEnc          using ( enc )
open import T4.ChaitinG1CoreNumRawAlph Lstar_meta
  using ( CGI_core_num_raw_Alph ; Sigma ; mkSigma ; fst ; snd )

CGI_core_num_raw_self_Alph :
  Deriv (eqF (ap1 (checkAlphN Lstar_meta) (enc gLcodeDefAlph)) (ap1 s O)) ->
  (w : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeAlph (ap1 outKdefAlph w))) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
CGI_core_num_raw_self_Alph checkFires w h =
  CGI_core_num_raw_Alph checkFires w (ap1 outKdefAlph w) h
