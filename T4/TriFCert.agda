{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriFCert -- packaging the (fully-internal, structure-carrying) object
-- TRIANGLE as a ParCert: for every cert tree c, triF (codeC c) is a valid
-- certificate of  Par (tgt (codeC c)) (devF (src (codeC c)))  =  Par (u, dev t).
-- This bridges the new triF triangle (TriFPres + TriFEnds) to the Par-cert
-- infrastructure (ParReflPres.ParCert, ready for parIntro -> Deriv (Par ..)).

module T4.TriFCert where

open import T4.Base

open import T4.CertTree    using ( CertM ; codeC )
open import T4.ParReflPres using ( ParCert ; mkParCert )
open import T4.ParEnds     using ( src ; tgt ; isCert )
open import T4.TriF        using ( triF )
open import T4.DevF        using ( devF )
open import T4.TriFPres    using ( isCert_triF_M )
open import T4.TriFEnds    using ( src_triF ; tgt_triF )

triFCert : (c : CertM) ->
  ParCert (ap1 tgt (codeC c)) (ap1 devF (ap1 src (codeC c)))
triFCert c =
  mkParCert (ap1 triF (codeC c)) (isCert_triF_M c) (src_triF c) (tgt_triF c)
