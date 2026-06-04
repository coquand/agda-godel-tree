{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiDPosFun1 -- the Fun1-based dPos for the CGI clash.
--
-- Applies Thm 13 (singulary) at  (f := g_L , X := w , Y := s (subjOf w x hyp))
-- to internalise the meta-Deriv  g_L w = s (subjOf w x hyp)  as the thmT-level
-- fact
--
--   thmT( ap1 (Df_gL) w ) = codeFXeqY1 g_L w (s (subjOf w x hyp))
--                         = code( g_L (num w) = num (s (subjOf w x hyp)) )
--                         = code( g_L (num w) = s (num (subjOf w x hyp)) )    [num_at_S]
--                         = code( g_L (num w) = s ((subjOf w x hyp)_) ) .
--
-- This is the positive leg of the chaitin clash, derived WITHOUT walking
-- evalU and WITHOUT K-management.

module T4.CgiDPosFun1 where

open import T4.Base
open import T4.ThmT          using ( thmT )
open import T4.Kdef          using ( Kcode )
open import T4.Num           using ( num ; num_at_S )
open import T4.SearchFun1    using ( g_L ; gL_at_w ; subjOfFromHit )
open import T4.KdefRecog     using ( hitKdef_fires ; outKdef ; hitKdef )
open import T4.KGodel1Bridge using ( Lstar )
open import T4.Thm12.Thm13   using ( codeFXeqY1 ; thm13_singulary )
open import T4.Thm12.All     using ( thm12 ; fst )

------------------------------------------------------------------------
-- The dPos proof code:  ap1 (Df_gL) w  where Df_gL = fst (thm12 g_L).

cPosFun1 : Term -> Term
cPosFun1 w = ap1 (fst (thm12 g_L)) w

-- The dPos thmT-fact: T proves  g_L(num w) = s (num (subj))  via Thm 13.
dPosFun1 :
  (w x : Term) ->
  (hyp : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))) ->
  Deriv (eqF (ap1 thmT (cPosFun1 w))
              (codeFXeqY1 g_L w (ap1 s (subjOfFromHit w x (hitKdef_fires Lstar w x hyp)))))
dPosFun1 w x hyp =
  thm13_singulary g_L w (ap1 s (subjOfFromHit w x (hitKdef_fires Lstar w x hyp)))
    (gL_at_w w x hyp)
