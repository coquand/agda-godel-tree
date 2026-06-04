{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SearchFun1 -- the surprise.pdf loop g_L as a Fun1 (no evalU walk).
--
-- For chaitin_G1's run, we do NOT walk evalU through the encoded mu-program.
-- Instead we package the loop's per-step semantics as a Fun1
--
--   g_L : Fun1
--   g_L x  =  s (outKdef Lstar (Search.g (s x)))
--
-- where Search.g is the FirstHit.Search.g recursor at predicate
-- pK = hitKdef Lstar (outKdef Lstar) -- the recogniser that the chaitin
-- hypothesis fires.  At x = w (the witness from chaitin_G1's hyp),
--
--   g_L w  =  s (outKdef Lstar (Search.g (s w)))
--          =  s (outKdef Lstar w0)            -- w0 = first hit position
--          =  s (subjOf w x hyp)              -- the read-off subject
--
-- a meta-Deriv proved by three compose1U unfolds + one C-unfold of  g_unary .
--
-- Thm 13 (singulary) at  (f := g_L , x := w , z := s (subjOf w x hyp))  then
-- internalises this meta-Deriv as the dPos thmT-fact -- no evalU, no stepU,
-- no K-management.

module T4.SearchFun1 where

open import T4.Base
open import T4.KdefRecog   using ( hitKdef ; outKdef ; hitKdef_le_one ; hitKdef_fires )
open import T4.Kdef        using ( Kcode )
open import T4.ThmT        using ( thmT )
open import T4.KGodel1Bridge using ( Lstar )
open import T4.FirstHit    using ( module Search )

open import BRA3.Fan         using ( compose1U ; compose1U_eq )
open import BRA3.ChurchLeq   using ( leq )

------------------------------------------------------------------------
-- SECTION 1.  The hit predicate and the Search instance.

pK : Fun1
pK = hitKdef Lstar (outKdef Lstar)

pK_le_one : (r : Term) -> Deriv (leq (ap1 pK r) (ap1 s O))
pK_le_one = hitKdef_le_one Lstar (outKdef Lstar)

open Search pK pK_le_one using ( gRec ; g ; LeastNumber ; leastNumber )

------------------------------------------------------------------------
-- SECTION 2.  g_unary : Fun1 -- a Fun1 wrapper around  g .
--
--   Search.g r  =  ap2 gRec O r    (Term -> Term, meta level)
--
-- The Fun1  g_unary = C gRec o u  has  ap1 g_unary r = ap2 gRec O r .

g_unary : Fun1
g_unary = C gRec o u

g_unary_eq : (r : Term) -> Deriv (eqF (ap1 g_unary r) (ap2 gRec O r))
g_unary_eq r =
  let e1 : Deriv (eqF (ap1 g_unary r) (ap2 gRec (ap1 o r) (ap1 u r)))
      e1 = ax_C gRec o u r
      e2 : Deriv (eqF (ap2 gRec (ap1 o r) (ap1 u r)) (ap2 gRec O (ap1 u r)))
      e2 = congL gRec (ap1 u r) (ax_o r)
      e3 : Deriv (eqF (ap2 gRec O (ap1 u r)) (ap2 gRec O r))
      e3 = congR gRec O (ax_u r)
  in ruleTrans e1 (ruleTrans e2 e3)

-- g_unary equals Search.g at every argument.
g_unary_is_g : (r : Term) -> Deriv (eqF (ap1 g_unary r) (g r))
g_unary_is_g r = g_unary_eq r
-- (Search.g r is DEFINITIONALLY ap2 gRec O r ; the Deriv is the same.)

------------------------------------------------------------------------
-- SECTION 3.  g_L : Fun1 -- the surprise.pdf loop, packaged as a Fun1.
--
--   g_L x  =  s (outKdef Lstar (g_unary (s x)))
--         =  s (outKdef Lstar (Search.g (s x)))

g_L : Fun1
g_L = compose1U s (compose1U (outKdef Lstar) (compose1U g_unary s))

------------------------------------------------------------------------
-- SECTION 4.  The meta-Deriv  g_L w = s (outKdef Lstar (g (s w))) .
--
-- Pure compose1U-unfolding; no stepU, no induction, no K-management.

gL_at : (w : Term) ->
        Deriv (eqF (ap1 g_L w) (ap1 s (ap1 (outKdef Lstar) (g (ap1 s w)))))
gL_at w =
  let inner3 : Deriv (eqF (ap1 (compose1U g_unary s) w) (ap1 g_unary (ap1 s w)))
      inner3 = compose1U_eq g_unary s w
      inner3' : Deriv (eqF (ap1 (compose1U g_unary s) w) (g (ap1 s w)))
      inner3' = ruleTrans inner3 (g_unary_is_g (ap1 s w))
      inner2 : Deriv (eqF (ap1 (compose1U (outKdef Lstar) (compose1U g_unary s)) w)
                          (ap1 (outKdef Lstar) (ap1 (compose1U g_unary s) w)))
      inner2 = compose1U_eq (outKdef Lstar) (compose1U g_unary s) w
      inner2' : Deriv (eqF (ap1 (compose1U (outKdef Lstar) (compose1U g_unary s)) w)
                           (ap1 (outKdef Lstar) (g (ap1 s w))))
      inner2' = ruleTrans inner2 (cong1 (outKdef Lstar) inner3')
      outer : Deriv (eqF (ap1 g_L w)
                          (ap1 s (ap1 (compose1U (outKdef Lstar) (compose1U g_unary s)) w)))
      outer = compose1U_eq s (compose1U (outKdef Lstar) (compose1U g_unary s)) w
  in ruleTrans outer (cong1 s inner2')

------------------------------------------------------------------------
-- SECTION 5.  At the chaitin witness  w , this is exactly the read-off
--   subject  subjOf w x hyp  (= outKdef Lstar (firstHit w x hyp)) wrapped
--   in  s , and  firstHit w x hyp = g (s w)  by LeastNumber.w1.

firstHitInternal : (w x : Term) ->
                   Deriv (eqF (ap1 pK w) (ap1 s O)) ->
                   Term
firstHitInternal w x hitAtW = LeastNumber.w1 (leastNumber w hitAtW)

-- firstHitInternal w x hitAtW  =  g (s w)  -- by leastNumber's defn.

subjOfFromHit : (w x : Term) ->
                Deriv (eqF (ap1 pK w) (ap1 s O)) ->
                Term
subjOfFromHit w x hitAtW = ap1 (outKdef Lstar) (firstHitInternal w x hitAtW)

------------------------------------------------------------------------
-- SECTION 6.  The chaitin-shape meta-Deriv:
--
--   gL_at_w :  Deriv (eqF (ap1 g_L w) (ap1 s (subjOf w x hyp)))
--
-- where  subjOf w x hyp  = ap1 (outKdef Lstar) (firstHit w x hyp)
--                       = ap1 (outKdef Lstar) (g (s w))
-- via the hyp -> hit -> leastNumber chain.

gL_at_w : (w x : Term) ->
          (hyp : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))) ->
          Deriv (eqF (ap1 g_L w) (ap1 s (subjOfFromHit w x (hitKdef_fires Lstar w x hyp))))
gL_at_w w x hyp = gL_at w
