{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DListGL -- the dPos sequence builder for the Fun1-route CGI.
--
-- For the list-based definable
--   definable p s x n  :=  s = <wn, w(n-1), ..., w0, 0>  with
--     thmT(wn) = code(p(num n) = num(s x))         -- halt at top (= head)
--     thmT(wi) = code(p(num i) = num 0)            -- looping below (i < n)
--
-- the dPos at  g_L  supplies the specific list of Thm 12 proof codes.  Define
-- the list-builders as R-recursive Fun1's:
--
--   dList_loops O      = O                                       -- empty endmarker
--   dList_loops (s n') = Pair (D_gL n') (dList_loops n')          -- looping sublist
--
--   dList_full n  = Pair (D_gL n) (dList_loops n)                 -- halt on top + loopings
--
-- where  D_gL = fst (thm12 g_L)  is the Thm 12 proof builder for the Fun1
-- g_L : Fun1 .
--
-- This file establishes the Fun1 structure and the R-equations  dList_loops_at_O
-- and  dList_loops_at_S , and  dList_full_eq .

module T4.DListGL where

open import T4.Base
open import T4.SearchFun1 using ( g_L )
open import T4.Thm12.All  using ( thm12 ; fst )

open import BRA3.Fan         using ( Lift1 )
open import BRA3.PairAlgebra using ( axFan ; axLift )

------------------------------------------------------------------------
-- SECTION 1.  The Thm 12 proof builder for g_L.

D_gL : Fun1
D_gL = fst (thm12 g_L)

------------------------------------------------------------------------
-- SECTION 2.  dList_loops : Fun1  --  the looping sublist.
--
--   dList_loops O      = O
--   dList_loops (s n') = Pair (D_gL n') (dList_loops n')
--
-- Build as  R o stepFun v  (single-arg Fun1 via the C wrapping below):
--
--   stepFun(n', prev) = Pair (D_gL n') prev
--                     = ap2 Pair (ap1 D_gL n') prev .
--
-- As Fun2:  stepFun = Fan (Lift1 D_gL) v Pair .

stepFun : Fun2
stepFun = Fan (Lift1 D_gL) v Pair

stepFun_eq :
  (n' prev : Term) ->
  Deriv (eqF (ap2 stepFun n' prev) (ap2 Pair (ap1 D_gL n') prev))
stepFun_eq n' prev =
  let e1 : Deriv (eqF (ap2 stepFun n' prev)
                       (ap2 Pair (ap2 (Lift1 D_gL) n' prev) (ap2 v n' prev)))
      e1 = axFan (Lift1 D_gL) v Pair n' prev
      e2 : Deriv (eqF (ap2 (Lift1 D_gL) n' prev) (ap1 D_gL n'))
      e2 = axLift D_gL n' prev
      e3 : Deriv (eqF (ap2 v n' prev) prev)
      e3 = ax_v n' prev
  in ruleTrans e1
       (ruleTrans (congL Pair (ap2 v n' prev) e2)
                  (congR Pair (ap1 D_gL n') e3))

-- The unary Fun1 wrapping the R-Fun2.
dList_loops_F2 : Fun2
dList_loops_F2 = R o stepFun v

dList_loops : Fun1
dList_loops = C dList_loops_F2 o u

------------------------------------------------------------------------
-- SECTION 3.  R-equations for  dList_loops .

dList_loops_unfold :
  (n : Term) ->
  Deriv (eqF (ap1 dList_loops n) (ap2 dList_loops_F2 O n))
dList_loops_unfold n =
  let e1 : Deriv (eqF (ap1 dList_loops n)
                       (ap2 dList_loops_F2 (ap1 o n) (ap1 u n)))
      e1 = ax_C dList_loops_F2 o u n
      e2 : Deriv (eqF (ap2 dList_loops_F2 (ap1 o n) (ap1 u n))
                       (ap2 dList_loops_F2 O (ap1 u n)))
      e2 = congL dList_loops_F2 (ap1 u n) (ax_o n)
      e3 : Deriv (eqF (ap2 dList_loops_F2 O (ap1 u n))
                       (ap2 dList_loops_F2 O n))
      e3 = congR dList_loops_F2 O (ax_u n)
  in ruleTrans e1 (ruleTrans e2 e3)

dList_loops_at_O : Deriv (eqF (ap1 dList_loops O) O)
dList_loops_at_O =
  ruleTrans (dList_loops_unfold O)
            (ruleTrans (ax_R_base o stepFun v O) (ax_o O))

dList_loops_at_S :
  (n : Term) ->
  Deriv (eqF (ap1 dList_loops (ap1 s n))
              (ap2 Pair (ap1 D_gL n) (ap1 dList_loops n)))
dList_loops_at_S n =
  let unfold : Deriv (eqF (ap1 dList_loops (ap1 s n))
                          (ap2 dList_loops_F2 O (ap1 s n)))
      unfold = dList_loops_unfold (ap1 s n)
      rstep : Deriv (eqF (ap2 dList_loops_F2 O (ap1 s n))
                          (ap2 stepFun (ap2 v O n) (ap2 dList_loops_F2 O n)))
      rstep = ax_R_step o stepFun v O n
      rstep' : Deriv (eqF (ap2 stepFun (ap2 v O n) (ap2 dList_loops_F2 O n))
                           (ap2 stepFun n (ap2 dList_loops_F2 O n)))
      rstep' = congL stepFun (ap2 dList_loops_F2 O n) (ax_v O n)
      eval : Deriv (eqF (ap2 stepFun n (ap2 dList_loops_F2 O n))
                         (ap2 Pair (ap1 D_gL n) (ap2 dList_loops_F2 O n)))
      eval = stepFun_eq n (ap2 dList_loops_F2 O n)
      backToFun1 : Deriv (eqF (ap2 dList_loops_F2 O n) (ap1 dList_loops n))
      backToFun1 = ruleSym (dList_loops_unfold n)
      finalCong : Deriv (eqF (ap2 Pair (ap1 D_gL n) (ap2 dList_loops_F2 O n))
                              (ap2 Pair (ap1 D_gL n) (ap1 dList_loops n)))
      finalCong = congR Pair (ap1 D_gL n) backToFun1
  in ruleTrans unfold
       (ruleTrans rstep
         (ruleTrans rstep' (ruleTrans eval finalCong)))

------------------------------------------------------------------------
-- SECTION 4.  dList_full : Fun1  --  the full witness list (halt at top,
-- loopings below).
--
--   dList_full n  =  Pair (D_gL n) (dList_loops n)
--
-- As a Fun1:  C Pair D_gL dList_loops .

dList_full : Fun1
dList_full = C Pair D_gL dList_loops

dList_full_eq :
  (n : Term) ->
  Deriv (eqF (ap1 dList_full n) (ap2 Pair (ap1 D_gL n) (ap1 dList_loops n)))
dList_full_eq n = ax_C Pair D_gL dList_loops n
