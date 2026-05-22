{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.CodeFTeq -- the asymmetric encoded equation target for
-- Theorem 12 (singulary case).
--
--   codeFTeq1 f x  =  asymmetric encoding of  "f(num x) = num(f x)"
--
-- The "asymmetric" piece is that  ap1 num x  is a TERM-level leaf
-- inside the Pair structure, NOT codeTerm of  ap1 num x .  This is
-- the same convention as BRA3.Thm.Thm12.CodeFTeq , and is what
-- the thmT cascade in PartU / PartO / PartS actually produces
-- (sbt_at_var_match plops the raw substituent into the slot ; it
-- does NOT codeTerm-wrap).

module BRA4.Thm12.CodeFTeq where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code  using ( codeFun1 ; codeFun2 )
open import BRA4.Num   using ( num )

------------------------------------------------------------------------
-- codeFTeq1 f x
--   =  Pair tag_eq
--        (Pair (Pair tag_ap1 (Pair (codeFun1 f) (num x)))
--              (num (f x)))

codeFTeq1 : Fun1 -> Term -> Term
codeFTeq1 f x =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (ap1 num x)))
              (ap1 num (ap1 f x)))

------------------------------------------------------------------------
-- codeFTeq2 g x y  =  asymmetric encoding of  "g(num x, num y) = num(g x y)"
--
--   = Pair tag_eq
--       (Pair (Pair tag_ap2 (Pair (codeFun2 g) (Pair (num x) (num y))))
--             (num (g x y)))

codeFTeq2 : Fun2 -> Term -> Term -> Term
codeFTeq2 g x y =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair (ap1 num x) (ap1 num y))))
              (ap1 num (ap2 g x y)))
