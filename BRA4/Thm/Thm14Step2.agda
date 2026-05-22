{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14Step2 -- Step 2 of Guard's Theorem 14 proof , EXACTLY
-- matching guard15.pdf p.17 line 2) :
--
--     th( Dsub(i,i) )  =  "sub(i,i) = j"   ,    by Th 13 .
--
-- (Guard writes "sub(i,i) = j" ; the underline-on-j is implicit per
--  Definition 12 + the Thm 13 typo correction noted in BRA4.Thm12.Thm13 ;
--  the actual encoded form has  num j  =  j_  on the RHS slot .)
--
-- BRA4 form .  UNCONDITIONAL .  With  i  =  natCode (codeFormulaNat H) ,
-- j = natCode (codeFormulaNat G)  ( BRA4.Thm.Thm14F ) :
--
--    Df_sub_ii  :=  ap2 (fst (thm12_Fun2 sub)) i i      ( = Guard's "Dsub(i, i)" )
--
--    step2 :
--      Deriv (eqF (ap1 thmT Df_sub_ii) (codeFXeqY2 sub i i j))
--                                                       ( = "sub(i,i) = j_" encoded )
--
-- Construction : direct application of thm13_binary at  sub  on the
-- diagonal identity  sub_ii_eq_j  :  Deriv (eqF (ap2 sub i i) j) .

module BRA4.Thm.Thm14Step2 where

open import BRA4.Base
open import BRA4.Sub               using ( sub )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.All         using ( thm12_Fun2 ; fst )
open import BRA4.Thm12.Thm13       using ( codeFXeqY2 ; thm13_binary )
open import BRA4.Thm.Thm14F
  using ( i ; j ; sub_ii_eq_j ; code ; encEqF ; encSub )

------------------------------------------------------------------------
-- Df_sub_ii  =  Guard's  "Dsub(i, i)"  Term .

Df_sub_ii : Term
Df_sub_ii = ap2 (fst (thm12_Fun2 sub)) i i

------------------------------------------------------------------------
-- Step 2 .  Guard's  "th( Dsub(i,i) ) = 'sub(i,i) = j'"  EXACTLY .
--
-- The RHS  encEqF (encSub (code i) (code i)) (code j)  is the encoded
-- form of Guard ' s  "sub(i, i) = j"  with all of  i , i , j  in the
-- encoded slots reading as  num applied  ( per Definition 12 + the
-- numeral-Goedel-handle convention) .  The Deriv body uses  thm13_binary
-- whose natural output is
--   codeFXeqY2 sub i i j  =  ap2 Pair (natCode tag_eq) (ap2 Pair (encSub-shape) (ap1 num j))
-- which is DEFINITIONALLY EQUAL to  encEqF (encSub (code i) (code i)) (code j) .

step2 :
  Deriv (eqF (ap1 thmT Df_sub_ii)
              (encEqF (encSub (code i) (code i)) (code j)))
step2 = thm13_binary sub i i j sub_ii_eq_j
