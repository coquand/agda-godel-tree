{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14Step3 -- Step 3 of Guard's Theorem 14 proof in BRA4 ,
-- EXACTLY matching guard15.pdf p.17 line 3) :
--
--     th(x) = j   ⊃   th(g(x))  =  "th(x_) = sub(i,i)"   ,    by 1) , 2) .
--
-- BRA4 form (non-parametric ;  F  is fixed in BRA4.Thm.Thm14F ).
-- Universal in  x : Term .  With Guard's helpers  code , encEqF , encThm ,
--  encSub  ( in BRA4.Thm.Thm14F ) :
--
--     P_x x  :=  eqF (ap1 thmT x) j                   -- "th(x) = j"
--
--     step3 :  (x : Term) ->
--              Deriv (imp (P_x x)
--                      (eqF (ap1 thmT (g x))
--                            (encEqF (encThm (code x))
--                                    (encSub (code i) (code i)))))
--                                                       -- "th(x_) = sub(i,i)"
--
-- Construction.  Imp-encoded equality chain through the common middle
-- Term  code j  ( = Guard's  j ).
--   Step 1  :  imp P_x (thmT(Dth(x)) = encEqF (encThm (code x)) (code j))   -- "th(x_) = j"
--   Step 2  :              thmT(Dsub(i,i)) = encEqF (encSub (code i) (code i)) (code j)
--           lifted via  impLift  + flipped via  imp_encoded_eqSym  :
--                       thmT(Df_flipped) = encEqF (code j) (encSub (code i) (code i))
--                                                                            -- "j = sub(i,i)"
--   Chain via imp_encoded_eqTrans with middle  code j .

module BRA4.Thm.Thm14Step3 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.ThmT              using ( thmT )
open import BRA4.SbStep
  using ( InertU ; NumCode ; ncNum ; ncAp1 ; ncAp2 ; sbt_inert_NumCode )
open import BRA4.Sub               using ( sub )
open import BRA4.Thm12.EncodedEqChain
  using ( Df_eqTrans )
open import BRA4.Thm12.EncodedAxEqTrans
  using ( Df_axEqTrans )
open import BRA4.Thm12.EncodedRefl
  using ( Df_refl_meta )
open import BRA4.Thm12.ImpHelpers   using ( impLift )
open import BRA4.Thm12.ImpEncodedEqChain
  using ( imp_encoded_eqSym ; imp_encoded_eqTrans )
open import BRA4.Thm.Thm14F
  using ( i ; j ; code ; encEqF ; encThm ; encSub )
open import BRA4.Thm.Thm14Step1     using ( P_x ; Df_thmT ; step1 )
open import BRA4.Thm.Thm14Step2     using ( Df_sub_ii ; step2 )

------------------------------------------------------------------------
-- The encoded form  "th(x_) = sub(i,i)"  in Guard's exact notation .

codeFXeqYZ : Term -> Term
codeFXeqYZ x = encEqF (encThm (code x)) (encSub (code i) (code i))

------------------------------------------------------------------------
-- Df_flipped_step2  -- the Term whose thmT decodes to
--   encEqF (code j) (encSub (code i) (code i))    -- "j = sub(i,i)"
-- (= Step 2's encEqF direction flipped via imp_encoded_eqSym 's pattern) .

Df_flipped_step2 : Term
Df_flipped_step2 =
  ap2 Pair (natCode tag_mp)
    (ap2 Pair
      (ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans (encSub (code i) (code i))
                                 (code j)
                                 (encSub (code i) (code i)))
                   Df_sub_ii))
      (Df_refl_meta (encSub (code i) (code i))))

------------------------------------------------------------------------
-- g x  =  Guard's combined derivation Term .

g : Term -> Term
g x = Df_eqTrans (Df_thmT x) Df_flipped_step2
                  (encThm (code x)) (code j) (encSub (code i) (code i))

------------------------------------------------------------------------
-- Step 3 .  Guard's "th(x) = j ⊃ th(g(x)) = 'th(x_) = sub(i,i)'" .

step3 :
  (x : Term) ->
  Deriv (imp (P_x x)
              (eqF (ap1 thmT (g x))
                    (codeFXeqYZ x)))
step3 x =
  let
    P : Formula
    P = P_x x

    -- Step 1 .  RHS = encEqF (encThm (code x)) (code j) = "th(x_) = j" .
    step1_imp :
      Deriv (imp P (eqF (ap1 thmT (Df_thmT x))
                         (encEqF (encThm (code x)) (code j))))
    step1_imp = step1 x

    -- Step 2 lifted .  RHS = encEqF (encSub (code i) (code i)) (code j)  =  "sub(i,i) = j" .
    step2_imp :
      Deriv (imp P (eqF (ap1 thmT Df_sub_ii)
                         (encEqF (encSub (code i) (code i)) (code j))))
    step2_imp = impLift {P} step2

    -- InertU witnesses : code t = num t , so every substituent is num-based.
    iEncThmX : InertU (encThm (code x))
    iEncThmX = sbt_inert_NumCode (encThm (code x))
                 (ncAp1 thmT (code x) (ncNum x))

    iCodeJ : InertU (code j)
    iCodeJ = sbt_inert_NumCode (code j) (ncNum j)

    iEncSub : InertU (encSub (code i) (code i))
    iEncSub = sbt_inert_NumCode (encSub (code i) (code i))
                (ncAp2 sub (code i) (code i) (ncNum i) (ncNum i))

    -- Flip Step 2 : "sub(i,i) = j" -> "j = sub(i,i)" .
    step2_flipped :
      Deriv (imp P (eqF (ap1 thmT Df_flipped_step2)
                         (encEqF (code j) (encSub (code i) (code i)))))
    step2_flipped =
      imp_encoded_eqSym P Df_sub_ii
                          (encSub (code i) (code i)) (code j)
                          iEncSub iCodeJ
                          step2_imp

    -- Chain :  "th(x_) = j"  +  "j = sub(i,i)"  =>  "th(x_) = sub(i,i)" .
    step3_imp :
      Deriv (imp P (eqF (ap1 thmT (g x))
                         (encEqF (encThm (code x)) (encSub (code i) (code i)))))
    step3_imp =
      imp_encoded_eqTrans P
        (Df_thmT x) Df_flipped_step2
        (encThm (code x)) (code j) (encSub (code i) (code i))
        iEncThmX iCodeJ iEncSub
        step1_imp step2_flipped

  in step3_imp
