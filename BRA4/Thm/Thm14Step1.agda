{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm.Thm14Step1 -- Step 1 of Guard's Theorem 14 proof , EXACTLY
-- matching guard15.pdf p.16 / 17 line 1) :
--
--     th(x) = j   ⊃   th(Dth(x))  =  "th(x_) = j_"   ,    by Th 13 .
--
-- (Guard writes "th(x_) = j" ; the underline-on-j is implicit per
--  Definition 12 + the typo correction noted in BRA4.Thm12.Thm13 .)
--
-- BRA4 form (non-parametric ;  F  is fixed in BRA4.Thm.Thm14F ).
-- Universal in  x : Term .  With  j = natCode jNat = natCode (codeFormulaNat G) :
--
--     P_x x  :=  eqF (ap1 thmT x) j                  -- "th(x) = j"
--
--     step1 :  (x : Term) ->
--              Deriv (imp (P_x x)
--                      (eqF (ap1 thmT (Df_thmT x))
--                            (codeFXeqY1 thmT x j)))     -- "th(x_) = j_"
--
-- Construction.  Carneiro-lifted  thm13_singulary  at  thmT  with the
-- "consequent" cF specialised to  j  .

module BRA4.Thm.Thm14Step1 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 )
open import BRA4.Num               using ( num )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 )
open import BRA4.Thm12.All         using ( thm12 ; fst ; snd )
open import BRA4.Thm12.Thm13       using ( codeFXeqY1 )
open import BRA4.Thm12.ImpHelpers
  using ( impLift ; impRefl ; impCong1 ; impCongR ; impEqTrans )
open import BRA4.Thm.Thm14F        using ( j ; code ; encEqF ; encThm )

------------------------------------------------------------------------
-- Carneiro-lifted thm13 at a general Fun1 .  Reusable helper .

thm13_singulary_imp :
  (P : Formula) (f : Fun1) (x y : Term) ->
  Deriv (imp P (eqF (ap1 f x) y)) ->
  Deriv (imp P (eqF (ap1 thmT (ap1 (fst (thm12 f)) x))
                     (codeFXeqY1 f x y)))
thm13_singulary_imp P f x y hyp_imp =
  let
    p_f = thm12 f
    Df = fst p_f
    ih = snd p_f

    e_thm12 : Deriv (eqF (ap1 thmT (ap1 Df x)) (codeFTeq1 f x))
    e_thm12 = ih x

    e_thm12_imp : Deriv (imp P (eqF (ap1 thmT (ap1 Df x)) (codeFTeq1 f x)))
    e_thm12_imp = impLift {P} e_thm12

    num_bridge_imp :
      Deriv (imp P (eqF (ap1 num (ap1 f x)) (ap1 num y)))
    num_bridge_imp = impCong1 {P} num (ap1 f x) y hyp_imp

    codeApSlot : Term
    codeApSlot =
      ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) (ap1 num x))

    inner_pair_imp :
      Deriv (imp P (eqF (ap2 Pair codeApSlot (ap1 num (ap1 f x)))
                         (ap2 Pair codeApSlot (ap1 num y))))
    inner_pair_imp = impCongR {P} Pair (ap1 num (ap1 f x)) (ap1 num y)
                                codeApSlot num_bridge_imp

    outer_bridge_imp :
      Deriv (imp P (eqF (codeFTeq1 f x) (codeFXeqY1 f x y)))
    outer_bridge_imp =
      impCongR {P} Pair
        (ap2 Pair codeApSlot (ap1 num (ap1 f x)))
        (ap2 Pair codeApSlot (ap1 num y))
        (natCode tag_eq) inner_pair_imp

  in impEqTrans {P}
       (ap1 thmT (ap1 Df x)) (codeFTeq1 f x) (codeFXeqY1 f x y)
       e_thm12_imp outer_bridge_imp

------------------------------------------------------------------------
-- Guard's hypothesis  "th(x) = j"  ,  EXACTLY .

P_x : Term -> Formula
P_x x = eqF (ap1 thmT x) j

------------------------------------------------------------------------
-- Df_thmT x  -- Guard's "Dth(x)"  Term .

Df_thmT : Term -> Term
Df_thmT x = ap1 (fst (thm12 thmT)) x

------------------------------------------------------------------------
-- Step 1 .  Guard's "th(x) = j ⊃ th(Dth(x)) = 'th(x_) = j'"  EXACTLY .
--
-- The RHS  encEqF (encThm (code x)) (code j)   is the encoded form of
-- Guard's  "th(x_) = j"  with  x_ = num x = code x  ( per Def 12 ) and
--  j = num j = code j  (per Guard's numeral-Goedel-handle convention) .
-- The Deriv body uses  thm13_singulary_imp  whose natural output is
--  codeFXeqY1 thmT x j  = ap2 Pair (natCode tag_eq) (ap2 Pair (ap2 Pair (natCode tag_ap1)
--                          (ap2 Pair (codeFun1 thmT) (ap1 num x))) (ap1 num j))
-- which is DEFINITIONALLY EQUAL to encEqF (encThm (code x)) (code j) .

step1 :
  (x : Term) ->
  Deriv (imp (P_x x)
              (eqF (ap1 thmT (Df_thmT x))
                    (encEqF (encThm (code x)) (code j))))
step1 x =
  thm13_singulary_imp (P_x x) thmT x j (impRefl (P_x x))
