{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartVF2 -- Theorem 12, v case with  Df_v_F2 : Fun2 .
--
--   Df_v_F2 : Fun2
--   ap2 Df_v_F2 X Y =Deriv= Df_v X Y
--
--   thm12_v_F2 :
--     (X Y : Term) ->
--     Deriv (eqF (ap1 thmT (ap2 Df_v_F2 X Y)) (codeFTeq2 v X Y))
--
-- Building blocks (private) :
--   pairF2 f g = Fan f g Pair
--   kF2  c    = Lift1 (kF1 c)        -- always returns the closed Term  c
--   numF2_first  = Lift1 num         -- ap2 _ X Y = num X
--   numF2_second = Lift2 num         -- ap2 _ X Y = num Y

module BRA4.Thm12.PartVF2 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Num               using ( num )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq2 )
open import BRA4.Thm12.PartV       using ( Df_v ; thm12_v )
open import BRA4.Thm12.PartRStep
  using ( kF1 ; kF1_eq_closed )
open import BRA3.Dispatch          using ( closed_ap2 )

------------------------------------------------------------------------
-- Closure of  packAx3_O .

private
  N3 : Nat
  N3 = suc (suc (suc zero))

  packAx3_O : Term
  packAx3_O =
    ap2 Pair (natCode tag_ax) (ap2 Pair (natCode N3) O)

  closed_packAx3_O : Closed packAx3_O
  closed_packAx3_O =
    closed_ap2 Pair (natCode tag_ax) _
      (closed_natCode tag_ax)
      (closed_ap2 Pair (natCode N3) O
        (closed_natCode N3) closed_O)

------------------------------------------------------------------------
-- Fun2 building blocks.

private
  pairF2 : Fun2 -> Fun2 -> Fun2
  pairF2 f g = Fan f g Pair

  pairF2_eq :
    (f g : Fun2) (X Y : Term) ->
    Deriv (eqF (ap2 (pairF2 f g) X Y) (ap2 Pair (ap2 f X Y) (ap2 g X Y)))
  pairF2_eq f g X Y = axFan f g Pair X Y

  kF2 : Term -> Fun2
  kF2 c = Lift1 (kF1 c)

  kF2_eq_closed :
    (c : Term) -> Closed c -> (X Y : Term) ->
    Deriv (eqF (ap2 (kF2 c) X Y) c)
  kF2_eq_closed c cl X Y =
    ruleTrans (axLift (kF1 c) X Y) (kF1_eq_closed c cl X)

  numF2_first : Fun2
  numF2_first = Lift1 num

  numF2_first_eq :
    (X Y : Term) -> Deriv (eqF (ap2 numF2_first X Y) (ap1 num X))
  numF2_first_eq X Y = axLift num X Y

  numF2_second : Fun2
  numF2_second = Lift2 num

  numF2_second_eq :
    (X Y : Term) -> Deriv (eqF (ap2 numF2_second X Y) (ap1 num Y))
  numF2_second_eq X Y = axLift2 num X Y

------------------------------------------------------------------------
-- Df_v_F2 .

private
  innerSpec : Fun2
  innerSpec =
    pairF2 (pairF2 (kF2 (natCode zero)) numF2_first)
           (pairF2 (kF2 (natCode (suc zero))) numF2_second)

  midF2 : Fun2
  midF2 = pairF2 innerSpec (kF2 packAx3_O)

Df_v_F2 : Fun2
Df_v_F2 = pairF2 (kF2 (natCode tag_sb2)) midF2

------------------------------------------------------------------------
-- Closure equation.  ap2 Df_v_F2 X Y =Deriv= Df_v X Y .

Df_v_F2_unfold :
  (X Y : Term) -> Deriv (eqF (ap2 Df_v_F2 X Y) (Df_v X Y))
Df_v_F2_unfold X Y =
  let
    -- Targets at each layer.
    numX = ap1 num X
    numY = ap1 num Y

    inner_left : Term
    inner_left = ap2 Pair (natCode zero) numX

    inner_right : Term
    inner_right = ap2 Pair (natCode (suc zero)) numY

    spec_target : Term
    spec_target = ap2 Pair inner_left inner_right

    mid_target : Term
    mid_target = ap2 Pair spec_target packAx3_O

    df_v_target : Term
    df_v_target = ap2 Pair (natCode tag_sb2) mid_target

    -- inner_left : pairF2 (kF2 0) numF2_first
    e_inner_left :
      Deriv (eqF (ap2 (pairF2 (kF2 (natCode zero)) numF2_first) X Y)
                  inner_left)
    e_inner_left =
      ruleTrans (pairF2_eq (kF2 (natCode zero)) numF2_first X Y)
        (ruleTrans
          (congL Pair (ap2 numF2_first X Y)
            (kF2_eq_closed (natCode zero) (closed_natCode zero) X Y))
          (congR Pair (natCode zero) (numF2_first_eq X Y)))

    -- inner_right : pairF2 (kF2 1) numF2_second
    e_inner_right :
      Deriv (eqF (ap2 (pairF2 (kF2 (natCode (suc zero))) numF2_second) X Y)
                  inner_right)
    e_inner_right =
      ruleTrans (pairF2_eq (kF2 (natCode (suc zero))) numF2_second X Y)
        (ruleTrans
          (congL Pair (ap2 numF2_second X Y)
            (kF2_eq_closed (natCode (suc zero)) (closed_natCode (suc zero)) X Y))
          (congR Pair (natCode (suc zero)) (numF2_second_eq X Y)))

    -- innerSpec evaluation : pair of inner_left, inner_right.
    e_innerSpec :
      Deriv (eqF (ap2 innerSpec X Y) spec_target)
    e_innerSpec =
      ruleTrans (pairF2_eq (pairF2 (kF2 (natCode zero)) numF2_first)
                             (pairF2 (kF2 (natCode (suc zero))) numF2_second) X Y)
        (ruleTrans
          (congL Pair (ap2 (pairF2 (kF2 (natCode (suc zero))) numF2_second) X Y) e_inner_left)
          (congR Pair inner_left e_inner_right))

    -- packAx3_O constant.
    e_pack :
      Deriv (eqF (ap2 (kF2 packAx3_O) X Y) packAx3_O)
    e_pack = kF2_eq_closed packAx3_O closed_packAx3_O X Y

    -- midF2 evaluation.
    e_mid :
      Deriv (eqF (ap2 midF2 X Y) mid_target)
    e_mid =
      ruleTrans (pairF2_eq innerSpec (kF2 packAx3_O) X Y)
        (ruleTrans
          (congL Pair (ap2 (kF2 packAx3_O) X Y) e_innerSpec)
          (congR Pair spec_target e_pack))

    -- Top : pairF2 (kF2 tag_sb2) midF2.
    e_tag :
      Deriv (eqF (ap2 (kF2 (natCode tag_sb2)) X Y) (natCode tag_sb2))
    e_tag = kF2_eq_closed (natCode tag_sb2) (closed_natCode tag_sb2) X Y

    e_top :
      Deriv (eqF (ap2 Df_v_F2 X Y) df_v_target)
    e_top =
      ruleTrans (pairF2_eq (kF2 (natCode tag_sb2)) midF2 X Y)
        (ruleTrans
          (congL Pair (ap2 midF2 X Y) e_tag)
          (congR Pair (natCode tag_sb2) e_mid))

    -- df_v_target is definitionally Df_v X Y (see PartV.Df_v).

  in e_top

------------------------------------------------------------------------
-- thm12_v lifted to the Fun2 representation.

thm12_v_F2 :
  (X Y : Term) ->
  Deriv (eqF (ap1 thmT (ap2 Df_v_F2 X Y)) (codeFTeq2 v X Y))
thm12_v_F2 X Y =
  let e_unfold : Deriv (eqF (ap1 thmT (ap2 Df_v_F2 X Y)) (ap1 thmT (Df_v X Y)))
      e_unfold = cong1 thmT (Df_v_F2_unfold X Y)
  in ruleTrans e_unfold (thm12_v X Y)
