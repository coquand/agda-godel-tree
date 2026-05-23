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

-- F2-level single  tag_sb  layer builder (mirrors PartRStep.sbLayerF1).
private
  sbLayerF2 : Nat -> Fun2 -> Fun2 -> Fun2
  sbLayerF2 k vF inF =
    pairF2 (kF2 (natCode tag_sb)) (pairF2 (pairF2 (kF2 (natCode k)) vF) inF)

  sbLayerF2_eq :
    (k : Nat) (vF inF : Fun2) (vT innerT : Term) (X Y : Term) ->
    Deriv (eqF (ap2 vF X Y) vT) ->
    Deriv (eqF (ap2 inF X Y) innerT) ->
    Deriv (eqF (ap2 (sbLayerF2 k vF inF) X Y)
                (ap2 Pair (natCode tag_sb)
                  (ap2 Pair (ap2 Pair (natCode k) vT) innerT)))
  sbLayerF2_eq k vF inF vT innerT X Y ev einner =
    let e_specPair :
          Deriv (eqF (ap2 (pairF2 (kF2 (natCode k)) vF) X Y)
                      (ap2 Pair (natCode k) vT))
        e_specPair =
          ruleTrans (pairF2_eq (kF2 (natCode k)) vF X Y)
            (ruleTrans
              (congL Pair (ap2 vF X Y)
                (kF2_eq_closed (natCode k) (closed_natCode k) X Y))
              (congR Pair (natCode k) ev))
        e_mid :
          Deriv (eqF (ap2 (pairF2 (pairF2 (kF2 (natCode k)) vF) inF) X Y)
                      (ap2 Pair (ap2 Pair (natCode k) vT) innerT))
        e_mid =
          ruleTrans (pairF2_eq (pairF2 (kF2 (natCode k)) vF) inF X Y)
            (ruleTrans (congL Pair (ap2 inF X Y) e_specPair)
                       (congR Pair (ap2 Pair (natCode k) vT) einner))
    in ruleTrans
         (pairF2_eq (kF2 (natCode tag_sb)) (pairF2 (pairF2 (kF2 (natCode k)) vF) inF) X Y)
         (ruleTrans
           (congL Pair (ap2 (pairF2 (pairF2 (kF2 (natCode k)) vF) inF) X Y)
                       (kF2_eq_closed (natCode tag_sb) (closed_natCode tag_sb) X Y))
           (congR Pair (natCode tag_sb) e_mid))

Df_v_F2 : Fun2
Df_v_F2 =
  sbLayerF2 zero numF2_first
    (sbLayerF2 (suc zero) numF2_second (kF2 packAx3_O))

------------------------------------------------------------------------
-- Closure equation.  ap2 Df_v_F2 X Y =Deriv= Df_v X Y .

Df_v_F2_unfold :
  (X Y : Term) -> Deriv (eqF (ap2 Df_v_F2 X Y) (Df_v X Y))
Df_v_F2_unfold X Y =
  let i1 : Fun2
      i1 = sbLayerF2 (suc zero) numF2_second (kF2 packAx3_O)

      e1 = sbLayerF2_eq (suc zero) numF2_second (kF2 packAx3_O)
             (ap1 num Y) packAx3_O X Y
             (numF2_second_eq X Y)
             (kF2_eq_closed packAx3_O closed_packAx3_O X Y)
      e0 = sbLayerF2_eq zero numF2_first i1
             (ap1 num X) _ X Y
             (numF2_first_eq X Y) e1
  in e0

------------------------------------------------------------------------
-- thm12_v lifted to the Fun2 representation.

thm12_v_F2 :
  (X Y : Term) ->
  Deriv (eqF (ap1 thmT (ap2 Df_v_F2 X Y)) (codeFTeq2 v X Y))
thm12_v_F2 X Y =
  let e_unfold : Deriv (eqF (ap1 thmT (ap2 Df_v_F2 X Y)) (ap1 thmT (Df_v X Y)))
      e_unfold = cong1 thmT (Df_v_F2_unfold X Y)
  in ruleTrans e_unfold (thm12_v X Y)
