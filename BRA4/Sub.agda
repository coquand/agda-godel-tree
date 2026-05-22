{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Sub -- the top-level Guard substitution functor  sub : Fun2 .
--
-- Definition (Guard 1963 , Exercise 24 [8] / guard15.pdf p.15) :
--
--    sub z cP =Deriv=  sbf (Pair (natCode 0) (num z)) cP
--
-- = "substitute  num z  for var 0 in the encoded formula  cP " .
--
-- This is THE function Guard uses throughout the diagonal lemma and
-- Theorem 14 .  The encoded form of "sub(i, i)" in Guard 's notation is
--   ap2 (codeFun2 sub) (Pair (num i) (num i))   in BRA4 ' s Pair encoding.
--
-- The BRA4 definition uses BRA3.Fan combinators :
--
--    specMaker z cP   =  Pair (natCode 0) (num z)               -- a Fun2
--    sub z cP         =  sbf (specMaker z cP) cP                 -- Fan
--
-- Closure proof  sub_eq  by  Fan_eq + ax_v + ax_o + Lift1_eq + cong .

module BRA4.Sub where

open import BRA4.Base
open import BRA4.Num               using ( num )
open import BRA4.SbF               using ( sbf )
open import BRA3.Fan               using ( Fan ; Fan_eq ; Lift1 ; Lift1_eq )

------------------------------------------------------------------------
-- Build the substitution-spec : a  Fun2  whose closure at  (z, cP)  is
--  Pair (natCode 0) (num z) , independent of  cP .
--
--   specMaker  =  Fan (Lift1 o) (Lift1 num) Pair .
--
-- Closure :  ap2 specMaker z cP  =Deriv=  Pair (ap1 o z) (ap1 num z)
--                                =Deriv=  Pair (natCode 0) (ap1 num z)
-- via ax_o on the first slot ( natCode 0 = O = ap1 o z ).

specMaker : Fun2
specMaker = Fan (Lift1 o) (Lift1 num) Pair

specMaker_eq :
  (z cP : Term) ->
  Deriv (eqF (ap2 specMaker z cP)
              (ap2 Pair (natCode zero) (ap1 num z)))
specMaker_eq z cP =
  let
    -- (1) Fan_eq : specMaker z cP  =  Pair (Lift1 o $ z, cP) (Lift1 num $ z, cP).
    fanStep :
      Deriv (eqF (ap2 specMaker z cP)
                  (ap2 Pair (ap2 (Lift1 o) z cP) (ap2 (Lift1 num) z cP)))
    fanStep = Fan_eq (Lift1 o) (Lift1 num) Pair z cP

    -- (2) Lift1_eq o z cP : Lift1 o $ z, cP = ap1 o z .
    lift1_o : Deriv (eqF (ap2 (Lift1 o) z cP) (ap1 o z))
    lift1_o = Lift1_eq o z cP

    -- (3) ax_o z : ap1 o z = O .  And  O = natCode 0  definitionally.
    o_eq_zero : Deriv (eqF (ap1 o z) (natCode zero))
    o_eq_zero = ax_o z

    -- (4) Combine (2) , (3) :  Lift1 o $ z, cP  =  natCode 0 .
    leftSlot_eq : Deriv (eqF (ap2 (Lift1 o) z cP) (natCode zero))
    leftSlot_eq = ruleTrans lift1_o o_eq_zero

    -- (5) Lift1_eq num z cP : Lift1 num $ z, cP = ap1 num z .
    rightSlot_eq : Deriv (eqF (ap2 (Lift1 num) z cP) (ap1 num z))
    rightSlot_eq = Lift1_eq num z cP

    -- (6) Pair-cong : lift (4) , (5) inside  ap2 Pair _ _ .
    pair_left :
      Deriv (eqF (ap2 Pair (ap2 (Lift1 o) z cP) (ap2 (Lift1 num) z cP))
                  (ap2 Pair (natCode zero) (ap2 (Lift1 num) z cP)))
    pair_left = congL Pair (ap2 (Lift1 num) z cP) leftSlot_eq

    pair_right :
      Deriv (eqF (ap2 Pair (natCode zero) (ap2 (Lift1 num) z cP))
                  (ap2 Pair (natCode zero) (ap1 num z)))
    pair_right = congR Pair (natCode zero) rightSlot_eq

  in ruleTrans fanStep (ruleTrans pair_left pair_right)

------------------------------------------------------------------------
-- The top-level Guard substitution functor :
--
--    sub  =  Fan specMaker v sbf .
--
--    ap2 sub z cP
--      =Deriv=  ap2 sbf (ap2 specMaker z cP) (ap2 v z cP)         [Fan_eq]
--      =Deriv=  ap2 sbf (Pair (natCode 0) (num z)) cP             [specMaker_eq + ax_v]

sub : Fun2
sub = Fan specMaker v sbf

sub_eq :
  (z cP : Term) ->
  Deriv (eqF (ap2 sub z cP)
              (ap2 sbf (ap2 Pair (natCode zero) (ap1 num z)) cP))
sub_eq z cP =
  let
    -- (1) Fan_eq : sub z cP = sbf (specMaker z cP) (v z cP) .
    fanStep :
      Deriv (eqF (ap2 sub z cP)
                  (ap2 sbf (ap2 specMaker z cP) (ap2 v z cP)))
    fanStep = Fan_eq specMaker v sbf z cP

    -- (2) specMaker_eq : specMaker z cP = Pair (natCode 0) (num z) .
    spec_eq :
      Deriv (eqF (ap2 specMaker z cP)
                  (ap2 Pair (natCode zero) (ap1 num z)))
    spec_eq = specMaker_eq z cP

    -- (3) ax_v : v z cP = cP .
    v_eq : Deriv (eqF (ap2 v z cP) cP)
    v_eq = ax_v z cP

    -- (4) Lift  (2) inside  ap2 sbf _ _ : congL on the first slot.
    sbf_left :
      Deriv (eqF (ap2 sbf (ap2 specMaker z cP) (ap2 v z cP))
                  (ap2 sbf (ap2 Pair (natCode zero) (ap1 num z))
                            (ap2 v z cP)))
    sbf_left = congL sbf (ap2 v z cP) spec_eq

    -- (5) Lift  (3) inside  ap2 sbf _ _ : congR on the second slot.
    sbf_right :
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (ap1 num z))
                          (ap2 v z cP))
                  (ap2 sbf (ap2 Pair (natCode zero) (ap1 num z)) cP))
    sbf_right = congR sbf (ap2 Pair (natCode zero) (ap1 num z)) v_eq

  in ruleTrans fanStep (ruleTrans sbf_left sbf_right)
