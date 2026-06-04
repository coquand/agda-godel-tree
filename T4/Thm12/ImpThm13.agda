{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Thm12.ImpThm13 -- the imp-lifted form of  T4.Thm12.Thm13.thm13_binary
-- ( clos Step 4 :  "(Kr x0 = 0) => thmT(D Kr x0) = code (Kr(num x0) = 0)" ).
--
-- thm13_binary uses its run-fact hypothesis  h : Deriv (eqF (ap2 g x1 x2) y)
-- in EXACTLY ONE place :  num_bridge = cong1 num h .   Everything else is
-- unconditional ( the  thm12  instance + Pair-congruence bridges ).   So the
-- whole proof imp-lifts mechanically :  cong1 -> impCong1 , congR -> impCongR ,
-- ruleTrans -> impEqTrans , unconditional steps wrapped by  impLift .
--
--   imp_thm13_binary g x1 x2 y P
--     (imp_h : Deriv (imp P (eqF (ap2 g x1 x2) y)))
--   : Deriv (imp P (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 g)) x1 x2))
--                       (codeFXeqY2 g x1 x2 y)))
--
-- This is the Carneiro witness-level imp-lift ( NOT a forbidden
-- Deriv A -> Deriv B  =>  Deriv (imp A B)  primitive ) :  the hypothesis is
-- threaded through the reconstructed proof, never lifted post-hoc.

module T4.Thm12.ImpThm13 where

open import T4.Base
open import T4.Tags
open import T4.Code          using ( codeFun1 ; codeFun2 )
open import T4.Num            using ( num )
open import T4.ThmT          using ( thmT )
open import T4.Thm12.CodeFTeq using ( codeFTeq1 ; codeFTeq2 )
open import T4.Thm12.Thm13   using ( codeFXeqY1 ; codeFXeqY2 )
open import T4.Thm12.All     using ( thm12 ; thm12_Fun2 ; fst ; snd )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impCong1 ; impCongR ; impEqTrans )

------------------------------------------------------------------------
-- imp-lifted  thm13_binary .

-- imp-lifted  thm13_singulary  ( the Fun1 form clos Step 4 applies to  Kr ).

imp_thm13_singulary :
  (f : Fun1) (x y : Term) (P : Formula) ->
  Deriv (imp P (eqF (ap1 f x) y)) ->
  Deriv (imp P (eqF (ap1 thmT (ap1 (fst (thm12 f)) x))
                    (codeFXeqY1 f x y)))
imp_thm13_singulary f x y P imp_h =
  let
    p_f = thm12 f
    Df = fst p_f
    ih = snd p_f

    e_thm12 : Deriv (eqF (ap1 thmT (ap1 Df x)) (codeFTeq1 f x))
    e_thm12 = ih x

    num_bridge : Deriv (imp P (eqF (ap1 num (ap1 f x)) (ap1 num y)))
    num_bridge = impCong1 num (ap1 f x) y imp_h

    codeApSlot : Term
    codeApSlot =
      ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) (ap1 num x))

    inner_pair :
      Deriv (imp P (eqF (ap2 Pair codeApSlot (ap1 num (ap1 f x)))
                        (ap2 Pair codeApSlot (ap1 num y))))
    inner_pair =
      impCongR Pair (ap1 num (ap1 f x)) (ap1 num y) codeApSlot num_bridge

    outer_bridge :
      Deriv (imp P (eqF (codeFTeq1 f x) (codeFXeqY1 f x y)))
    outer_bridge =
      impCongR Pair (ap2 Pair codeApSlot (ap1 num (ap1 f x)))
                    (ap2 Pair codeApSlot (ap1 num y))
                    (natCode tag_eq) inner_pair
  in impEqTrans (ap1 thmT (ap1 Df x)) (codeFTeq1 f x) (codeFXeqY1 f x y)
       (impLift {P} e_thm12)
       outer_bridge

imp_thm13_binary :
  (g : Fun2) (x1 x2 y : Term) (P : Formula) ->
  Deriv (imp P (eqF (ap2 g x1 x2) y)) ->
  Deriv (imp P (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 g)) x1 x2))
                    (codeFXeqY2 g x1 x2 y)))
imp_thm13_binary g x1 x2 y P imp_h =
  let
    p_g = thm12_Fun2 g
    Df = fst p_g
    ih = snd p_g

    -- thm12 instance at x1 x2 ( UNCONDITIONAL, lifted by impLift ).
    e_thm12 : Deriv (eqF (ap1 thmT (ap2 Df x1 x2)) (codeFTeq2 g x1 x2))
    e_thm12 = ih x1 x2

    -- THE ONLY hypothesis use :  num (g x1 x2) -> num y  under P .
    num_bridge : Deriv (imp P (eqF (ap1 num (ap2 g x1 x2)) (ap1 num y)))
    num_bridge = impCong1 num (ap2 g x1 x2) y imp_h

    codeApSlot : Term
    codeApSlot =
      ap2 Pair (natCode tag_ap2)
        (ap2 Pair (codeFun2 g) (ap2 Pair (ap1 num x1) (ap1 num x2)))

    inner_pair :
      Deriv (imp P (eqF (ap2 Pair codeApSlot (ap1 num (ap2 g x1 x2)))
                        (ap2 Pair codeApSlot (ap1 num y))))
    inner_pair =
      impCongR Pair (ap1 num (ap2 g x1 x2)) (ap1 num y) codeApSlot num_bridge

    outer_bridge :
      Deriv (imp P (eqF (codeFTeq2 g x1 x2) (codeFXeqY2 g x1 x2 y)))
    outer_bridge =
      impCongR Pair (ap2 Pair codeApSlot (ap1 num (ap2 g x1 x2)))
                    (ap2 Pair codeApSlot (ap1 num y))
                    (natCode tag_eq) inner_pair
  in impEqTrans (ap1 thmT (ap2 Df x1 x2)) (codeFTeq2 g x1 x2)
       (codeFXeqY2 g x1 x2 y)
       (impLift {P} e_thm12)
       outer_bridge
