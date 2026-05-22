{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.Thm13 -- Guard 1963 Theorem 13 (corollary of Theorem 12).
--
-- Given Deriv (eqF (ap1 f x) y) , produce the encoded equation
--   "f(num x) = num y"  via thmT . The Df returned by thm12 already
-- decodes to  "f(num x) = num (f x)" ; thm13 just bridges the RHS slot
--  num (f x) -> num y  using the supplied derivation.
--
-- NOTE: guard15.pdf p.16 states the conclusion as " f x_ = y " (raw y) ;
-- this is a paper typo .  The proof one line below uses  num y  (= y_) ,
-- which is what we code here.

module BRA4.Thm12.Thm13 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.Num               using ( num )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 ; codeFTeq2 )
open import BRA4.Thm12.All
  using ( thm12 ; thm12_Fun2 ; Sigma ; fst ; snd )

------------------------------------------------------------------------
-- The encoded equation targets.
--
--   codeFXeqY1 f x y  =  Pair tag_eq (Pair (Pair tag_ap1 (Pair (codeFun1 f) (num x)))
--                                              (num y))
--   codeFXeqY2 g x1 x2 y  similarly with codeFun2 g and (Pair (num x1) (num x2)) .

codeFXeqY1 : Fun1 -> Term -> Term -> Term
codeFXeqY1 f x y =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 f) (ap1 num x)))
              (ap1 num y))

codeFXeqY2 : Fun2 -> Term -> Term -> Term -> Term
codeFXeqY2 g x1 x2 y =
  ap2 Pair (natCode tag_eq)
    (ap2 Pair (ap2 Pair (natCode tag_ap2)
                        (ap2 Pair (codeFun2 g)
                          (ap2 Pair (ap1 num x1) (ap1 num x2))))
              (ap1 num y))

------------------------------------------------------------------------
-- thm13 (singulary).

thm13_singulary :
  (f : Fun1) (x y : Term) ->
  Deriv (eqF (ap1 f x) y) ->
  Deriv (eqF (ap1 thmT (ap1 (fst (thm12 f)) x))
              (codeFXeqY1 f x y))
thm13_singulary f x y h_fx_eq_y =
  let
    p_f = thm12 f
    Df = fst p_f
    ih = snd p_f

    -- thm12 instance at x.
    e_thm12 : Deriv (eqF (ap1 thmT (ap1 Df x)) (codeFTeq1 f x))
    e_thm12 = ih x

    -- num (f x) -> num y.
    num_bridge : Deriv (eqF (ap1 num (ap1 f x)) (ap1 num y))
    num_bridge = cong1 num h_fx_eq_y

    -- codeFTeq1 f x  =  Pair tag_eq (Pair codeApSlot (num (f x))) .
    codeApSlot : Term
    codeApSlot =
      ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) (ap1 num x))

    inner_pair :
      Deriv (eqF (ap2 Pair codeApSlot (ap1 num (ap1 f x)))
                  (ap2 Pair codeApSlot (ap1 num y)))
    inner_pair = congR Pair codeApSlot num_bridge

    outer_bridge :
      Deriv (eqF (codeFTeq1 f x) (codeFXeqY1 f x y))
    outer_bridge = congR Pair (natCode tag_eq) inner_pair

  in ruleTrans e_thm12 outer_bridge

------------------------------------------------------------------------
-- thm13 (binary).

thm13_binary :
  (g : Fun2) (x1 x2 y : Term) ->
  Deriv (eqF (ap2 g x1 x2) y) ->
  Deriv (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 g)) x1 x2))
              (codeFXeqY2 g x1 x2 y))
thm13_binary g x1 x2 y h_gx_eq_y =
  let
    p_g = thm12_Fun2 g
    Df = fst p_g
    ih = snd p_g

    e_thm12 : Deriv (eqF (ap1 thmT (ap2 Df x1 x2)) (codeFTeq2 g x1 x2))
    e_thm12 = ih x1 x2

    num_bridge : Deriv (eqF (ap1 num (ap2 g x1 x2)) (ap1 num y))
    num_bridge = cong1 num h_gx_eq_y

    codeApSlot : Term
    codeApSlot =
      ap2 Pair (natCode tag_ap2)
        (ap2 Pair (codeFun2 g) (ap2 Pair (ap1 num x1) (ap1 num x2)))

    inner_pair :
      Deriv (eqF (ap2 Pair codeApSlot (ap1 num (ap2 g x1 x2)))
                  (ap2 Pair codeApSlot (ap1 num y)))
    inner_pair = congR Pair codeApSlot num_bridge

    outer_bridge :
      Deriv (eqF (codeFTeq2 g x1 x2) (codeFXeqY2 g x1 x2 y))
    outer_bridge = congR Pair (natCode tag_eq) inner_pair

  in ruleTrans e_thm12 outer_bridge
