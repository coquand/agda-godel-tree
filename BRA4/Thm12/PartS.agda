{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartS -- Theorem 12, case  f = s  (successor functor).
--
-- Goal :
--   thm12_s : (X : Term) ->
--     Deriv (eqF (ap1 thmT (Df_s_meta X)) (codeFTeq1 s X))
--
-- Construction.  Df_s_meta X = Df_refl_meta (num (s X)).
--   ap1 thmT (Df_s_meta X)  =Deriv=  Pair tag_eq (Pair (num(s X)) (num(s X)))
--                                                                    [encoded_refl Y at Y = num(s X)]
--
-- Bridge LHS slot via  num_at_S X  :
--   num (s X)  =Deriv=  Pair tag_ap1 (Pair (natCode tag_s) (num X))
--               =       codeS_at (num X)   (the asymmetric encoding of  s (num X))
--
-- So  Pair tag_eq (Pair (num(s X)) (num(s X)))  =Deriv=
--      Pair tag_eq (Pair (codeS_at (num X)) (num(s X)))   =  codeFTeq1 s X .

module BRA4.Thm12.PartS where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code             using ( codeFun1 )
open import BRA4.Num              using ( num ; num_at_S )
open import BRA4.ThmT             using ( thmT )
open import BRA4.Thm12.CodeFTeq   using ( codeFTeq1 )
open import BRA4.Thm12.EncodedRefl
  using ( Df_refl_meta ; encoded_refl ; codedReflTerm )

------------------------------------------------------------------------
-- Df_s_meta : Term -> Term .  ( ap1-style meta version, since Df_refl
-- is a meta-function over Terms.)

Df_s_meta : Term -> Term
Df_s_meta X = Df_refl_meta (ap1 num (ap1 s X))

------------------------------------------------------------------------
-- The s case.

thm12_s :
  (X : Term) ->
  Deriv (eqF (ap1 thmT (Df_s_meta X)) (codeFTeq1 s X))
thm12_s X =
  let
    Y : Term
    Y = ap1 num (ap1 s X)

    -- (1)  thmT (Df_s_meta X)  =Deriv=  codedReflTerm Y  =  Pair tag_eq (Pair Y Y) .
    e_refl :
      Deriv (eqF (ap1 thmT (Df_s_meta X)) (codedReflTerm Y))
    e_refl = encoded_refl Y

    -- (2)  Bridge LHS slot  Y  ->  codeS_at (num X)  =  Pair tag_ap1 (Pair tag_s (num X)) .
    codeS_at_numX : Term
    codeS_at_numX =
      ap2 Pair (natCode tag_ap1)
        (ap2 Pair (codeFun1 s) (ap1 num X))

    succ_eq : Deriv (eqF Y codeS_at_numX)
    succ_eq = num_at_S X

    -- (3)  Lift through inner Pair (Y Y -> codeS_at_numX Y) :
    inner_eq :
      Deriv (eqF (ap2 Pair Y Y) (ap2 Pair codeS_at_numX Y))
    inner_eq = congL Pair Y succ_eq

    -- (4)  Lift through outer Pair (tag_eq, ...).
    e_bridge :
      Deriv (eqF (codedReflTerm Y) (codeFTeq1 s X))
    e_bridge = congR Pair (natCode tag_eq) inner_eq

  in ruleTrans e_refl e_bridge
