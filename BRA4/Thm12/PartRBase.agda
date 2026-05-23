{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartRBase -- Theorem 12, R-case BASE  (Y = O).
--
-- Goal (parametric on IH_g for the inner Fun1 g ; universal in X : Term ; no Closed) :
--
--   thm12_R_at_O :
--     (g : Fun1) (h1 h2 : Fun2)
--     (Df_g_inst : Term -> Term)
--     (ih_g : (X : Term) ->
--                Deriv (eqF (ap1 thmT (Df_g_inst X)) (codeFTeq1 g X)))
--     (X : Term) ->
--     Deriv (eqF (ap1 thmT (Df_R_at_O g h1 h2 Df_g_inst X))
--                 (codeFTeq2 (R g h1 h2) X O))
--
-- Construction.  Build the encoded chain (left-aligned):
--
--   L1  =  encoded "R g h1 h2 (num X, O)"
--       =  Pair tag_ap2 (Pair (codeFun2 (R g h1 h2)) (Pair (num X) O))
--   L2  =  encoded "g (num X)"
--       =  Pair tag_ap1 (Pair (codeFun1 g) (num X))   ( = encH_at g X )
--   L3  =  num (g X)
--
-- Chain:
--   enc(L1 = L2)   via encodedAxRBase g h1 h2 X .
--   enc(L2 = L3)   via IH_g X   ( codeFTeq1 g X = encEq L2 L3 ).
-- Compose via encoded_eqTrans to obtain enc(L1 = L3).
--
-- Final bridges (Term-level, lifted through Pair structure) :
--   L1  ->  L1' = Pair tag_ap2 (Pair (codeFun2 (R g h1 h2)) (Pair (num X) (num O)))
--           via cong on inner-right slot  O -> num O  (ruleSym num_at_O).
--   L3  ->  num ((R g h1 h2) X O)
--           via cong1 num (ruleSym (ax_R_base g h1 h2 X)).
--
-- After these bridges  encEq L1 L3  =Deriv=  codeFTeq2 (R g h1 h2) X O .

module BRA4.Thm12.PartRBase where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code            using ( codeFun1 ; codeFun2 )
open import BRA4.Num             using ( num ; num_at_O )
open import BRA4.SbStep
  using ( InertU ; NumCode ; ncO ; ncNum ; ncAp1 ; ncAp2 ; sbt_inert_NumCode )
open import BRA4.ThmT            using ( thmT )
open import BRA4.Thm12.CodeFTeq  using ( codeFTeq1 ; codeFTeq2 )
open import BRA4.Thm12.EncodedAxRBase
  using ( Df_axRBase ; encodedAxRBase ; encodedAxRBase_Term )
open import BRA4.Thm12.EncodedEqChain
  using ( encEq ; Df_eqTrans ; encoded_eqTrans )

------------------------------------------------------------------------
-- Term-level sub-terms used throughout.

private
  L1_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term
  L1_at g h1 h2 X =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) O))

  L2_at : Fun1 -> Term -> Term
  L2_at g X =
    ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 g) (ap1 num X))

  L3_at : Fun1 -> Term -> Term
  L3_at g X = ap1 num (ap1 g X)

  -- The bridged LHS slot of  codeFTeq2 (R g h1 h2) X O .
  L1'_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term
  L1'_at g h1 h2 X =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) (ap1 num O)))

------------------------------------------------------------------------
-- Df_R_at_O : the encoded chain for the base case.

Df_R_at_O :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_inst : Term -> Term)
  (X : Term) -> Term
Df_R_at_O g h1 h2 Df_g_inst X =
  Df_eqTrans (ap1 (Df_axRBase g h1 h2) X) (Df_g_inst X)
             (L1_at g h1 h2 X) (L2_at g X) (L3_at g X)

------------------------------------------------------------------------
-- Main theorem.

thm12_R_at_O :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_inst : Term -> Term)
  (ih_g : (X : Term) ->
             Deriv (eqF (ap1 thmT (Df_g_inst X)) (codeFTeq1 g X)))
  (X : Term) ->
  Deriv (eqF (ap1 thmT (Df_R_at_O g h1 h2 Df_g_inst X))
              (codeFTeq2 (R g h1 h2) X O))
thm12_R_at_O g h1 h2 Df_g_inst ih_g X =
  let
    L1 : Term
    L1 = L1_at g h1 h2 X

    L2 : Term
    L2 = L2_at g X

    L3 : Term
    L3 = L3_at g X

    L1' : Term
    L1' = L1'_at g h1 h2 X

    -- Step A : enc(L1 = L2)  via encodedAxRBase .
    e_step_A : Deriv (eqF (ap1 thmT (ap1 (Df_axRBase g h1 h2) X)) (encEq L1 L2))
    e_step_A = encodedAxRBase g h1 h2 X

    -- Step B : enc(L2 = L3)  via IH_g X .
    --   codeFTeq1 g X  =Deriv=  encEq L2 L3   (definitionally).
    e_step_B : Deriv (eqF (ap1 thmT (Df_g_inst X)) (encEq L2 L3))
    e_step_B = ih_g X

    -- Step C : enc(L1 = L3) via encoded_eqTrans .  All L-positions num-based.
    iL1 : InertU L1
    iL1 = sbt_inert_NumCode L1
            (ncAp2 (R g h1 h2) (ap1 num X) O (ncNum X) ncO)

    iL2 : InertU L2
    iL2 = sbt_inert_NumCode L2 (ncAp1 g (ap1 num X) (ncNum X))

    iL3 : InertU L3
    iL3 = sbt_inert_NumCode L3 (ncNum (ap1 g X))

    e_step_C : Deriv (eqF (ap1 thmT (Df_R_at_O g h1 h2 Df_g_inst X)) (encEq L1 L3))
    e_step_C = encoded_eqTrans (ap1 (Df_axRBase g h1 h2) X) (Df_g_inst X)
                  L1 L2 L3 iL1 iL2 iL3 e_step_A e_step_B

    ---------------------------------------------------------------
    -- Bridges.
    ---------------------------------------------------------------

    -- LHS slot bridge : L1 -> L1' via cong on inner-right slot O -> num O.
    --   L1  = pi tag_ap2 (pi (codeFun2 (R g h1 h2)) (pi (num X) O))
    --   L1' = pi tag_ap2 (pi (codeFun2 (R g h1 h2)) (pi (num X) (num O)))
    --
    -- num_at_O : eqF (ap1 num O) O .   We need  eqF O (ap1 num O)  here.
    O_to_numO :
      Deriv (eqF O (ap1 num O))
    O_to_numO = ruleSym num_at_O

    inner_pair_bridge :
      Deriv (eqF (ap2 Pair (ap1 num X) O)
                  (ap2 Pair (ap1 num X) (ap1 num O)))
    inner_pair_bridge = congR Pair (ap1 num X) O_to_numO

    inner2_pair_bridge :
      Deriv (eqF (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) O))
                  (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) (ap1 num O))))
    inner2_pair_bridge = congR Pair (codeFun2 (R g h1 h2)) inner_pair_bridge

    LHS_slot_bridge : Deriv (eqF L1 L1')
    LHS_slot_bridge = congR Pair (natCode tag_ap2) inner2_pair_bridge

    -- RHS slot bridge : L3 = num (g X) -> num (R g h1 h2 X O).
    axRBase_eq :
      Deriv (eqF (ap2 (R g h1 h2) X O) (ap1 g X))
    axRBase_eq = ax_R_base g h1 h2 X

    RHS_slot_bridge :
      Deriv (eqF L3 (ap1 num (ap2 (R g h1 h2) X O)))
    RHS_slot_bridge = cong1 num (ruleSym axRBase_eq)

    -- Lift through inner Pair structure.
    pair_inner :
      Deriv (eqF (ap2 Pair L1 L3)
                  (ap2 Pair L1' (ap1 num (ap2 (R g h1 h2) X O))))
    pair_inner =
      ruleTrans (congL Pair L3 LHS_slot_bridge)
                (congR Pair L1' RHS_slot_bridge)

    -- Lift through outer  Pair tag_eq  .
    outer_bridge :
      Deriv (eqF (encEq L1 L3)
                  (codeFTeq2 (R g h1 h2) X O))
    outer_bridge = congR Pair (natCode tag_eq) pair_inner

    -- codeFTeq2 (R g h1 h2) X O  is definitionally :
    --   Pair tag_eq (Pair (Pair tag_ap2 (Pair (codeFun2 (R g h1 h2))
    --                                            (Pair (num X) (num O))))
    --                      (num (R g h1 h2 X O)))
    --   = Pair tag_eq (Pair L1' (num (R g h1 h2 X O)))   --  matches.

  in ruleTrans e_step_C outer_bridge
