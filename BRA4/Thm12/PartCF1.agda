{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartCF1 -- Theorem 12, composition case with Df_C_F1 : Fun1.
--
--   Df_C_F1 :
--     (g : Fun2) (h1 h2 : Fun1)
--     (Df_g_F2 : Fun2) (Df_h1_F1 Df_h2_F1 : Fun1) -> Fun1
--
--   ap1 Df_C_F1 X =Deriv= Df_C g h1 h2 (ap2 Df_g_F2) (ap1 Df_h1_F1) (ap1 Df_h2_F1) X
--
--   thm12_C_F1 :
--     ... + IHs over Df_g_F2 / Df_h1_F1 / Df_h2_F1 ... + (X : Term) ->
--     Deriv (eqF (ap1 thmT (ap1 Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1 X))
--                 (codeFTeq1 (C g h1 h2) X))
--
-- Construction.  We build Fun1 wrappers
--   L1_F1 ... L5_F1  for the five Term anchors of the encoded chain ,
--   d_axC_F1 = Df_axC g h1 h2 (already Fun1) ,
--   d_step_B_F1 = mpWrapF1 (Df_axEqCongL_F1 g L1' L2' L3')  Df_h1_F1 ,
--   d_step_C_F1 = mpWrapF1 (Df_axEqCongR_F1 g ...) Df_h2_F1 ,
--   d_step_D_F1 = C Df_g_F2 h1 h2  ( ax_C : ap1 D X = ap2 Df_g_F2 (h1 X) (h2 X) ) .
-- Then chain three Df_eqTrans_F1 (already in PartRStep).

module BRA4.Thm12.PartCF1 where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.Num               using ( num )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 ; codeFTeq2 )
open import BRA4.Thm12.EncodedAxC
  using ( Df_axC )
open import BRA4.Thm12.EncodedAxEqCongL
  using ( Df_axEqCongL )
open import BRA4.Thm12.EncodedAxEqCongR
  using ( Df_axEqCongR )
open import BRA4.Thm12.EncodedEqChain
  using ( Df_eqTrans )
open import BRA4.Thm12.PartC
  using ( Df_C ; thm12_C )
open import BRA4.Thm12.PartRStep
  using ( pairF1 ; pairF1_eq ; natF1 ; natF1_eq
        ; mpWrapF1 ; mpWrapF1_eq
        ; codeFun1_F1 ; codeFun1_F1_eq
        ; codeFun2_F1 ; codeFun2_F1_eq
        ; Df_axEqCongL_F1 ; Df_axEqCongL_F1_eq
        ; Df_axEqCongR_F1 ; Df_axEqCongR_F1_eq
        ; Df_axEqCongL_cong ; Df_axEqCongR_cong
        ; Df_eqTrans_F1 ; Df_eqTrans_F1_eq
        ; Df_eqTrans_T_cong )

------------------------------------------------------------------------
-- Fun1 wrappers for the sub-Terms used in Df_C .

-- encH_at_F1 h : ap1 (encH_at_F1 h) X = Pair tag_ap1 (Pair (codeFun1 h) (num X))
encH_at_F1 : Fun1 -> Fun1
encH_at_F1 h = pairF1 (natF1 tag_ap1) (pairF1 (codeFun1_F1 h) num)

private
  encH_at : Fun1 -> Term -> Term
  encH_at h X = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 h) (ap1 num X))

  encH_at_F1_eq :
    (h : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (encH_at_F1 h) X) (encH_at h X))
  encH_at_F1_eq h X =
    let
      e_inner :
        Deriv (eqF (ap1 (pairF1 (codeFun1_F1 h) num) X)
                    (ap2 Pair (codeFun1 h) (ap1 num X)))
      e_inner =
        ruleTrans (pairF1_eq (codeFun1_F1 h) num X)
          (congL Pair (ap1 num X) (codeFun1_F1_eq h X))
    in ruleTrans (pairF1_eq (natF1 tag_ap1) (pairF1 (codeFun1_F1 h) num) X)
         (ruleTrans
           (congL Pair _ (natF1_eq tag_ap1 X))
           (congR Pair (natCode tag_ap1) e_inner))

-- encG_at_F1 g cA_F1 cB_F1 : Pair tag_ap2 (Pair (codeFun2 g) (Pair (ap1 cA_F1 X) (ap1 cB_F1 X)))
encG_at_F1 : Fun2 -> Fun1 -> Fun1 -> Fun1
encG_at_F1 g cA_F1 cB_F1 =
  pairF1 (natF1 tag_ap2) (pairF1 (codeFun2_F1 g) (pairF1 cA_F1 cB_F1))

private
  encG_at : Fun2 -> Term -> Term -> Term
  encG_at g A B =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair A B))

  encG_at_F1_eq :
    (g : Fun2) (cA_F1 cB_F1 : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (encG_at_F1 g cA_F1 cB_F1) X)
                (encG_at g (ap1 cA_F1 X) (ap1 cB_F1 X)))
  encG_at_F1_eq g cA_F1 cB_F1 X =
    let
      e_AB :
        Deriv (eqF (ap1 (pairF1 cA_F1 cB_F1) X)
                    (ap2 Pair (ap1 cA_F1 X) (ap1 cB_F1 X)))
      e_AB = pairF1_eq cA_F1 cB_F1 X

      e_codeG_AB :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 g) (pairF1 cA_F1 cB_F1)) X)
                    (ap2 Pair (codeFun2 g)
                       (ap2 Pair (ap1 cA_F1 X) (ap1 cB_F1 X))))
      e_codeG_AB =
        ruleTrans (pairF1_eq (codeFun2_F1 g) (pairF1 cA_F1 cB_F1) X)
          (ruleTrans
            (congL Pair (ap1 (pairF1 cA_F1 cB_F1) X) (codeFun2_F1_eq g X))
            (congR Pair (codeFun2 g) e_AB))
    in ruleTrans (pairF1_eq (natF1 tag_ap2) (pairF1 (codeFun2_F1 g) (pairF1 cA_F1 cB_F1)) X)
         (ruleTrans
           (congL Pair _ (natF1_eq tag_ap2 X))
           (congR Pair (natCode tag_ap2) e_codeG_AB))

-- numH_F1 h : ap1 (numH_F1 h) X = ap1 num (ap1 h X)
numH_F1 : Fun1 -> Fun1
numH_F1 h = compose1U num h

private
  numH_F1_eq :
    (h : Fun1) (X : Term) ->
    Deriv (eqF (ap1 (numH_F1 h) X) (ap1 num (ap1 h X)))
  numH_F1_eq h X = axComp num h X

------------------------------------------------------------------------
-- Df_C_F1 construction.

private
  L1_F1_of : Fun2 -> Fun1 -> Fun1 -> Fun1
  L1_F1_of g h1 h2 = encH_at_F1 (C g h1 h2)

  L2_F1_of : Fun2 -> Fun1 -> Fun1 -> Fun1
  L2_F1_of g h1 h2 = encG_at_F1 g (encH_at_F1 h1) (encH_at_F1 h2)

  L3_F1_of : Fun2 -> Fun1 -> Fun1 -> Fun1
  L3_F1_of g h1 h2 = encG_at_F1 g (numH_F1 h1) (encH_at_F1 h2)

  L4_F1_of : Fun2 -> Fun1 -> Fun1 -> Fun1
  L4_F1_of g h1 h2 = encG_at_F1 g (numH_F1 h1) (numH_F1 h2)

  L5_F1_of : Fun2 -> Fun1 -> Fun1 -> Fun1
  L5_F1_of g h1 h2 = compose1U num (C g h1 h2)

  d_step_B_F1_of :
    (g : Fun2) (h1 h2 : Fun1) (Df_h1_F1 : Fun1) -> Fun1
  d_step_B_F1_of g h1 h2 Df_h1_F1 =
    mpWrapF1
      (Df_axEqCongL_F1 g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2))
      Df_h1_F1

  d_step_C_F1_of :
    (g : Fun2) (h1 h2 : Fun1) (Df_h2_F1 : Fun1) -> Fun1
  d_step_C_F1_of g h1 h2 Df_h2_F1 =
    mpWrapF1
      (Df_axEqCongR_F1 g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1))
      Df_h2_F1

  d_step_D_F1_of :
    (g : Fun2) (h1 h2 : Fun1) (Df_g_F2 : Fun2) -> Fun1
  d_step_D_F1_of g h1 h2 Df_g_F2 = C Df_g_F2 h1 h2

Df_C_F1 :
  (g : Fun2) (h1 h2 : Fun1)
  (Df_g_F2 : Fun2) (Df_h1_F1 Df_h2_F1 : Fun1) -> Fun1
Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1 =
  let
    L1F = L1_F1_of g h1 h2
    L2F = L2_F1_of g h1 h2
    L3F = L3_F1_of g h1 h2
    L4F = L4_F1_of g h1 h2
    L5F = L5_F1_of g h1 h2

    d_axC_F1   = Df_axC g h1 h2
    d_stepB_F1 = d_step_B_F1_of g h1 h2 Df_h1_F1
    d_stepC_F1 = d_step_C_F1_of g h1 h2 Df_h2_F1
    d_stepD_F1 = d_step_D_F1_of g h1 h2 Df_g_F2

    trans_AB_F1 = Df_eqTrans_F1 d_axC_F1 d_stepB_F1 L1F L2F L3F
    trans_AC_F1 = Df_eqTrans_F1 trans_AB_F1 d_stepC_F1 L1F L3F L4F
    trans_AD_F1 = Df_eqTrans_F1 trans_AC_F1 d_stepD_F1 L1F L4F L5F
  in trans_AD_F1

------------------------------------------------------------------------
-- Closure equation : ap1 Df_C_F1 X =Deriv= Df_C g h1 h2 ... X .

Df_C_F1_unfold :
  (g : Fun2) (h1 h2 : Fun1)
  (Df_g_F2 : Fun2) (Df_h1_F1 Df_h2_F1 : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1) X)
              (Df_C g h1 h2
                (\ A B -> ap2 Df_g_F2 A B)
                (\ Z -> ap1 Df_h1_F1 Z)
                (\ Z -> ap1 Df_h2_F1 Z)
                X))
Df_C_F1_unfold g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1 X =
  let
    -- Fun1 layer.
    L1F = L1_F1_of g h1 h2
    L2F = L2_F1_of g h1 h2
    L3F = L3_F1_of g h1 h2
    L4F = L4_F1_of g h1 h2
    L5F = L5_F1_of g h1 h2

    d_axC_F1   = Df_axC g h1 h2
    d_stepB_F1 = d_step_B_F1_of g h1 h2 Df_h1_F1
    d_stepC_F1 = d_step_C_F1_of g h1 h2 Df_h2_F1
    d_stepD_F1 = d_step_D_F1_of g h1 h2 Df_g_F2

    trans_AB_F1 = Df_eqTrans_F1 d_axC_F1 d_stepB_F1 L1F L2F L3F
    trans_AC_F1 = Df_eqTrans_F1 trans_AB_F1 d_stepC_F1 L1F L3F L4F

    -- Concrete Term layer.
    L1 : Term
    L1 = encH_at (C g h1 h2) X

    L2 : Term
    L2 = encG_at g (encH_at h1 X) (encH_at h2 X)

    L3 : Term
    L3 = encG_at g (ap1 num (ap1 h1 X)) (encH_at h2 X)

    L4 : Term
    L4 = encG_at g (ap1 num (ap1 h1 X)) (ap1 num (ap1 h2 X))

    L5 : Term
    L5 = ap1 num (ap2 g (ap1 h1 X) (ap1 h2 X))

    d_axC_T : Term
    d_axC_T = ap1 (Df_axC g h1 h2) X

    d_stepB_T : Term
    d_stepB_T =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (Df_axEqCongL g (encH_at h1 X) (ap1 num (ap1 h1 X)) (encH_at h2 X))
          (ap1 Df_h1_F1 X))

    d_stepC_T : Term
    d_stepC_T =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (Df_axEqCongR g (encH_at h2 X) (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X)))
          (ap1 Df_h2_F1 X))

    d_stepD_T : Term
    d_stepD_T = ap2 Df_g_F2 (ap1 h1 X) (ap1 h2 X)

    d_trans_AB_T : Term
    d_trans_AB_T = Df_eqTrans d_axC_T d_stepB_T L1 L2 L3

    d_trans_AC_T : Term
    d_trans_AC_T = Df_eqTrans d_trans_AB_T d_stepC_T L1 L3 L4

    -- L_F1 bridges.
    eL1 : Deriv (eqF (ap1 L1F X) L1)
    eL1 = encH_at_F1_eq (C g h1 h2) X

    eL2 : Deriv (eqF (ap1 L2F X) L2)
    eL2 =
      let e_raw :
            Deriv (eqF (ap1 L2F X)
                        (encG_at g (ap1 (encH_at_F1 h1) X) (ap1 (encH_at_F1 h2) X)))
          e_raw = encG_at_F1_eq g (encH_at_F1 h1) (encH_at_F1 h2) X
          -- Bridge inner slots via encH_at_F1_eq.
          eA : Deriv (eqF (ap1 (encH_at_F1 h1) X) (encH_at h1 X))
          eA = encH_at_F1_eq h1 X
          eB : Deriv (eqF (ap1 (encH_at_F1 h2) X) (encH_at h2 X))
          eB = encH_at_F1_eq h2 X
          inner_pair :
            Deriv (eqF (ap2 Pair (ap1 (encH_at_F1 h1) X) (ap1 (encH_at_F1 h2) X))
                        (ap2 Pair (encH_at h1 X) (encH_at h2 X)))
          inner_pair =
            ruleTrans (congL Pair (ap1 (encH_at_F1 h2) X) eA)
                      (congR Pair (encH_at h1 X) eB)
          ie : Deriv (eqF (encG_at g (ap1 (encH_at_F1 h1) X) (ap1 (encH_at_F1 h2) X))
                          (encG_at g (encH_at h1 X) (encH_at h2 X)))
          ie = congR Pair (natCode tag_ap2)
                 (congR Pair (codeFun2 g) inner_pair)
      in ruleTrans e_raw ie

    eL3 : Deriv (eqF (ap1 L3F X) L3)
    eL3 =
      let e_raw :
            Deriv (eqF (ap1 L3F X)
                        (encG_at g (ap1 (numH_F1 h1) X) (ap1 (encH_at_F1 h2) X)))
          e_raw = encG_at_F1_eq g (numH_F1 h1) (encH_at_F1 h2) X
          eA : Deriv (eqF (ap1 (numH_F1 h1) X) (ap1 num (ap1 h1 X)))
          eA = numH_F1_eq h1 X
          eB : Deriv (eqF (ap1 (encH_at_F1 h2) X) (encH_at h2 X))
          eB = encH_at_F1_eq h2 X
          inner_pair :
            Deriv (eqF (ap2 Pair (ap1 (numH_F1 h1) X) (ap1 (encH_at_F1 h2) X))
                        (ap2 Pair (ap1 num (ap1 h1 X)) (encH_at h2 X)))
          inner_pair =
            ruleTrans (congL Pair (ap1 (encH_at_F1 h2) X) eA)
                      (congR Pair (ap1 num (ap1 h1 X)) eB)
          ie : Deriv (eqF (encG_at g (ap1 (numH_F1 h1) X) (ap1 (encH_at_F1 h2) X))
                          (encG_at g (ap1 num (ap1 h1 X)) (encH_at h2 X)))
          ie = congR Pair (natCode tag_ap2)
                 (congR Pair (codeFun2 g) inner_pair)
      in ruleTrans e_raw ie

    eL4 : Deriv (eqF (ap1 L4F X) L4)
    eL4 =
      let e_raw :
            Deriv (eqF (ap1 L4F X)
                        (encG_at g (ap1 (numH_F1 h1) X) (ap1 (numH_F1 h2) X)))
          e_raw = encG_at_F1_eq g (numH_F1 h1) (numH_F1 h2) X
          eA : Deriv (eqF (ap1 (numH_F1 h1) X) (ap1 num (ap1 h1 X)))
          eA = numH_F1_eq h1 X
          eB : Deriv (eqF (ap1 (numH_F1 h2) X) (ap1 num (ap1 h2 X)))
          eB = numH_F1_eq h2 X
          inner_pair :
            Deriv (eqF (ap2 Pair (ap1 (numH_F1 h1) X) (ap1 (numH_F1 h2) X))
                        (ap2 Pair (ap1 num (ap1 h1 X)) (ap1 num (ap1 h2 X))))
          inner_pair =
            ruleTrans (congL Pair (ap1 (numH_F1 h2) X) eA)
                      (congR Pair (ap1 num (ap1 h1 X)) eB)
          ie : Deriv (eqF (encG_at g (ap1 (numH_F1 h1) X) (ap1 (numH_F1 h2) X))
                          (encG_at g (ap1 num (ap1 h1 X)) (ap1 num (ap1 h2 X))))
          ie = congR Pair (natCode tag_ap2)
                 (congR Pair (codeFun2 g) inner_pair)
      in ruleTrans e_raw ie

    -- L5_F1 = compose1U num (C g h1 h2) : ap1 L5F X = num ((C g h1 h2) X) = num (g (h1 X) (h2 X)).
    eL5 : Deriv (eqF (ap1 L5F X) L5)
    eL5 =
      let e_step1 : Deriv (eqF (ap1 (compose1U num (C g h1 h2)) X)
                                (ap1 num (ap1 (C g h1 h2) X)))
          e_step1 = axComp num (C g h1 h2) X
          e_step2 : Deriv (eqF (ap1 (C g h1 h2) X) (ap2 g (ap1 h1 X) (ap1 h2 X)))
          e_step2 = ax_C g h1 h2 X
      in ruleTrans e_step1 (cong1 num e_step2)

    -- d_axC_F1 = Df_axC g h1 h2 (already Fun1).  ap1 d_axC_F1 X = d_axC_T  (refl).
    e_axC : Deriv (eqF (ap1 d_axC_F1 X) d_axC_T)
    e_axC = axRefl d_axC_T

    -- d_stepB_F1 closure.
    e_stepB : Deriv (eqF (ap1 d_stepB_F1 X) d_stepB_T)
    e_stepB =
      let
        e_eqCongL_F1 :
          Deriv (eqF (ap1 (Df_axEqCongL_F1 g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2)) X)
                      (Df_axEqCongL g (ap1 (encH_at_F1 h1) X) (ap1 (numH_F1 h1) X) (ap1 (encH_at_F1 h2) X)))
        e_eqCongL_F1 = Df_axEqCongL_F1_eq g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2) X

        e_axEqCongL_args :
          Deriv (eqF (Df_axEqCongL g (ap1 (encH_at_F1 h1) X) (ap1 (numH_F1 h1) X) (ap1 (encH_at_F1 h2) X))
                      (Df_axEqCongL g (encH_at h1 X) (ap1 num (ap1 h1 X)) (encH_at h2 X)))
        e_axEqCongL_args =
          Df_axEqCongL_cong g
            (ap1 (encH_at_F1 h1) X) (encH_at h1 X)
            (ap1 (numH_F1 h1) X) (ap1 num (ap1 h1 X))
            (ap1 (encH_at_F1 h2) X) (encH_at h2 X)
            (encH_at_F1_eq h1 X) (numH_F1_eq h1 X) (encH_at_F1_eq h2 X)

        -- Combine.
        e_eqCongL :
          Deriv (eqF (ap1 (Df_axEqCongL_F1 g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2)) X)
                      (Df_axEqCongL g (encH_at h1 X) (ap1 num (ap1 h1 X)) (encH_at h2 X)))
        e_eqCongL = ruleTrans e_eqCongL_F1 e_axEqCongL_args

        -- mpWrapF1_eq
        e_mp_raw :
          Deriv (eqF (ap1 d_stepB_F1 X)
                      (ap2 Pair (natCode tag_mp)
                        (ap2 Pair (ap1 (Df_axEqCongL_F1 g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2)) X)
                                  (ap1 Df_h1_F1 X))))
        e_mp_raw = mpWrapF1_eq
                     (Df_axEqCongL_F1 g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2))
                     Df_h1_F1 X

        e_inner_bridge :
          Deriv (eqF
            (ap2 Pair (ap1 (Df_axEqCongL_F1 g (encH_at_F1 h1) (numH_F1 h1) (encH_at_F1 h2)) X)
                      (ap1 Df_h1_F1 X))
            (ap2 Pair (Df_axEqCongL g (encH_at h1 X) (ap1 num (ap1 h1 X)) (encH_at h2 X))
                      (ap1 Df_h1_F1 X)))
        e_inner_bridge = congL Pair (ap1 Df_h1_F1 X) e_eqCongL
      in ruleTrans e_mp_raw (congR Pair (natCode tag_mp) e_inner_bridge)

    -- d_stepC_F1 closure (symmetric to e_stepB).
    e_stepC : Deriv (eqF (ap1 d_stepC_F1 X) d_stepC_T)
    e_stepC =
      let
        e_eqCongR_F1 :
          Deriv (eqF (ap1 (Df_axEqCongR_F1 g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1)) X)
                      (Df_axEqCongR g (ap1 (encH_at_F1 h2) X) (ap1 (numH_F1 h2) X) (ap1 (numH_F1 h1) X)))
        e_eqCongR_F1 = Df_axEqCongR_F1_eq g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1) X

        e_axEqCongR_args :
          Deriv (eqF (Df_axEqCongR g (ap1 (encH_at_F1 h2) X) (ap1 (numH_F1 h2) X) (ap1 (numH_F1 h1) X))
                      (Df_axEqCongR g (encH_at h2 X) (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X))))
        e_axEqCongR_args =
          Df_axEqCongR_cong g
            (ap1 (encH_at_F1 h2) X) (encH_at h2 X)
            (ap1 (numH_F1 h2) X) (ap1 num (ap1 h2 X))
            (ap1 (numH_F1 h1) X) (ap1 num (ap1 h1 X))
            (encH_at_F1_eq h2 X) (numH_F1_eq h2 X) (numH_F1_eq h1 X)

        e_eqCongR :
          Deriv (eqF (ap1 (Df_axEqCongR_F1 g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1)) X)
                      (Df_axEqCongR g (encH_at h2 X) (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X))))
        e_eqCongR = ruleTrans e_eqCongR_F1 e_axEqCongR_args

        e_mp_raw :
          Deriv (eqF (ap1 d_stepC_F1 X)
                      (ap2 Pair (natCode tag_mp)
                        (ap2 Pair (ap1 (Df_axEqCongR_F1 g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1)) X)
                                  (ap1 Df_h2_F1 X))))
        e_mp_raw = mpWrapF1_eq
                     (Df_axEqCongR_F1 g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1))
                     Df_h2_F1 X

        e_inner_bridge :
          Deriv (eqF
            (ap2 Pair (ap1 (Df_axEqCongR_F1 g (encH_at_F1 h2) (numH_F1 h2) (numH_F1 h1)) X)
                      (ap1 Df_h2_F1 X))
            (ap2 Pair (Df_axEqCongR g (encH_at h2 X) (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X)))
                      (ap1 Df_h2_F1 X)))
        e_inner_bridge = congL Pair (ap1 Df_h2_F1 X) e_eqCongR
      in ruleTrans e_mp_raw (congR Pair (natCode tag_mp) e_inner_bridge)

    -- d_stepD_F1 closure : ap1 (C Df_g_F2 h1 h2) X = ap2 Df_g_F2 (h1 X) (h2 X).
    e_stepD : Deriv (eqF (ap1 d_stepD_F1 X) d_stepD_T)
    e_stepD = ax_C Df_g_F2 h1 h2 X

    ---------------------------------------------------------------
    -- Chain three Df_eqTrans_F1 closures via Df_eqTrans_T_cong .
    ---------------------------------------------------------------

    -- Step AB.
    e_trans_AB_raw :
      Deriv (eqF (ap1 trans_AB_F1 X)
                  (Df_eqTrans (ap1 d_axC_F1 X) (ap1 d_stepB_F1 X)
                              (ap1 L1F X) (ap1 L2F X) (ap1 L3F X)))
    e_trans_AB_raw = Df_eqTrans_F1_eq d_axC_F1 d_stepB_F1 L1F L2F L3F X

    e_trans_AB_cong :
      Deriv (eqF (Df_eqTrans (ap1 d_axC_F1 X) (ap1 d_stepB_F1 X)
                             (ap1 L1F X) (ap1 L2F X) (ap1 L3F X))
                  d_trans_AB_T)
    e_trans_AB_cong =
      Df_eqTrans_T_cong (ap1 d_axC_F1 X) d_axC_T
                         (ap1 d_stepB_F1 X) d_stepB_T
                         (ap1 L1F X) L1
                         (ap1 L2F X) L2
                         (ap1 L3F X) L3
                         e_axC e_stepB eL1 eL2 eL3

    e_trans_AB : Deriv (eqF (ap1 trans_AB_F1 X) d_trans_AB_T)
    e_trans_AB = ruleTrans e_trans_AB_raw e_trans_AB_cong

    -- Step AC.
    e_trans_AC_raw :
      Deriv (eqF (ap1 trans_AC_F1 X)
                  (Df_eqTrans (ap1 trans_AB_F1 X) (ap1 d_stepC_F1 X)
                              (ap1 L1F X) (ap1 L3F X) (ap1 L4F X)))
    e_trans_AC_raw = Df_eqTrans_F1_eq trans_AB_F1 d_stepC_F1 L1F L3F L4F X

    e_trans_AC_cong :
      Deriv (eqF (Df_eqTrans (ap1 trans_AB_F1 X) (ap1 d_stepC_F1 X)
                             (ap1 L1F X) (ap1 L3F X) (ap1 L4F X))
                  d_trans_AC_T)
    e_trans_AC_cong =
      Df_eqTrans_T_cong (ap1 trans_AB_F1 X) d_trans_AB_T
                         (ap1 d_stepC_F1 X) d_stepC_T
                         (ap1 L1F X) L1
                         (ap1 L3F X) L3
                         (ap1 L4F X) L4
                         e_trans_AB e_stepC eL1 eL3 eL4

    e_trans_AC : Deriv (eqF (ap1 trans_AC_F1 X) d_trans_AC_T)
    e_trans_AC = ruleTrans e_trans_AC_raw e_trans_AC_cong

    -- Step AD.
    e_trans_AD_raw :
      Deriv (eqF (ap1 (Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1) X)
                  (Df_eqTrans (ap1 trans_AC_F1 X) (ap1 d_stepD_F1 X)
                              (ap1 L1F X) (ap1 L4F X) (ap1 L5F X)))
    e_trans_AD_raw = Df_eqTrans_F1_eq trans_AC_F1 d_stepD_F1 L1F L4F L5F X

    e_trans_AD_cong :
      Deriv (eqF (Df_eqTrans (ap1 trans_AC_F1 X) (ap1 d_stepD_F1 X)
                             (ap1 L1F X) (ap1 L4F X) (ap1 L5F X))
                  (Df_eqTrans d_trans_AC_T d_stepD_T L1 L4 L5))
    e_trans_AD_cong =
      Df_eqTrans_T_cong (ap1 trans_AC_F1 X) d_trans_AC_T
                         (ap1 d_stepD_F1 X) d_stepD_T
                         (ap1 L1F X) L1
                         (ap1 L4F X) L4
                         (ap1 L5F X) L5
                         e_trans_AC e_stepD eL1 eL4 eL5

  in ruleTrans e_trans_AD_raw e_trans_AD_cong

------------------------------------------------------------------------
-- thm12_C lifted to the Fun1 representation.

thm12_C_F1 :
  (g : Fun2) (h1 h2 : Fun1)
  (Df_g_F2 : Fun2) (Df_h1_F1 Df_h2_F1 : Fun1)
  (ih_g  : (A B : Term) ->
             Deriv (eqF (ap1 thmT (ap2 Df_g_F2 A B)) (codeFTeq2 g A B)))
  (ih_h1 : (Z : Term) ->
             Deriv (eqF (ap1 thmT (ap1 Df_h1_F1 Z)) (codeFTeq1 h1 Z)))
  (ih_h2 : (Z : Term) ->
             Deriv (eqF (ap1 thmT (ap1 Df_h2_F1 Z)) (codeFTeq1 h2 Z)))
  (X : Term) ->
  Deriv (eqF (ap1 thmT (ap1 (Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1) X))
              (codeFTeq1 (C g h1 h2) X))
thm12_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1 ih_g ih_h1 ih_h2 X =
  let
    e_unfold :
      Deriv (eqF (ap1 thmT (ap1 (Df_C_F1 g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1) X))
                  (ap1 thmT (Df_C g h1 h2
                              (\ A B -> ap2 Df_g_F2 A B)
                              (\ Z -> ap1 Df_h1_F1 Z)
                              (\ Z -> ap1 Df_h2_F1 Z)
                              X)))
    e_unfold = cong1 thmT (Df_C_F1_unfold g h1 h2 Df_g_F2 Df_h1_F1 Df_h2_F1 X)

    e_partC :
      Deriv (eqF (ap1 thmT (Df_C g h1 h2
                              (\ A B -> ap2 Df_g_F2 A B)
                              (\ Z -> ap1 Df_h1_F1 Z)
                              (\ Z -> ap1 Df_h2_F1 Z)
                              X))
                  (codeFTeq1 (C g h1 h2) X))
    e_partC = thm12_C g h1 h2
                       (\ A B -> ap2 Df_g_F2 A B)
                       (\ Z -> ap1 Df_h1_F1 Z)
                       (\ Z -> ap1 Df_h2_F1 Z)
                       ih_g ih_h1 ih_h2 X
  in ruleTrans e_unfold e_partC
