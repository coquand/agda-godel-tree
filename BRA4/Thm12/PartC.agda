{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartC -- Theorem 12, case  f = C g h1 h2  (composition).
--
-- Goal (parametric on IHs ; universal in X : Term ; no Closed) :
--
--   thm12_C :
--     (g : Fun2) (h1 h2 : Fun1)
--     (Df_g_inst  : Term -> Term -> Term)
--     (Df_h1_inst : Term -> Term)
--     (Df_h2_inst : Term -> Term)
--     (ih_g  : (X1 X2 : Term) ->
--                Deriv (eqF (ap1 thmT (Df_g_inst X1 X2)) (codeFTeq2 g X1 X2)))
--     (ih_h1 : (X : Term) ->
--                Deriv (eqF (ap1 thmT (Df_h1_inst X)) (codeFTeq1 h1 X)))
--     (ih_h2 : (X : Term) ->
--                Deriv (eqF (ap1 thmT (Df_h2_inst X)) (codeFTeq1 h2 X)))
--     (X : Term) ->
--     Deriv (eqF (ap1 thmT (Df_C g h1 h2 Df_g_inst Df_h1_inst Df_h2_inst X))
--                 (codeFTeq1 (C g h1 h2) X))
--
-- Construction.  Build an encoded eq-chain (left-aligned):
--
--   L1  =  encoded "(C g h1 h2) (num X)"
--       = Pair tag_ap1 (Pair (codeFun1 (C g h1 h2)) (num X))
--   L2  =  encoded "g (h1 (num X), h2 (num X))"
--       = Pair tag_ap2 (Pair (codeFun2 g) (Pair encH1X encH2X))
--   L3  =  encoded "g (num (h1 X), h2 (num X))"
--       = Pair tag_ap2 (Pair (codeFun2 g) (Pair (num (h1 X)) encH2X))
--   L4  =  encoded "g (num (h1 X), num (h2 X))"
--       = Pair tag_ap2 (Pair (codeFun2 g) (Pair (num (h1 X)) (num (h2 X))))
--   L5  =  num (g (h1 X) (h2 X))
--
-- Chain :
--   enc(L1 = L2)  via EncodedAxC.
--   enc(L2 = L3)  via EncodedAxEqCongL + encoded_mp on IH_h1.
--   enc(L3 = L4)  via EncodedAxEqCongR + encoded_mp on IH_h2.
--   enc(L4 = L5)  via IH_g at (h1 X) (h2 X).
-- Compose via encoded_eqTrans 3 times to obtain enc(L1 = L5).
--
-- Final bridge :  L5 = num ((C g h1 h2) X)  via cong1 num (ruleSym (ax_C ...)) ;
-- lifted through the outer Pair structure to convert  encEq L1 L5  into
--  codeFTeq1 (C g h1 h2) X .

module BRA4.Thm12.PartC where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 )
open import BRA4.Num               using ( num )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 ; codeFTeq2 )
open import BRA4.Thm12.EncodedAxC
  using ( Df_axC ; encodedAxC ; encodedAxC_Term )
open import BRA4.Thm12.EncodedAxEqCongL
  using ( Df_axEqCongL ; encodedAxEqCongL ; encodedAxEqCongL_Term )
open import BRA4.Thm12.EncodedAxEqCongR
  using ( Df_axEqCongR ; encodedAxEqCongR ; encodedAxEqCongR_Term )
open import BRA4.Thm12.EncodedMp   using ( encoded_mp )
open import BRA4.Thm12.EncodedEqChain
  using ( encEq ; Df_eqTrans ; encoded_eqTrans )

------------------------------------------------------------------------
-- Encoded sub-Term helpers.

private
  encH_at : Fun1 -> Term -> Term
  encH_at h X = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 h) (ap1 num X))

  encG_at : Fun2 -> Term -> Term -> Term
  encG_at g A B =
    ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair A B))

------------------------------------------------------------------------
-- Df_C : the Term-level constructor for the encoded composition proof.

private
  -- Step B's imp-proof : the encoded ax_eqCongL specialisation.
  --   ih ax  : thmT (Df_axEqCongL g encH1X (num (h1 X)) encH2X)
  --             = enc((encH1X = num (h1 X)) > (encG g encH1X encH2X
  --                                              = encG g (num (h1 X)) encH2X))
  -- mp with IH_h1 yields enc(L2 = L3) at the wrap site:
  Df_step_B : (g : Fun2) (h1 h2 : Fun1) (Df_h1_inst : Term -> Term) (X : Term) -> Term
  Df_step_B g h1 h2 Df_h1_inst X =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair (Df_axEqCongL g (encH_at h1 X) (ap1 num (ap1 h1 X)) (encH_at h2 X))
                (Df_h1_inst X))

  Df_step_C : (g : Fun2) (h1 h2 : Fun1) (Df_h2_inst : Term -> Term) (X : Term) -> Term
  Df_step_C g h1 h2 Df_h2_inst X =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair (Df_axEqCongR g (encH_at h2 X) (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X)))
                (Df_h2_inst X))

Df_C :
  (g : Fun2) (h1 h2 : Fun1)
  (Df_g_inst : Term -> Term -> Term)
  (Df_h1_inst : Term -> Term)
  (Df_h2_inst : Term -> Term)
  (X : Term) -> Term
Df_C g h1 h2 Df_g_inst Df_h1_inst Df_h2_inst X =
  let
    L1 = encH_at (C g h1 h2) X
    L2 = encG_at g (encH_at h1 X) (encH_at h2 X)
    L3 = encG_at g (ap1 num (ap1 h1 X)) (encH_at h2 X)
    L4 = encG_at g (ap1 num (ap1 h1 X)) (ap1 num (ap1 h2 X))
    L5 = ap1 num (ap2 g (ap1 h1 X) (ap1 h2 X))

    d_axC : Term
    d_axC = ap1 (Df_axC g h1 h2) X

    d_step_B : Term
    d_step_B = Df_step_B g h1 h2 Df_h1_inst X

    d_step_C : Term
    d_step_C = Df_step_C g h1 h2 Df_h2_inst X

    d_step_D : Term
    d_step_D = Df_g_inst (ap1 h1 X) (ap1 h2 X)

    -- Chain via 3 encoded_eqTrans :
    --   d_axC          : enc(L1 = L2)
    --   d_step_B       : enc(L2 = L3)
    --   d_step_C       : enc(L3 = L4)
    --   d_step_D       : enc(L4 = L5)

    d_trans_AB : Term
    d_trans_AB = Df_eqTrans d_axC d_step_B L1 L2 L3

    d_trans_AC : Term
    d_trans_AC = Df_eqTrans d_trans_AB d_step_C L1 L3 L4

    d_trans_AD : Term
    d_trans_AD = Df_eqTrans d_trans_AC d_step_D L1 L4 L5
  in d_trans_AD

------------------------------------------------------------------------
-- The main theorem.

thm12_C :
  (g : Fun2) (h1 h2 : Fun1)
  (Df_g_inst  : Term -> Term -> Term)
  (Df_h1_inst : Term -> Term)
  (Df_h2_inst : Term -> Term)
  (ih_g  : (X1 X2 : Term) ->
             Deriv (eqF (ap1 thmT (Df_g_inst X1 X2)) (codeFTeq2 g X1 X2)))
  (ih_h1 : (X : Term) ->
             Deriv (eqF (ap1 thmT (Df_h1_inst X)) (codeFTeq1 h1 X)))
  (ih_h2 : (X : Term) ->
             Deriv (eqF (ap1 thmT (Df_h2_inst X)) (codeFTeq1 h2 X)))
  (X : Term) ->
  Deriv (eqF (ap1 thmT (Df_C g h1 h2 Df_g_inst Df_h1_inst Df_h2_inst X))
              (codeFTeq1 (C g h1 h2) X))
thm12_C g h1 h2 Df_g_inst Df_h1_inst Df_h2_inst ih_g ih_h1 ih_h2 X =
  let
    L1 = encH_at (C g h1 h2) X
    L2 = encG_at g (encH_at h1 X) (encH_at h2 X)
    L3 = encG_at g (ap1 num (ap1 h1 X)) (encH_at h2 X)
    L4 = encG_at g (ap1 num (ap1 h1 X)) (ap1 num (ap1 h2 X))
    L5 = ap1 num (ap2 g (ap1 h1 X) (ap1 h2 X))

    ---------------------------------------------------------------
    -- Step A : enc(L1 = L2)  via EncodedAxC.
    --
    -- encodedAxC_Term g h1 h2 X  is  Pair tag_eq (Pair L1 L2)  by
    -- definition of  encCodeLHS / encCodeRHS  in  EncodedAxC .
    ---------------------------------------------------------------

    d_axC : Term
    d_axC = ap1 (Df_axC g h1 h2) X

    e_step_A : Deriv (eqF (ap1 thmT d_axC) (encEq L1 L2))
    e_step_A = encodedAxC g h1 h2 X

    ---------------------------------------------------------------
    -- Step B : enc(L2 = L3)  via EncodedAxEqCongL + encoded_mp on IH_h1.
    --
    -- EncodedAxEqCongL with tA:=encH1X, tB:=num(h1 X), tC:=encH2X :
    --   enc((encH1X = num(h1 X)) > (encG g encH1X encH2X
    --                                = encG g (num(h1 X)) encH2X))
    --   = enc((L2_premise) > (L2 = L3))   (premise is the antPart)
    ---------------------------------------------------------------

    encH1X : Term
    encH1X = encH_at h1 X

    encH2X : Term
    encH2X = encH_at h2 X

    -- The "ant" of the EqCongL imp = encEq encH1X (num (h1 X)) = codeFTeq1 h1 X.
    antB : Term
    antB = encEq encH1X (ap1 num (ap1 h1 X))

    -- The "cons" of the EqCongL imp = encEq L2 L3.
    consB : Term
    consB = encEq L2 L3

    -- The ih for ax instance.
    ih_ax_B :
      Deriv (eqF (ap1 thmT (Df_axEqCongL g encH1X (ap1 num (ap1 h1 X)) encH2X))
                  (encodedAxEqCongL_Term g encH1X (ap1 num (ap1 h1 X)) encH2X))
    ih_ax_B = encodedAxEqCongL g encH1X (ap1 num (ap1 h1 X)) encH2X

    -- IH_h1 : thmT (Df_h1_inst X) = codeFTeq1 h1 X = encEq encH1X (num (h1 X)).
    -- These are definitionally equal.
    ih_h1_typed :
      Deriv (eqF (ap1 thmT (Df_h1_inst X)) antB)
    ih_h1_typed = ih_h1 X

    d_step_B : Term
    d_step_B = Df_step_B g h1 h2 Df_h1_inst X

    e_step_B :
      Deriv (eqF (ap1 thmT d_step_B) consB)
    e_step_B = encoded_mp
                 (Df_axEqCongL g encH1X (ap1 num (ap1 h1 X)) encH2X)
                 (Df_h1_inst X)
                 antB consB
                 ih_ax_B ih_h1_typed

    ---------------------------------------------------------------
    -- Step C : enc(L3 = L4)  via EncodedAxEqCongR + encoded_mp on IH_h2.
    --
    -- EncodedAxEqCongR with tA:=encH2X, tB:=num(h2 X), tC:=num(h1 X) :
    --   enc((encH2X = num(h2 X)) > (encG g (num(h1 X)) encH2X
    --                                = encG g (num(h1 X)) (num(h2 X))))
    ---------------------------------------------------------------

    antC : Term
    antC = encEq encH2X (ap1 num (ap1 h2 X))

    consC : Term
    consC = encEq L3 L4

    ih_ax_C :
      Deriv (eqF (ap1 thmT (Df_axEqCongR g encH2X (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X))))
                  (encodedAxEqCongR_Term g encH2X (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X))))
    ih_ax_C = encodedAxEqCongR g encH2X (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X))

    ih_h2_typed :
      Deriv (eqF (ap1 thmT (Df_h2_inst X)) antC)
    ih_h2_typed = ih_h2 X

    d_step_C : Term
    d_step_C = Df_step_C g h1 h2 Df_h2_inst X

    e_step_C :
      Deriv (eqF (ap1 thmT d_step_C) consC)
    e_step_C = encoded_mp
                 (Df_axEqCongR g encH2X (ap1 num (ap1 h2 X)) (ap1 num (ap1 h1 X)))
                 (Df_h2_inst X)
                 antC consC
                 ih_ax_C ih_h2_typed

    ---------------------------------------------------------------
    -- Step D : enc(L4 = L5)  via IH_g at (h1 X) (h2 X).
    --
    -- codeFTeq2 g (h1 X) (h2 X) = encEq L4 L5  by definition.
    ---------------------------------------------------------------

    d_step_D : Term
    d_step_D = Df_g_inst (ap1 h1 X) (ap1 h2 X)

    e_step_D :
      Deriv (eqF (ap1 thmT d_step_D) (encEq L4 L5))
    e_step_D = ih_g (ap1 h1 X) (ap1 h2 X)

    ---------------------------------------------------------------
    -- Chain via encoded_eqTrans (3 times) to obtain enc(L1 = L5).
    ---------------------------------------------------------------

    d_trans_AB : Term
    d_trans_AB = Df_eqTrans d_axC d_step_B L1 L2 L3

    e_trans_AB : Deriv (eqF (ap1 thmT d_trans_AB) (encEq L1 L3))
    e_trans_AB = encoded_eqTrans d_axC d_step_B L1 L2 L3 e_step_A e_step_B

    d_trans_AC : Term
    d_trans_AC = Df_eqTrans d_trans_AB d_step_C L1 L3 L4

    e_trans_AC : Deriv (eqF (ap1 thmT d_trans_AC) (encEq L1 L4))
    e_trans_AC = encoded_eqTrans d_trans_AB d_step_C L1 L3 L4 e_trans_AB e_step_C

    d_trans_AD : Term
    d_trans_AD = Df_eqTrans d_trans_AC d_step_D L1 L4 L5

    e_trans_AD : Deriv (eqF (ap1 thmT d_trans_AD) (encEq L1 L5))
    e_trans_AD = encoded_eqTrans d_trans_AC d_step_D L1 L4 L5 e_trans_AC e_step_D

    ---------------------------------------------------------------
    -- Final bridge :  encEq L1 L5  =  codeFTeq1 (C g h1 h2) X .
    --
    -- L5 = num (g (h1 X) (h2 X))  and  codeFTeq1 (C g h1 h2) X's RHS is
    --   num ((C g h1 h2) X) .
    -- By ax_C g h1 h2 X :  (C g h1 h2) X = g (h1 X) (h2 X) .
    -- So num ((C g h1 h2) X) = num (g (h1 X) (h2 X)) = L5  by cong1 num .
    -- We need encEq L1 L5 = encEq L1 (num ((C g h1 h2) X))  via congR Pair .
    ---------------------------------------------------------------

    axC_eq :
      Deriv (eqF (ap1 (C g h1 h2) X) (ap2 g (ap1 h1 X) (ap1 h2 X)))
    axC_eq = ax_C g h1 h2 X

    num_lift :
      Deriv (eqF (ap1 num (ap1 (C g h1 h2) X)) L5)
    num_lift = cong1 num axC_eq

    num_lift_sym :
      Deriv (eqF L5 (ap1 num (ap1 (C g h1 h2) X)))
    num_lift_sym = ruleSym num_lift

    inner_pair_bridge :
      Deriv (eqF (ap2 Pair L1 L5)
                  (ap2 Pair L1 (ap1 num (ap1 (C g h1 h2) X))))
    inner_pair_bridge = congR Pair L1 num_lift_sym

    outer_bridge :
      Deriv (eqF (encEq L1 L5)
                  (ap2 Pair (natCode tag_eq) (ap2 Pair L1 (ap1 num (ap1 (C g h1 h2) X)))))
    outer_bridge = congR Pair (natCode tag_eq) inner_pair_bridge

    -- codeFTeq1 (C g h1 h2) X expands to
    --   Pair tag_eq (Pair (Pair tag_ap1 (Pair (codeFun1 (C g h1 h2)) (num X)))
    --                      (num ((C g h1 h2) X)))
    -- and  L1 = Pair tag_ap1 (Pair (codeFun1 (C g h1 h2)) (num X))  by
    -- definition of  encH_at .  So  outer_bridge  's RHS is definitionally
    --  codeFTeq1 (C g h1 h2) X .

  in ruleTrans e_trans_AD outer_bridge
