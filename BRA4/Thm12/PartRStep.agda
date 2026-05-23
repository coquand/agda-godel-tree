{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Thm12.PartRStep -- Theorem 12, R-case STEP (Y -> s Y).
--
-- *** STATUS 2026-05-19 SESSION C (PHASE 1B STEPS 1-3) ***
--
-- SHIPPED CUMULATIVELY (Sessions B + C) :
--   * META-level step transformation  thm12_R_step_meta .
--   * kF1 closed-Term Fun1 helper + codeFun1/2_closed.
--   * codeTerm_closed.
--   * Closure proofs : packAx2_O, packAx4_O, z_axU_v0, z_axRefl_v0,
--     layer*_code, packAx10_R, packAx6, packAx7.
--   * Pair-builder Fun1 helpers : pairF1, mpWrapF1, codeFun1/2_F1,
--     L1/L2/L3_F1 (base), spec2_F1, spec3_F1, encH1_F1, encH2_at_F1,
--     encR_at_F1, num_apply2_F1, L1_step_F1, L5_step_F1.
--   * axEqTrans_F1, refl_meta_F1.
--   * Df_axEqTrans_cong, Df_refl_meta_cong, Df_eqSym_T_cong, Df_eqTrans_T_cong.
--   * baseF1 + baseF1_eq.
--   * Extractor Fun1's : extract_X_F1, extract_Y_F1, extract_prev_F1.
--
--   *** Phase 1B Step 1 (Session C) *** :
--   * Df_axRStep_F1 + Df_axRStep_F1_eq (sb2-wrap of axN10).
--   * Df_axEqCongL_F1 + Df_axEqCongL_F1_eq (sb3-wrap of axN6).
--   * Df_axEqCongR_F1 + Df_axEqCongR_F1_eq (sb3-wrap of axN7).
--
--   *** Phase 1B Step 2 (Session C) *** :
--   * Df_eqSym_F1 + Df_eqSym_F1_eq , Df_eqTrans_F1 + Df_eqTrans_F1_eq.
--   * stepF1 (Fun1 step function for Dg) + stepF1_eq (closure equation
--     at p = Pair (Pair X Y) prev).
--
--   *** Phase 1B Step 3 (Session C) *** :
--   * Dg : Fun2 -- the BRA primitive recursor  R baseF1 (Post stepF1 Pair) Pair .
--   * dg_at_O_red : Dg X O = baseF1 X (via ax_R_base).
--   * dg_at_succ_red : Dg X (s Y) = stepF1 (Pair (Pair X Y) (Dg X Y))
--     (via ax_R_step + axPost).
--
-- Total cumulative : ~2930 LoC.  Fresh chain to PartRStep : ~8s.
--
-- REMAINING for Phase 1 completion (next session) :
--   * Step 4 -- imp_encoded_mp : Carneiro-lifted encoded_mp .
--     Requires imp-lifting thmT_at_mp (BRA4/ThmTAtMp.agda lines 830-1300 :
--     ~470 LoC of cov_spec dispatch chain).  BRA3's analogous lift was
--     1000+ LoC ; estimate similar here.
--   * Step 5 -- step_proof_imp : impEqTrans chain via dg_at_succ_red +
--     imp-lifted thm12_R_step_meta + RHS bridge.  Estimate ~250 LoC ,
--     blocked on Step 4.
--   * Step 6 -- ruleIndNat + ruleInst2 -> thm12_R : Formula bridges
--     (bridge_codeFTeq2 , bridge_simSubst_codeFTeq2) + base_proof +
--     step_proof_imp_substF + ruleIndNat 0 .  Estimate ~200 LoC ,
--     blocked on Step 5.
--
-- Total Phase 1 remaining : ~1500-1700 LoC (driven by Step 4 size).
--
-- Goal (META-level step transformation; the building block consumed by
-- the ruleIndNat assembly):
--
--   thm12_R_step_meta :
--     (g : Fun1) (h1 h2 : Fun2)
--     (Df_h1_inst : Term -> Term -> Term)
--     (Df_h2_inst : Term -> Term -> Term)
--     (ih_h1 : (A B : Term) ->
--               Deriv (eqF (ap1 thmT (Df_h1_inst A B)) (codeFTeq2 h1 A B)))
--     (ih_h2 : (A B : Term) ->
--               Deriv (eqF (ap1 thmT (Df_h2_inst A B)) (codeFTeq2 h2 A B)))
--     (X Y : Term) (Df_R_prev : Term)
--     (ih_R_prev : Deriv (eqF (ap1 thmT Df_R_prev) (codeFTeq2 (R g h1 h2) X Y))) ->
--     Deriv (eqF (ap1 thmT (Df_R_step g h1 h2 Df_h1_inst Df_h2_inst Df_R_prev X Y))
--                 (codeFTeq2 (R g h1 h2) X (ap1 s Y)))
--
-- Construction.  Build the encoded eq-chain (left-aligned):
--
--   L1   =  encoded "R g h1 h2 (num X, s_enc(num Y))"   [output of encodedAxRStep]
--   L2   =  encoded "h1 (encH2(num X, num Y), encR(num X, num Y))"  [other output of encodedAxRStep]
--   L3   =  encoded "h1 (num (h2 X Y), encR(num X, num Y))"          [step B: IH_h2]
--   L4   =  encoded "h1 (num (h2 X Y), num (R g h1 h2 X Y))"          [step C: IH_R]
--   L5   =  num (h1 (h2 X Y) (R g h1 h2 X Y))                        [step D: IH_h1]
--   (then bridge L5 -> num (R g h1 h2 X (s Y)) via ruleSym ax_R_step.)
--
-- Chain via 3 encoded_eqTrans.
--
-- Final bridges (Term-level lifted through Pair structure):
--   L1  ->  L1' = encR_at(num X, num (s Y))   via num_at_S Y (in reverse: s_enc -> num (s Y)).
--   L5  ->  num (R g h1 h2 X (s Y))            via cong1 num (ruleSym (ax_R_step g h1 h2 X Y)).
--
-- After these bridges  encEq L1 L5  =Deriv=  codeFTeq2 (R g h1 h2) X (s Y).
--
-- The full PartRStep also packages this transformation into a Fun1
-- stepF1 (using BRA combinators on (Pair (Pair X Y) prev)) and the
-- BRA recursor Dg = R baseF1 stepF2 Pair where stepF2 = Post stepF1
-- Pair.  This enables the ruleIndNat assembly with the Carneiro lift.

module BRA4.Thm12.PartRStep where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code              using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import BRA4.Num               using ( num ; num_at_S )
open import BRA4.SbStep
  using ( InertU ; NumCode ; ncNum ; ncAp1 ; ncAp2 ; sbt_inert_NumCode )
open import BRA4.ThmT              using ( thmT )
open import BRA4.Thm12.CodeFTeq    using ( codeFTeq1 ; codeFTeq2 )
open import BRA4.Thm12.EncodedAxRStep
  using ( Df_axRStep ; encodedAxRStep ; encodedAxRStep_Term )
open import BRA4.Thm12.EncodedAxEqTrans
  using ( Df_axEqTrans ; encodedAxEqTrans )
open import BRA4.Thm12.EncodedRefl
  using ( Df_refl_meta ; encoded_refl )
open import BRA4.Thm12.EncodedAxRBase
  using ( Df_axRBase )
open import BRA4.Thm12.PartRBase using ( Df_R_at_O ; thm12_R_at_O )
open import BRA4.Thm12.EncodedAxEqCongL
  using ( Df_axEqCongL ; encodedAxEqCongL ; encodedAxEqCongL_Term )
open import BRA4.Thm12.EncodedAxEqCongR
  using ( Df_axEqCongR ; encodedAxEqCongR ; encodedAxEqCongR_Term )
open import BRA4.Thm12.EncodedMp   using ( encoded_mp ; imp_encoded_mp )
open import BRA4.Thm12.EncodedEqChain
  using ( encEq ; Df_eqTrans ; encoded_eqTrans )
open import BRA4.Thm12.ImpHelpers
  using ( impRefl ; impLift ; impEqTrans )

open import BRA3.Dispatch using
  ( Closed ; mkClosed ; closedAt ; closed_O ; closed_natCode ; closed_ap1 ; closed_ap2 )
open import BRA3.Fan using ( compose1U ; compose1U_eq )
open import BRA3.PairAlgebra using ( Post ; axPost )
open import BRA4.RuleInst2 using ( ruleInst2 ; simSubstT ; simSubstF )

------------------------------------------------------------------------
-- Encoded sub-Term helpers.

private
  -- s-encoded (= encoded "s applied to num Y" in code form).
  s_enc_num : Term -> Term
  s_enc_num Y =
    ap2 Pair (natCode tag_ap1)
      (ap2 Pair (codeFun1 s) (ap1 num Y))

  -- encH2(num X, num Y)  =  encoded "h2 applied to (num X, num Y)".
  encH2_at : Fun2 -> Term -> Term -> Term
  encH2_at h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 h2) (ap2 Pair (ap1 num X) (ap1 num Y)))

  -- encR_at(num X, num Y) = encoded "R g h1 h2 applied to (num X, num Y)".
  encR_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
  encR_at g h1 h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) (ap1 num Y)))

  -- encR_at_s : encoded "R g h1 h2 (num X, s_enc num Y)" (output LHS of encodedAxRStep).
  encR_at_s : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
  encR_at_s g h1 h2 X Y =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) (s_enc_num Y)))

  -- encH1_at(A, B) = Pair tag_ap2 (Pair (codeFun2 h1) (Pair A B))  =  encoded "h1 applied to (A, B)".
  encH1_at : Fun2 -> Term -> Term -> Term
  encH1_at h1 A B =
    ap2 Pair (natCode tag_ap2)
      (ap2 Pair (codeFun2 h1) (ap2 Pair A B))

------------------------------------------------------------------------
-- L-positions (universal in X, Y).

L1_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
L1_at g h1 h2 X Y = encR_at_s g h1 h2 X Y

L2_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
L2_at g h1 h2 X Y =
  encH1_at h1 (encH2_at h2 X Y) (encR_at g h1 h2 X Y)

L3_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
L3_at g h1 h2 X Y =
  encH1_at h1 (ap1 num (ap2 h2 X Y)) (encR_at g h1 h2 X Y)

L4_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
L4_at g h1 h2 X Y =
  encH1_at h1 (ap1 num (ap2 h2 X Y)) (ap1 num (ap2 (R g h1 h2) X Y))

L5_at : Fun2 -> Fun2 -> Fun2 -> Term -> Term -> Term
L5_at g h1 h2 X Y =
  ap1 num (ap2 h1 (ap2 h2 X Y) (ap2 g X Y))

L5_R : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
L5_R g h1 h2 X Y =
  ap1 num (ap2 h1 (ap2 h2 X Y) (ap2 (R g h1 h2) X Y))

-- Bridged LHS slot:  encR_at(num X, num (s Y))  =  encR_at_s g h1 h2 X Y  modulo
-- the inner-rightmost slot.
L1'_at : Fun1 -> Fun2 -> Fun2 -> Term -> Term -> Term
L1'_at g h1 h2 X Y =
  ap2 Pair (natCode tag_ap2)
    (ap2 Pair (codeFun2 (R g h1 h2))
      (ap2 Pair (ap1 num X) (ap1 num (ap1 s Y))))

------------------------------------------------------------------------
-- Df_step_B / Df_step_C : the encoded ax_eqCong{L,R} + encoded_mp wraps.
--
-- Df_step_B  uses  IH_h2  (Df_h2_inst X Y)  at  encH2_at h2 X Y -> num (h2 X Y) ;
-- Df_step_C  uses  IH_R   (Df_R_prev)       at  encR_at g h1 h2 X Y -> num (R g h1 h2 X Y) .

private
  Df_step_B : Fun2 -> Term -> Term -> Term -> Term -> Term
  Df_step_B h1 encH2 num_h2X_Y encR Df_h2_proof =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair (Df_axEqCongL h1 encH2 num_h2X_Y encR) Df_h2_proof)

  Df_step_C : Fun2 -> Term -> Term -> Term -> Term -> Term
  Df_step_C h1 encR num_R_X_Y num_h2_X_Y Df_R_prev =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair (Df_axEqCongR h1 encR num_R_X_Y num_h2_X_Y) Df_R_prev)

------------------------------------------------------------------------
-- Df_R_step : the encoded chain for the step case.
--
--   Df_R_step ... X Y Df_R_prev =
--     Df_eqTrans (Df_eqTrans (Df_eqTrans
--       (encodedAxRStep_proof) (Df_step_B ...) L1 L2 L3)
--       (Df_step_C ...) L1 L3 L4)
--       (Df_h1_proof at (h2 X Y, R g h1 h2 X Y)) L1 L4 L5

Df_R_step :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_h1_inst : Term -> Term -> Term)
  (Df_h2_inst : Term -> Term -> Term)
  (Df_R_prev : Term)
  (X Y : Term) -> Term
Df_R_step g h1 h2 Df_h1_inst Df_h2_inst Df_R_prev X Y =
  let
    L1 = L1_at g h1 h2 X Y
    L2 = L2_at g h1 h2 X Y
    L3 = L3_at g h1 h2 X Y
    L4 = L4_at g h1 h2 X Y
    L5 = L5_R g h1 h2 X Y

    encH2 = encH2_at h2 X Y
    encR  = encR_at g h1 h2 X Y

    d_axRStep : Term
    d_axRStep = Df_axRStep g h1 h2 X Y

    d_step_B : Term
    d_step_B =
      Df_step_B h1 encH2 (ap1 num (ap2 h2 X Y)) encR
                (Df_h2_inst X Y)

    d_step_C : Term
    d_step_C =
      Df_step_C h1 encR (ap1 num (ap2 (R g h1 h2) X Y)) (ap1 num (ap2 h2 X Y))
                Df_R_prev

    d_step_D : Term
    d_step_D = Df_h1_inst (ap2 h2 X Y) (ap2 (R g h1 h2) X Y)

    d_trans_AB : Term
    d_trans_AB = Df_eqTrans d_axRStep d_step_B L1 L2 L3

    d_trans_AC : Term
    d_trans_AC = Df_eqTrans d_trans_AB d_step_C L1 L3 L4

    d_trans_AD : Term
    d_trans_AD = Df_eqTrans d_trans_AC d_step_D L1 L4 L5
  in d_trans_AD

------------------------------------------------------------------------
-- kF1 : Fun1 wrapper for closed Terms.
--
-- For any closed Term c , kF1 c : Fun1 satisfies ap1 (kF1 c) X = c .
--
-- Structural recursion on c .  The  var  case never fires under  Closed
-- (the closure witness contradicts it via closed_var_absurd), but to
-- keep the definition total we use  o  as a placeholder that gets
-- discharged via emptyElim in the closure lemma.
--
-- This is the key building block for assembling baseF1 / stepF1 from
-- the literal Pair-encoded Df expressions.

private
  natEq_refl_aux : (m : Nat) -> Eq (natEq m m) true
  natEq_refl_aux zero    = refl
  natEq_refl_aux (suc m) = natEq_refl_aux m

  absurd_sO_eq_var : (m : Nat) -> Eq (ap1 s O) (var m) -> Empty
  absurd_sO_eq_var m ()

  closed_var_absurd : (m : Nat) -> Closed (var m) -> Empty
  closed_var_absurd m cm =
    let nm : Eq (natEq m m) true
        nm = natEq_refl_aux m
        raw : Eq (boolCase (natEq m m) (ap1 s O) (var m)) (var m)
        raw = closedAt cm m (ap1 s O)
        step : Eq (ap1 s O) (var m)
        step = eqSubst (\ b -> Eq (boolCase b (ap1 s O) (var m)) (var m)) nm raw
    in absurd_sO_eq_var m step

  ap1_get_arg : Term -> Term
  ap1_get_arg O           = O
  ap1_get_arg (var _)     = O
  ap1_get_arg (ap1 _ x)   = x
  ap1_get_arg (ap2 _ _ _) = O

  ap2_get_arg1 : Term -> Term
  ap2_get_arg1 O           = O
  ap2_get_arg1 (var _)     = O
  ap2_get_arg1 (ap1 _ _)   = O
  ap2_get_arg1 (ap2 _ x _) = x

  ap2_get_arg2 : Term -> Term
  ap2_get_arg2 O           = O
  ap2_get_arg2 (var _)     = O
  ap2_get_arg2 (ap1 _ _)   = O
  ap2_get_arg2 (ap2 _ _ y) = y

  ap1_inj : {f : Fun1} {x y : Term} -> Eq (ap1 f x) (ap1 f y) -> Eq x y
  ap1_inj h = eqCong ap1_get_arg h

  ap2_inj_l : {g : Fun2} {x y u v : Term} ->
              Eq (ap2 g x y) (ap2 g u v) -> Eq x u
  ap2_inj_l h = eqCong ap2_get_arg1 h

  ap2_inj_r : {g : Fun2} {x y u v : Term} ->
              Eq (ap2 g x y) (ap2 g u v) -> Eq y v
  ap2_inj_r h = eqCong ap2_get_arg2 h

  closed_ap1_inv : (f : Fun1) (a : Term) -> Closed (ap1 f a) -> Closed a
  closed_ap1_inv f a c = mkClosed (\ k b ->
    ap1_inj {f = f} (closedAt c k b))

  closed_ap2_inv_l : (g : Fun2) (a b : Term) -> Closed (ap2 g a b) -> Closed a
  closed_ap2_inv_l g a b c = mkClosed (\ k b' ->
    ap2_inj_l {g = g} (closedAt c k b'))

  closed_ap2_inv_r : (g : Fun2) (a b : Term) -> Closed (ap2 g a b) -> Closed b
  closed_ap2_inv_r g a b c = mkClosed (\ k b' ->
    ap2_inj_r {g = g} (closedAt c k b'))

kF1 : Term -> Fun1
kF1 O           = o
kF1 (var _)     = o
kF1 (ap1 f t)   = compose1U f (kF1 t)
kF1 (ap2 g a b) = C g (kF1 a) (kF1 b)

kF1_eq_closed :
  (c : Term) -> Closed c -> (X : Term) ->
  Deriv (eqF (ap1 (kF1 c) X) c)
kF1_eq_closed O cl X = ax_o X
kF1_eq_closed (var k) cl X = emptyElim (closed_var_absurd k cl)
kF1_eq_closed (ap1 f t) cl X =
  ruleTrans (compose1U_eq f (kF1 t) X)
            (cong1 f (kF1_eq_closed t (closed_ap1_inv f t cl) X))
kF1_eq_closed (ap2 g a b) cl X =
  ruleTrans (ax_C g (kF1 a) (kF1 b) X)
    (ruleTrans
      (congL g (ap1 (kF1 b) X) (kF1_eq_closed a (closed_ap2_inv_l g a b cl) X))
      (congR g a (kF1_eq_closed b (closed_ap2_inv_r g a b cl) X)))

------------------------------------------------------------------------
-- Closure of  codeFun1 / codeFun2  (by structural recursion on the
-- Fun1 / Fun2 grammar).

codeFun1_closed : (f : Fun1) -> Closed (codeFun1 f)
codeFun2_closed : (g : Fun2) -> Closed (codeFun2 g)

codeFun1_closed s = closed_natCode tag_s
codeFun1_closed o = closed_natCode tag_o
codeFun1_closed u = closed_natCode tag_u
codeFun1_closed (C g h1 h2) =
  closed_ap2 Pair (natCode tag_C) _
    (closed_natCode tag_C)
    (closed_ap2 Pair (codeFun2 g) _
      (codeFun2_closed g)
      (closed_ap2 Pair (codeFun1 h1) (codeFun1 h2)
        (codeFun1_closed h1) (codeFun1_closed h2)))

codeFun2_closed v = closed_natCode tag_v
codeFun2_closed (R g h1 h2) =
  closed_ap2 Pair (natCode tag_R) _
    (closed_natCode tag_R)
    (closed_ap2 Pair (codeFun1 g) _
      (codeFun1_closed g)
      (closed_ap2 Pair (codeFun2 h1) (codeFun2 h2)
        (codeFun2_closed h1) (codeFun2_closed h2)))

------------------------------------------------------------------------
-- pairF1 -- Fun1 builder for Pair-of-Fun1.  ap1 (pairF1 f g) X
--           =  ap2 Pair (ap1 f X) (ap1 g X).
--
-- The PRIMARY combinator for assembling baseF1 / stepF1.

pairF1 : Fun1 -> Fun1 -> Fun1
pairF1 = C Pair

pairF1_eq :
  (f g : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (pairF1 f g) X) (ap2 Pair (ap1 f X) (ap1 g X)))
pairF1_eq = ax_C Pair

------------------------------------------------------------------------
-- Convenience aliases for closed-Term Fun1 wrappers.

oF1 : Fun1
oF1 = o

oF1_eq : (X : Term) -> Deriv (eqF (ap1 oF1 X) O)
oF1_eq = ax_o

natF1 : Nat -> Fun1
natF1 = constN

natF1_eq : (n : Nat) (X : Term) -> Deriv (eqF (ap1 (natF1 n) X) (natCode n))
natF1_eq = constN_eq

------------------------------------------------------------------------
-- Structural Fun1 wrappers for codeFun1 / codeFun2 :
--   ap1 (codeFun1_F1 f) X =Deriv= codeFun1 f
--   ap1 (codeFun2_F1 g) X =Deriv= codeFun2 g
--
-- These match  codeFun1 / codeFun2 's structural definition so the
-- closure equations are mechanical.

codeFun1_F1 : Fun1 -> Fun1
codeFun2_F1 : Fun2 -> Fun1

codeFun1_F1 s             = natF1 tag_s
codeFun1_F1 o             = natF1 tag_o
codeFun1_F1 u             = natF1 tag_u
codeFun1_F1 (C g h1 h2)   =
  pairF1 (natF1 tag_C)
    (pairF1 (codeFun2_F1 g)
      (pairF1 (codeFun1_F1 h1) (codeFun1_F1 h2)))

codeFun2_F1 v             = natF1 tag_v
codeFun2_F1 (R g h1 h2)   =
  pairF1 (natF1 tag_R)
    (pairF1 (codeFun1_F1 g)
      (pairF1 (codeFun2_F1 h1) (codeFun2_F1 h2)))

codeFun1_F1_eq :
  (f : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (codeFun1_F1 f) X) (codeFun1 f))
codeFun2_F1_eq :
  (g : Fun2) (X : Term) ->
  Deriv (eqF (ap1 (codeFun2_F1 g) X) (codeFun2 g))

codeFun1_F1_eq s             X = natF1_eq tag_s X
codeFun1_F1_eq o             X = natF1_eq tag_o X
codeFun1_F1_eq u             X = natF1_eq tag_u X
codeFun1_F1_eq (C g h1 h2)   X =
  let inner3 :
        Deriv (eqF (ap1 (pairF1 (codeFun1_F1 h1) (codeFun1_F1 h2)) X)
                    (ap2 Pair (codeFun1 h1) (codeFun1 h2)))
      inner3 =
        ruleTrans (pairF1_eq (codeFun1_F1 h1) (codeFun1_F1 h2) X)
          (ruleTrans
            (congL Pair (ap1 (codeFun1_F1 h2) X) (codeFun1_F1_eq h1 X))
            (congR Pair (codeFun1 h1) (codeFun1_F1_eq h2 X)))
      inner2 :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 g) (pairF1 (codeFun1_F1 h1) (codeFun1_F1 h2))) X)
                    (ap2 Pair (codeFun2 g) (ap2 Pair (codeFun1 h1) (codeFun1 h2))))
      inner2 =
        ruleTrans (pairF1_eq (codeFun2_F1 g) (pairF1 (codeFun1_F1 h1) (codeFun1_F1 h2)) X)
          (ruleTrans
            (congL Pair (ap1 (pairF1 (codeFun1_F1 h1) (codeFun1_F1 h2)) X) (codeFun2_F1_eq g X))
            (congR Pair (codeFun2 g) inner3))
  in ruleTrans (pairF1_eq (natF1 tag_C) _ X)
       (ruleTrans
         (congL Pair _ (natF1_eq tag_C X))
         (congR Pair (natCode tag_C) inner2))

codeFun2_F1_eq v             X = natF1_eq tag_v X
codeFun2_F1_eq (R g h1 h2)   X =
  let inner3 :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 h1) (codeFun2_F1 h2)) X)
                    (ap2 Pair (codeFun2 h1) (codeFun2 h2)))
      inner3 =
        ruleTrans (pairF1_eq (codeFun2_F1 h1) (codeFun2_F1 h2) X)
          (ruleTrans
            (congL Pair (ap1 (codeFun2_F1 h2) X) (codeFun2_F1_eq h1 X))
            (congR Pair (codeFun2 h1) (codeFun2_F1_eq h2 X)))
      inner2 :
        Deriv (eqF (ap1 (pairF1 (codeFun1_F1 g) (pairF1 (codeFun2_F1 h1) (codeFun2_F1 h2))) X)
                    (ap2 Pair (codeFun1 g) (ap2 Pair (codeFun2 h1) (codeFun2 h2))))
      inner2 =
        ruleTrans (pairF1_eq (codeFun1_F1 g) (pairF1 (codeFun2_F1 h1) (codeFun2_F1 h2)) X)
          (ruleTrans
            (congL Pair (ap1 (pairF1 (codeFun2_F1 h1) (codeFun2_F1 h2)) X) (codeFun1_F1_eq g X))
            (congR Pair (codeFun1 g) inner3))
  in ruleTrans (pairF1_eq (natF1 tag_R) _ X)
       (ruleTrans
         (congL Pair _ (natF1_eq tag_R X))
         (congR Pair (natCode tag_R) inner2))

------------------------------------------------------------------------
-- L1_F1 / L2_F1 / L3_F1 -- Fun1 wrappers for the three Term positions
-- appearing in  Df_R_at_O .  Each parameterised on Fun1 / Fun2
-- arguments g , h1 , h2 .

L1_F1 : Fun1 -> Fun2 -> Fun2 -> Fun1
L1_F1 g h1 h2 =
  pairF1 (natF1 tag_ap2)
    (pairF1 (codeFun2_F1 (R g h1 h2))
      (pairF1 num oF1))

L2_F1 : Fun1 -> Fun1
L2_F1 g = pairF1 (natF1 tag_ap1) (pairF1 (codeFun1_F1 g) num)

-- L3_at g X = ap1 num (ap1 g X) = ap1 (compose1U num g) X.
L3_F1 : Fun1 -> Fun1
L3_F1 g = compose1U num g

L1_F1_eq :
  (g : Fun1) (h1 h2 : Fun2) (X : Term) ->
  Deriv (eqF (ap1 (L1_F1 g h1 h2) X)
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair (codeFun2 (R g h1 h2))
                  (ap2 Pair (ap1 num X) O))))
L1_F1_eq g h1 h2 X =
  let inner3 :
        Deriv (eqF (ap1 (pairF1 num oF1) X) (ap2 Pair (ap1 num X) O))
      inner3 =
        ruleTrans (pairF1_eq num oF1 X)
          (congR Pair (ap1 num X) (oF1_eq X))
      inner2 :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 (R g h1 h2)) (pairF1 num oF1)) X)
                    (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) O)))
      inner2 =
        ruleTrans (pairF1_eq (codeFun2_F1 (R g h1 h2)) (pairF1 num oF1) X)
          (ruleTrans
            (congL Pair (ap1 (pairF1 num oF1) X) (codeFun2_F1_eq (R g h1 h2) X))
            (congR Pair (codeFun2 (R g h1 h2)) inner3))
  in ruleTrans (pairF1_eq (natF1 tag_ap2) _ X)
       (ruleTrans
         (congL Pair _ (natF1_eq tag_ap2 X))
         (congR Pair (natCode tag_ap2) inner2))

L2_F1_eq :
  (g : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (L2_F1 g) X)
              (ap2 Pair (natCode tag_ap1)
                (ap2 Pair (codeFun1 g) (ap1 num X))))
L2_F1_eq g X =
  let inner :
        Deriv (eqF (ap1 (pairF1 (codeFun1_F1 g) num) X)
                    (ap2 Pair (codeFun1 g) (ap1 num X)))
      inner =
        ruleTrans (pairF1_eq (codeFun1_F1 g) num X)
          (congL Pair (ap1 num X) (codeFun1_F1_eq g X))
  in ruleTrans (pairF1_eq (natF1 tag_ap1) _ X)
       (ruleTrans
         (congL Pair _ (natF1_eq tag_ap1 X))
         (congR Pair (natCode tag_ap1) inner))

L3_F1_eq :
  (g : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (L3_F1 g) X) (ap1 num (ap1 g X)))
L3_F1_eq g X = compose1U_eq num g X

------------------------------------------------------------------------
-- Closure of  codeTerm / codeFormula  (used below for proving closure
-- of z_axRefl_v0 etc.).
--
-- codeTerm produces a Closed Term for ANY input Term : it replaces all
--  var  positions with  natCode  leaves.

codeTerm_closed : (t : Term) -> Closed (codeTerm t)
codeTerm_closed O = closed_O
codeTerm_closed (var k) =
  closed_ap2 Pair (natCode tag_var) (natCode k)
    (closed_natCode tag_var) (closed_natCode k)
codeTerm_closed (ap1 f t) =
  closed_ap2 Pair (natCode tag_ap1) _
    (closed_natCode tag_ap1)
    (closed_ap2 Pair (codeFun1 f) (codeTerm t)
      (codeFun1_closed f) (codeTerm_closed t))
codeTerm_closed (ap2 g a b) =
  closed_ap2 Pair (natCode tag_ap2) _
    (closed_natCode tag_ap2)
    (closed_ap2 Pair (codeFun2 g) _
      (codeFun2_closed g)
      (closed_ap2 Pair (codeTerm a) (codeTerm b)
        (codeTerm_closed a) (codeTerm_closed b)))

------------------------------------------------------------------------
-- Closure of z_axRefl_v0 (built from natCode + codeTerm + ap2 Pair).

open import BRA4.Thm12.EncodedReflVar0
  using ( z_axRefl_v0 ; z_axU_v0 ; packAx2_O ; packAx4_O
        ; layer1_code ; layer2_code ; layer3_code ; layer4_code ; layer5_code
        ; inner_mp_code ; outer_mp_code )

private
  closed_packAx2_O : Closed packAx2_O
  closed_packAx2_O =
    closed_ap2 Pair _ _ (closed_natCode tag_ax)
      (closed_ap2 Pair _ _ (closed_natCode (suc (suc zero))) closed_O)

  closed_packAx4_O : Closed packAx4_O
  closed_packAx4_O =
    closed_ap2 Pair _ _ (closed_natCode tag_ax)
      (closed_ap2 Pair _ _ (closed_natCode (suc (suc (suc (suc zero))))) closed_O)

  closed_z_axU_v0 : Closed z_axU_v0
  closed_z_axU_v0 =
    closed_ap2 Pair _ _ (closed_natCode tag_sb)
      (closed_ap2 Pair _ _
        (closed_ap2 Pair _ _ (closed_natCode zero)
          (codeTerm_closed (var zero)))
        closed_packAx2_O)

  closed_layer1_code : Closed layer1_code
  closed_layer1_code =
    closed_ap2 Pair _ _ (closed_natCode tag_sb)
      (closed_ap2 Pair _ _
        (closed_ap2 Pair _ _ (closed_natCode (suc zero))
          (codeTerm_closed (var (suc (suc (suc zero))))))
        closed_packAx4_O)

  closed_layer2_code : Closed layer2_code
  closed_layer2_code =
    closed_ap2 Pair _ _ (closed_natCode tag_sb)
      (closed_ap2 Pair _ _
        (closed_ap2 Pair _ _ (closed_natCode (suc (suc zero)))
          (codeTerm_closed (var (suc (suc (suc (suc zero)))))))
        closed_layer1_code)

  closed_layer3_code : Closed layer3_code
  closed_layer3_code =
    closed_ap2 Pair _ _ (closed_natCode tag_sb)
      (closed_ap2 Pair _ _
        (closed_ap2 Pair _ _ (closed_natCode zero)
          (codeTerm_closed (ap1 u (var zero))))
        closed_layer2_code)

  closed_layer4_code : Closed layer4_code
  closed_layer4_code =
    closed_ap2 Pair _ _ (closed_natCode tag_sb)
      (closed_ap2 Pair _ _
        (closed_ap2 Pair _ _ (closed_natCode (suc (suc (suc zero))))
          (codeTerm_closed (var zero)))
        closed_layer3_code)

  closed_layer5_code : Closed layer5_code
  closed_layer5_code =
    closed_ap2 Pair _ _ (closed_natCode tag_sb)
      (closed_ap2 Pair _ _
        (closed_ap2 Pair _ _ (closed_natCode (suc (suc (suc (suc zero)))))
          (codeTerm_closed (var zero)))
        closed_layer4_code)

  closed_inner_mp_code : Closed inner_mp_code
  closed_inner_mp_code =
    closed_ap2 Pair _ _ (closed_natCode tag_mp)
      (closed_ap2 Pair _ _ closed_layer5_code closed_z_axU_v0)

  closed_outer_mp_code : Closed outer_mp_code
  closed_outer_mp_code =
    closed_ap2 Pair _ _ (closed_natCode tag_mp)
      (closed_ap2 Pair _ _ closed_inner_mp_code closed_z_axU_v0)

closed_z_axRefl_v0 : Closed z_axRefl_v0
closed_z_axRefl_v0 = closed_outer_mp_code

------------------------------------------------------------------------
-- packAx4_F1 -- Fun1 producing the closed packAx4 leaf.
--   ap1 packAx4_F1 X =Deriv= packAx4_O   ( = packAx4 inside Df_axEqTrans )

packAx4_F1 : Fun1
packAx4_F1 = kF1 packAx4_O

packAx4_F1_eq : (X : Term) -> Deriv (eqF (ap1 packAx4_F1 X) packAx4_O)
packAx4_F1_eq X = kF1_eq_closed packAx4_O closed_packAx2_O' X
  where
  -- packAx4_O has same shape as packAx2_O but with N4 instead of N2 ;
  -- reuse closed_ap2 + closed_natCode + closed_O.
  closed_packAx2_O' : Closed packAx4_O
  closed_packAx2_O' = closed_packAx4_O

------------------------------------------------------------------------
-- Single-variable sb-layer Fun1 builder (for the NESTED-sb encodings).
--
--   specPairF1 k vF        : ap1 (..) p = Pair (natCode k) (ap1 vF p)
--   sbLayerF1 k vF inF     : ap1 (..) p = Pair tag_sb (Pair (Pair (natCode k) (ap1 vF p)) (ap1 inF p))
--
-- Composing these  n  times builds the  n-fold nested  tag_sb  wrap that
-- replaced the old  tag_sb2 / tag_sb3  wraps.

specPairF1 : Nat -> Fun1 -> Fun1
specPairF1 k vF = pairF1 (natF1 k) vF

specPairF1_eq :
  (k : Nat) (vF : Fun1) (vT : Term) (p : Term) ->
  Deriv (eqF (ap1 vF p) vT) ->
  Deriv (eqF (ap1 (specPairF1 k vF) p) (ap2 Pair (natCode k) vT))
specPairF1_eq k vF vT p e_v =
  ruleTrans (pairF1_eq (natF1 k) vF p)
    (ruleTrans (congL Pair (ap1 vF p) (natF1_eq k p))
               (congR Pair (natCode k) e_v))

sbLayerF1 : Nat -> Fun1 -> Fun1 -> Fun1
sbLayerF1 k vF inF = pairF1 (natF1 tag_sb) (pairF1 (specPairF1 k vF) inF)

sbLayerF1_eq :
  (k : Nat) (vF inF : Fun1) (vT innerT : Term) (p : Term) ->
  Deriv (eqF (ap1 vF p) vT) ->
  Deriv (eqF (ap1 inF p) innerT) ->
  Deriv (eqF (ap1 (sbLayerF1 k vF inF) p)
              (ap2 Pair (natCode tag_sb)
                (ap2 Pair (ap2 Pair (natCode k) vT) innerT)))
sbLayerF1_eq k vF inF vT innerT p e_v e_inner =
  let e_mid :
        Deriv (eqF (ap1 (pairF1 (specPairF1 k vF) inF) p)
                    (ap2 Pair (ap2 Pair (natCode k) vT) innerT))
      e_mid =
        ruleTrans (pairF1_eq (specPairF1 k vF) inF p)
          (ruleTrans (congL Pair (ap1 inF p) (specPairF1_eq k vF vT p e_v))
                     (congR Pair (ap2 Pair (natCode k) vT) e_inner))
  in ruleTrans (pairF1_eq (natF1 tag_sb) (pairF1 (specPairF1 k vF) inF) p)
       (ruleTrans (congL Pair (ap1 (pairF1 (specPairF1 k vF) inF) p)
                              (natF1_eq tag_sb p))
                  (congR Pair (natCode tag_sb) e_mid))

------------------------------------------------------------------------
-- axEqTrans_F1 -- Fun1 producing  Df_axEqTrans (ap1 tA_F1 X) (ap1 tB_F1 X) (ap1 tC_F1 X) .
-- (Three nested  tag_sb  layers ; var 0 := tA, var 1 := tB, var 2 := tC.)

axEqTrans_F1 : Fun1 -> Fun1 -> Fun1 -> Fun1
axEqTrans_F1 tA_F1 tB_F1 tC_F1 =
  sbLayerF1 zero tA_F1
    (sbLayerF1 (suc zero) tB_F1
      (sbLayerF1 (suc (suc zero)) tC_F1 packAx4_F1))

axEqTrans_F1_eq :
  (tA_F1 tB_F1 tC_F1 : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (axEqTrans_F1 tA_F1 tB_F1 tC_F1) X)
              (Df_axEqTrans (ap1 tA_F1 X) (ap1 tB_F1 X) (ap1 tC_F1 X)))
axEqTrans_F1_eq tA_F1 tB_F1 tC_F1 X =
  let i2 : Fun1
      i2 = sbLayerF1 (suc (suc zero)) tC_F1 packAx4_F1
      i1 : Fun1
      i1 = sbLayerF1 (suc zero) tB_F1 i2

      e2 = sbLayerF1_eq (suc (suc zero)) tC_F1 packAx4_F1
             (ap1 tC_F1 X) packAx4_O X
             (axRefl (ap1 tC_F1 X)) (packAx4_F1_eq X)
      e1 = sbLayerF1_eq (suc zero) tB_F1 i2
             (ap1 tB_F1 X) _ X
             (axRefl (ap1 tB_F1 X)) e2
      e0 = sbLayerF1_eq zero tA_F1 i1
             (ap1 tA_F1 X) _ X
             (axRefl (ap1 tA_F1 X)) e1
  in e0

------------------------------------------------------------------------
-- z_axRefl_v0_F1 -- Fun1 producing z_axRefl_v0 (closed).

z_axRefl_v0_F1 : Fun1
z_axRefl_v0_F1 = kF1 z_axRefl_v0

z_axRefl_v0_F1_eq :
  (X : Term) -> Deriv (eqF (ap1 z_axRefl_v0_F1 X) z_axRefl_v0)
z_axRefl_v0_F1_eq X = kF1_eq_closed z_axRefl_v0 closed_z_axRefl_v0 X

------------------------------------------------------------------------
-- refl_meta_F1 -- Fun1 wrapping Df_refl_meta around a parametric Y_F1.

refl_meta_F1 : Fun1 -> Fun1
refl_meta_F1 Y_F1 =
  pairF1 (natF1 tag_sb)
    (pairF1 (pairF1 (natF1 zero) Y_F1) z_axRefl_v0_F1)

refl_meta_F1_eq :
  (Y_F1 : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (refl_meta_F1 Y_F1) X) (Df_refl_meta (ap1 Y_F1 X)))
refl_meta_F1_eq Y_F1 X =
  let Y = ap1 Y_F1 X
      inner_kY :
        Deriv (eqF (ap1 (pairF1 (natF1 zero) Y_F1) X)
                    (ap2 Pair (natCode zero) Y))
      inner_kY =
        ruleTrans (pairF1_eq (natF1 zero) Y_F1 X)
          (congL Pair Y (natF1_eq zero X))
      mid_eq :
        Deriv (eqF (ap1 (pairF1 (pairF1 (natF1 zero) Y_F1) z_axRefl_v0_F1) X)
                    (ap2 Pair (ap2 Pair (natCode zero) Y) z_axRefl_v0))
      mid_eq =
        ruleTrans (pairF1_eq (pairF1 (natF1 zero) Y_F1) z_axRefl_v0_F1 X)
          (ruleTrans
            (congL Pair (ap1 z_axRefl_v0_F1 X) inner_kY)
            (congR Pair (ap2 Pair (natCode zero) Y) (z_axRefl_v0_F1_eq X)))
  in ruleTrans (pairF1_eq (natF1 tag_sb) _ X)
       (ruleTrans
         (congL Pair _ (natF1_eq tag_sb X))
         (congR Pair _ mid_eq))

------------------------------------------------------------------------
-- mpWrapF1 -- Fun1 builder for an encoded-mp wrap.
--   ap1 (mpWrapF1 f g) X =Deriv= Pair tag_mp (Pair (ap1 f X) (ap1 g X))

mpWrapF1 : Fun1 -> Fun1 -> Fun1
mpWrapF1 f g = pairF1 (natF1 tag_mp) (pairF1 f g)

mpWrapF1_eq :
  (f g : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (mpWrapF1 f g) X)
              (ap2 Pair (natCode tag_mp) (ap2 Pair (ap1 f X) (ap1 g X))))
mpWrapF1_eq f g X =
  ruleTrans (pairF1_eq (natF1 tag_mp) (pairF1 f g) X)
    (ruleTrans
      (congL Pair _ (natF1_eq tag_mp X))
      (congR Pair (natCode tag_mp) (pairF1_eq f g X)))

------------------------------------------------------------------------
-- baseF1 : the Fun1 producing  Df_R_at_O g h1 h2 (\ X -> Df_g_F1 X) X .
--
-- Structure (left-aligned) :
--
--   baseF1 X =
--     mpWrap                                            -- outer Df_eqTrans
--       ( mpWrap                                        -- inner Df_eqTrans body
--         ( Df_axEqTrans L2 L1 L3 )
--         ( eqSym ) )
--       ( Df_g_F1 X )
--   where
--     eqSym = mpWrap                                     -- outer Df_eqSym
--       ( mpWrap                                          -- inner Df_eqSym body
--         ( Df_axEqTrans L1 L2 L1 )
--         ( Df_axRBase X ) )
--       ( Df_refl_meta L1 )

baseF1 :
  (g : Fun1) (h1 h2 : Fun2) (Df_g_F1 : Fun1) -> Fun1
baseF1 g h1 h2 Df_g_F1 =
  let
    L1F = L1_F1 g h1 h2
    L2F = L2_F1 g
    L3F = L3_F1 g

    eqSymF1 : Fun1
    eqSymF1 =
      mpWrapF1
        (mpWrapF1 (axEqTrans_F1 L1F L2F L1F) (Df_axRBase g h1 h2))
        (refl_meta_F1 L1F)

    eqTransBodyF1 : Fun1
    eqTransBodyF1 =
      mpWrapF1 (axEqTrans_F1 L2F L1F L3F) eqSymF1
  in mpWrapF1 eqTransBodyF1 Df_g_F1

------------------------------------------------------------------------
-- sbLayer_cong -- Term-level congruence for ONE nested  tag_sb  layer.
--
--   Pair tag_sb (Pair (Pair (natCode k) v) inner)
--     vs    ... v' ... inner' .

sbLayer_cong :
  (k : Nat) (vt vt' inner inner' : Term) ->
  Deriv (eqF vt vt') ->
  Deriv (eqF inner inner') ->
  Deriv (eqF (ap2 Pair (natCode tag_sb)
               (ap2 Pair (ap2 Pair (natCode k) vt) inner))
              (ap2 Pair (natCode tag_sb)
                (ap2 Pair (ap2 Pair (natCode k) vt') inner')))
sbLayer_cong k vt vt' inner inner' ev einner =
  congR Pair (natCode tag_sb)
    (ruleTrans (congL Pair inner (congR Pair (natCode k) ev))
               (congR Pair (ap2 Pair (natCode k) vt') einner))

------------------------------------------------------------------------
-- 3-arg congruence for  Df_axEqTrans  on its three Term slots (nested sb).

Df_axEqTrans_cong :
  (tA tA' tB tB' tC tC' : Term) ->
  Deriv (eqF tA tA') ->
  Deriv (eqF tB tB') ->
  Deriv (eqF tC tC') ->
  Deriv (eqF (Df_axEqTrans tA tB tC) (Df_axEqTrans tA' tB' tC'))
Df_axEqTrans_cong tA tA' tB tB' tC tC' eA eB eC =
  sbLayer_cong zero tA tA' _ _ eA
    (sbLayer_cong (suc zero) tB tB' _ _ eB
      (sbLayer_cong (suc (suc zero)) tC tC' packAx4_O packAx4_O eC
        (axRefl packAx4_O)))

------------------------------------------------------------------------
-- 1-arg congruence for  Df_refl_meta  on its Term slot.

Df_refl_meta_cong :
  (Y Y' : Term) ->
  Deriv (eqF Y Y') ->
  Deriv (eqF (Df_refl_meta Y) (Df_refl_meta Y'))
Df_refl_meta_cong Y Y' eY =
  let
    pair_kY : Deriv (eqF (ap2 Pair (natCode zero) Y)
                          (ap2 Pair (natCode zero) Y'))
    pair_kY = congR Pair (natCode zero) eY

    pair_kY_refl :
      Deriv (eqF (ap2 Pair (ap2 Pair (natCode zero) Y) z_axRefl_v0)
                  (ap2 Pair (ap2 Pair (natCode zero) Y') z_axRefl_v0))
    pair_kY_refl = congL Pair z_axRefl_v0 pair_kY
  in congR Pair (natCode tag_sb) pair_kY_refl

------------------------------------------------------------------------
-- baseF1_eq -- the main closure equation.

baseF1_eq :
  (g : Fun1) (h1 h2 : Fun2) (Df_g_F1 : Fun1) (X : Term) ->
  Deriv (eqF (ap1 (baseF1 g h1 h2 Df_g_F1) X)
              (Df_R_at_O g h1 h2 (\ X' -> ap1 Df_g_F1 X') X))
baseF1_eq g h1 h2 Df_g_F1 X =
  let
    L1F = L1_F1 g h1 h2
    L2F = L2_F1 g
    L3F = L3_F1 g

    eqSymF1 : Fun1
    eqSymF1 =
      mpWrapF1
        (mpWrapF1 (axEqTrans_F1 L1F L2F L1F) (Df_axRBase g h1 h2))
        (refl_meta_F1 L1F)

    eqTransBodyF1 : Fun1
    eqTransBodyF1 =
      mpWrapF1 (axEqTrans_F1 L2F L1F L3F) eqSymF1

    L1X : Term
    L1X = ap1 L1F X

    L2X : Term
    L2X = ap1 L2F X

    L3X : Term
    L3X = ap1 L3F X

    rB_X : Term
    rB_X = ap1 (Df_axRBase g h1 h2) X

    gX : Term
    gX = ap1 Df_g_F1 X

    -- Step 1: ap1 (axEqTrans_F1 L1F L2F L1F) X = Df_axEqTrans L1X L2X L1X
    aET_inner_eq :
      Deriv (eqF (ap1 (axEqTrans_F1 L1F L2F L1F) X) (Df_axEqTrans L1X L2X L1X))
    aET_inner_eq = axEqTrans_F1_eq L1F L2F L1F X

    -- Step 2: ap1 (mpWrapF1 (axEqTrans_F1 L1F L2F L1F) (Df_axRBase g h1 h2)) X
    --         = Pair tag_mp (Pair (Df_axEqTrans L1X L2X L1X) rB_X)
    inner_mp_eq :
      Deriv (eqF (ap1 (mpWrapF1 (axEqTrans_F1 L1F L2F L1F) (Df_axRBase g h1 h2)) X)
                  (ap2 Pair (natCode tag_mp)
                    (ap2 Pair (Df_axEqTrans L1X L2X L1X) rB_X)))
    inner_mp_eq =
      ruleTrans (mpWrapF1_eq (axEqTrans_F1 L1F L2F L1F) (Df_axRBase g h1 h2) X)
        (congR Pair (natCode tag_mp)
          (congL Pair rB_X aET_inner_eq))

    -- Step 3: ap1 (refl_meta_F1 L1F) X = Df_refl_meta L1X
    refl_eq :
      Deriv (eqF (ap1 (refl_meta_F1 L1F) X) (Df_refl_meta L1X))
    refl_eq = refl_meta_F1_eq L1F X

    -- Step 4: ap1 eqSymF1 X = Pair tag_mp (Pair (Pair tag_mp (Pair (Df_axEqTrans L1 L2 L1) rB_X)) (Df_refl_meta L1))
    eqSym_X_target : Term
    eqSym_X_target =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans L1X L2X L1X) rB_X))
          (Df_refl_meta L1X))

    eqSym_eq : Deriv (eqF (ap1 eqSymF1 X) eqSym_X_target)
    eqSym_eq =
      ruleTrans (mpWrapF1_eq (mpWrapF1 (axEqTrans_F1 L1F L2F L1F) (Df_axRBase g h1 h2)) (refl_meta_F1 L1F) X)
        (congR Pair (natCode tag_mp)
          (ruleTrans (congL Pair (ap1 (refl_meta_F1 L1F) X) inner_mp_eq)
                     (congR Pair _ refl_eq)))

    -- Step 5: ap1 (axEqTrans_F1 L2F L1F L3F) X = Df_axEqTrans L2X L1X L3X
    aET_outer_eq :
      Deriv (eqF (ap1 (axEqTrans_F1 L2F L1F L3F) X) (Df_axEqTrans L2X L1X L3X))
    aET_outer_eq = axEqTrans_F1_eq L2F L1F L3F X

    -- Step 6: ap1 eqTransBodyF1 X = Pair tag_mp (Pair (Df_axEqTrans L2 L1 L3) eqSym_X_target)
    eqTransBody_target : Term
    eqTransBody_target =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans L2X L1X L3X) eqSym_X_target)

    eqTransBody_eq : Deriv (eqF (ap1 eqTransBodyF1 X) eqTransBody_target)
    eqTransBody_eq =
      ruleTrans (mpWrapF1_eq (axEqTrans_F1 L2F L1F L3F) eqSymF1 X)
        (congR Pair (natCode tag_mp)
          (ruleTrans (congL Pair (ap1 eqSymF1 X) aET_outer_eq)
                     (congR Pair _ eqSym_eq)))

    -- Step 7: ap1 baseF1 X = Pair tag_mp (Pair eqTransBody_target gX)
    --                       = Df_R_at_O ... X via unfolding (which Agda will verify).
    final_eq :
      Deriv (eqF (ap1 (baseF1 g h1 h2 Df_g_F1) X)
                  (ap2 Pair (natCode tag_mp)
                    (ap2 Pair eqTransBody_target gX)))
    final_eq =
      ruleTrans (mpWrapF1_eq eqTransBodyF1 Df_g_F1 X)
        (congR Pair (natCode tag_mp)
          (congL Pair gX eqTransBody_eq))

    -- Bridge to (L1X, L2X, L3X) using L1_F1_eq / L2_F1_eq / L3_F1_eq.
    L1_bridge : Deriv (eqF L1X
                            (ap2 Pair (natCode tag_ap2)
                              (ap2 Pair (codeFun2 (R g h1 h2))
                                (ap2 Pair (ap1 num X) O))))
    L1_bridge = L1_F1_eq g h1 h2 X

    L2_bridge : Deriv (eqF L2X
                            (ap2 Pair (natCode tag_ap1)
                              (ap2 Pair (codeFun1 g) (ap1 num X))))
    L2_bridge = L2_F1_eq g X

    L3_bridge : Deriv (eqF L3X (ap1 num (ap1 g X)))
    L3_bridge = L3_F1_eq g X

    -- Now bridge LiX -> Li_at_unfolded via Li_F1_eq.

    L1' : Term
    L1' = ap2 Pair (natCode tag_ap2)
            (ap2 Pair (codeFun2 (R g h1 h2))
              (ap2 Pair (ap1 num X) O))

    L2' : Term
    L2' = ap2 Pair (natCode tag_ap1)
            (ap2 Pair (codeFun1 g) (ap1 num X))

    L3' : Term
    L3' = ap1 num (ap1 g X)

    e1 : Deriv (eqF L1X L1')
    e1 = L1_F1_eq g h1 h2 X

    e2 : Deriv (eqF L2X L2')
    e2 = L2_F1_eq g X

    e3 : Deriv (eqF L3X L3')
    e3 = L3_F1_eq g X

    aET_outer_bridge :
      Deriv (eqF (Df_axEqTrans L2X L1X L3X) (Df_axEqTrans L2' L1' L3'))
    aET_outer_bridge = Df_axEqTrans_cong L2X L2' L1X L1' L3X L3' e2 e1 e3

    aET_inner_bridge :
      Deriv (eqF (Df_axEqTrans L1X L2X L1X) (Df_axEqTrans L1' L2' L1'))
    aET_inner_bridge = Df_axEqTrans_cong L1X L1' L2X L2' L1X L1' e1 e2 e1

    refl_bridge :
      Deriv (eqF (Df_refl_meta L1X) (Df_refl_meta L1'))
    refl_bridge = Df_refl_meta_cong L1X L1' e1

    -- eqSym_X_target target -> using L*' targets.
    eqSym_X_target' : Term
    eqSym_X_target' =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair
          (ap2 Pair (natCode tag_mp)
            (ap2 Pair (Df_axEqTrans L1' L2' L1') rB_X))
          (Df_refl_meta L1'))

    -- Bridge eqSym_X_target -> eqSym_X_target' via congs.
    eqSym_inner_step :
      Deriv (eqF (ap2 Pair (Df_axEqTrans L1X L2X L1X) rB_X)
                  (ap2 Pair (Df_axEqTrans L1' L2' L1') rB_X))
    eqSym_inner_step = congL Pair rB_X aET_inner_bridge

    eqSym_inner_mp :
      Deriv (eqF (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans L1X L2X L1X) rB_X))
                  (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans L1' L2' L1') rB_X)))
    eqSym_inner_mp = congR Pair (natCode tag_mp) eqSym_inner_step

    eqSym_pair_part :
      Deriv (eqF
        (ap2 Pair
          (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans L1X L2X L1X) rB_X))
          (Df_refl_meta L1X))
        (ap2 Pair
          (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans L1' L2' L1') rB_X))
          (Df_refl_meta L1')))
    eqSym_pair_part =
      ruleTrans (congL Pair (Df_refl_meta L1X) eqSym_inner_mp)
                (congR Pair _ refl_bridge)

    eqSym_bridge : Deriv (eqF eqSym_X_target eqSym_X_target')
    eqSym_bridge = congR Pair (natCode tag_mp) eqSym_pair_part

    -- eqTransBody_target -> eqTransBody_target' (using L*' and eqSym_X_target').
    eqTransBody_target' : Term
    eqTransBody_target' =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans L2' L1' L3') eqSym_X_target')

    eqTransBody_inner :
      Deriv (eqF (ap2 Pair (Df_axEqTrans L2X L1X L3X) eqSym_X_target)
                  (ap2 Pair (Df_axEqTrans L2' L1' L3') eqSym_X_target'))
    eqTransBody_inner =
      ruleTrans (congL Pair eqSym_X_target aET_outer_bridge)
                (congR Pair _ eqSym_bridge)

    eqTransBody_bridge : Deriv (eqF eqTransBody_target eqTransBody_target')
    eqTransBody_bridge = congR Pair (natCode tag_mp) eqTransBody_inner

    -- Final assembly : bridge final_eq's RHS to Df_R_at_O.
    target' : Term
    target' = ap2 Pair (natCode tag_mp) (ap2 Pair eqTransBody_target' gX)

    final_bridge :
      Deriv (eqF (ap2 Pair (natCode tag_mp) (ap2 Pair eqTransBody_target gX))
                  target')
    final_bridge =
      congR Pair (natCode tag_mp) (congL Pair gX eqTransBody_bridge)

  in ruleTrans final_eq final_bridge

------------------------------------------------------------------------
-- Extractor Fun1's for  p = Pair (Pair X Y) prev .
--
--   extract_X p   = Fst (Fst p) = X
--   extract_Y p   = Snd (Fst p) = Y
--   extract_prev p = Snd p      = prev
--
-- All universal in arbitrary X , Y , prev .

extract_X_F1 : Fun1
extract_X_F1 = compose1U Fst Fst

extract_Y_F1 : Fun1
extract_Y_F1 = compose1U Snd Fst

extract_prev_F1 : Fun1
extract_prev_F1 = Snd

extract_X_at :
  (X Y prev : Term) ->
  Deriv (eqF (ap1 extract_X_F1 (ap2 Pair (ap2 Pair X Y) prev)) X)
extract_X_at X Y prev =
  let p = ap2 Pair (ap2 Pair X Y) prev
      e1 : Deriv (eqF (ap1 (compose1U Fst Fst) p) (ap1 Fst (ap1 Fst p)))
      e1 = compose1U_eq Fst Fst p
      e_inner : Deriv (eqF (ap1 Fst p) (ap2 Pair X Y))
      e_inner = axFst (ap2 Pair X Y) prev
      e_outer : Deriv (eqF (ap1 Fst (ap1 Fst p)) X)
      e_outer =
        ruleTrans (cong1 Fst e_inner) (axFst X Y)
  in ruleTrans e1 e_outer

extract_Y_at :
  (X Y prev : Term) ->
  Deriv (eqF (ap1 extract_Y_F1 (ap2 Pair (ap2 Pair X Y) prev)) Y)
extract_Y_at X Y prev =
  let p = ap2 Pair (ap2 Pair X Y) prev
      e1 : Deriv (eqF (ap1 (compose1U Snd Fst) p) (ap1 Snd (ap1 Fst p)))
      e1 = compose1U_eq Snd Fst p
      e_inner : Deriv (eqF (ap1 Fst p) (ap2 Pair X Y))
      e_inner = axFst (ap2 Pair X Y) prev
      e_outer : Deriv (eqF (ap1 Snd (ap1 Fst p)) Y)
      e_outer =
        ruleTrans (cong1 Snd e_inner) (axSnd X Y)
  in ruleTrans e1 e_outer

extract_prev_at :
  (X Y prev : Term) ->
  Deriv (eqF (ap1 extract_prev_F1 (ap2 Pair (ap2 Pair X Y) prev)) prev)
extract_prev_at X Y prev = axSnd (ap2 Pair X Y) prev

------------------------------------------------------------------------
-- Phase 1B Step 1 -- Fun1 wrappers for sb2 / sb3 axiom-wraps.
--
-- We build Df_axRStep_F1 (sb2-wrap of axN10), Df_axEqCongL_F1 (sb3-wrap
-- of axN6), and Df_axEqCongR_F1 (sb3-wrap of axN7).  Each is a Fun1
-- producing the matching Df_ax* Term when supplied with X_F1 / Y_F1 /
-- tA_F1 / tB_F1 / tC_F1 Fun1's.
--
-- packAxN_* leaves are CLOSED (depend only on Fun1/Fun2 indices), so we
-- wrap them via kF1.

------------------------------------------------------------------------
-- spec2_F1 -- Fun1 builder for spec2_at .
--
-- spec2_at X Y  =  Pair (Pair 0 (num X)) (Pair 1 (num Y)) .
-- spec2_F1 X_F1 Y_F1  applied to p  gives  spec2_at (X_F1 p) (Y_F1 p).

private
  spec2_F1 : Fun1 -> Fun1 -> Fun1
  spec2_F1 X_F1 Y_F1 =
    pairF1 (pairF1 (natF1 zero) (compose1U num X_F1))
      (pairF1 (natF1 (suc zero)) (compose1U num Y_F1))

  spec2_F1_eq :
    (X_F1 Y_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (spec2_F1 X_F1 Y_F1) p)
                (ap2 Pair (ap2 Pair (natCode zero) (ap1 num (ap1 X_F1 p)))
                          (ap2 Pair (natCode (suc zero)) (ap1 num (ap1 Y_F1 p)))))
  spec2_F1_eq X_F1 Y_F1 p =
    let numX = ap1 num (ap1 X_F1 p)
        numY = ap1 num (ap1 Y_F1 p)

        e_numX : Deriv (eqF (ap1 (compose1U num X_F1) p) numX)
        e_numX = compose1U_eq num X_F1 p

        e_numY : Deriv (eqF (ap1 (compose1U num Y_F1) p) numY)
        e_numY = compose1U_eq num Y_F1 p

        e_left :
          Deriv (eqF (ap1 (pairF1 (natF1 zero) (compose1U num X_F1)) p)
                      (ap2 Pair (natCode zero) numX))
        e_left =
          ruleTrans (pairF1_eq (natF1 zero) (compose1U num X_F1) p)
            (ruleTrans (congL Pair (ap1 (compose1U num X_F1) p) (natF1_eq zero p))
                       (congR Pair (natCode zero) e_numX))

        e_right :
          Deriv (eqF (ap1 (pairF1 (natF1 (suc zero)) (compose1U num Y_F1)) p)
                      (ap2 Pair (natCode (suc zero)) numY))
        e_right =
          ruleTrans (pairF1_eq (natF1 (suc zero)) (compose1U num Y_F1) p)
            (ruleTrans (congL Pair (ap1 (compose1U num Y_F1) p) (natF1_eq (suc zero) p))
                       (congR Pair (natCode (suc zero)) e_numY))

    in ruleTrans (pairF1_eq (pairF1 (natF1 zero) (compose1U num X_F1)) _ p)
         (ruleTrans (congL Pair _ e_left)
                    (congR Pair _ e_right))

------------------------------------------------------------------------
-- spec3_F1 -- Fun1 builder for the sb3 spec
--
-- spec3T 0 1 2 tA tB tC = Pair (Pair 0 tA) (Pair (Pair 1 tB) (Pair 2 tC)) .

private
  spec3_F1 : Fun1 -> Fun1 -> Fun1 -> Fun1
  spec3_F1 tA_F1 tB_F1 tC_F1 =
    pairF1 (pairF1 (natF1 zero) tA_F1)
      (pairF1 (pairF1 (natF1 (suc zero)) tB_F1)
        (pairF1 (natF1 (suc (suc zero))) tC_F1))

  spec3_F1_eq :
    (tA_F1 tB_F1 tC_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (spec3_F1 tA_F1 tB_F1 tC_F1) p)
                (ap2 Pair (ap2 Pair (natCode zero) (ap1 tA_F1 p))
                  (ap2 Pair (ap2 Pair (natCode (suc zero)) (ap1 tB_F1 p))
                            (ap2 Pair (natCode (suc (suc zero))) (ap1 tC_F1 p)))))
  spec3_F1_eq tA_F1 tB_F1 tC_F1 p =
    let tA = ap1 tA_F1 p
        tB = ap1 tB_F1 p
        tC = ap1 tC_F1 p

        e_kA :
          Deriv (eqF (ap1 (pairF1 (natF1 zero) tA_F1) p)
                      (ap2 Pair (natCode zero) tA))
        e_kA =
          ruleTrans (pairF1_eq (natF1 zero) tA_F1 p)
            (congL Pair tA (natF1_eq zero p))

        e_kB :
          Deriv (eqF (ap1 (pairF1 (natF1 (suc zero)) tB_F1) p)
                      (ap2 Pair (natCode (suc zero)) tB))
        e_kB =
          ruleTrans (pairF1_eq (natF1 (suc zero)) tB_F1 p)
            (congL Pair tB (natF1_eq (suc zero) p))

        e_kC :
          Deriv (eqF (ap1 (pairF1 (natF1 (suc (suc zero))) tC_F1) p)
                      (ap2 Pair (natCode (suc (suc zero))) tC))
        e_kC =
          ruleTrans (pairF1_eq (natF1 (suc (suc zero))) tC_F1 p)
            (congL Pair tC (natF1_eq (suc (suc zero)) p))

        e_BC :
          Deriv (eqF (ap1 (pairF1 (pairF1 (natF1 (suc zero)) tB_F1)
                                   (pairF1 (natF1 (suc (suc zero))) tC_F1)) p)
                      (ap2 Pair (ap2 Pair (natCode (suc zero)) tB)
                                (ap2 Pair (natCode (suc (suc zero))) tC)))
        e_BC =
          ruleTrans (pairF1_eq (pairF1 (natF1 (suc zero)) tB_F1)
                                (pairF1 (natF1 (suc (suc zero))) tC_F1) p)
            (ruleTrans (congL Pair _ e_kB)
                       (congR Pair _ e_kC))

    in ruleTrans (pairF1_eq (pairF1 (natF1 zero) tA_F1) _ p)
         (ruleTrans (congL Pair _ e_kA)
                    (congR Pair _ e_BC))

------------------------------------------------------------------------
-- packAx leaves (closed, parametric on Fun1/Fun2 indices).
--
-- packAx10_codeR_Term g h1 h2  =  Pair tag_ax (Pair (natCode 10) (codeFun2 (R g h1 h2)))
-- packAx6_codeF2 h             =  Pair tag_ax (Pair (natCode 6)  (codeFun2 h))
-- packAx7_codeF2 h             =  Pair tag_ax (Pair (natCode 7)  (codeFun2 h))

private
  N6 : Nat
  N6 = suc (suc (suc (suc (suc (suc zero)))))

  N7 : Nat
  N7 = suc (suc (suc (suc (suc (suc (suc zero))))))

  N10 : Nat
  N10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  packAx10_R_T : Fun1 -> Fun2 -> Fun2 -> Term
  packAx10_R_T g h1 h2 =
    ap2 Pair (natCode tag_ax)
      (ap2 Pair (natCode N10) (codeFun2 (R g h1 h2)))

  packAx6_T : Fun2 -> Term
  packAx6_T h =
    ap2 Pair (natCode tag_ax) (ap2 Pair (natCode N6) (codeFun2 h))

  packAx7_T : Fun2 -> Term
  packAx7_T h =
    ap2 Pair (natCode tag_ax) (ap2 Pair (natCode N7) (codeFun2 h))

  closed_packAx10_R : (g : Fun1) (h1 h2 : Fun2) -> Closed (packAx10_R_T g h1 h2)
  closed_packAx10_R g h1 h2 =
    closed_ap2 Pair _ _ (closed_natCode tag_ax)
      (closed_ap2 Pair _ _ (closed_natCode N10) (codeFun2_closed (R g h1 h2)))

  closed_packAx6 : (h : Fun2) -> Closed (packAx6_T h)
  closed_packAx6 h =
    closed_ap2 Pair _ _ (closed_natCode tag_ax)
      (closed_ap2 Pair _ _ (closed_natCode N6) (codeFun2_closed h))

  closed_packAx7 : (h : Fun2) -> Closed (packAx7_T h)
  closed_packAx7 h =
    closed_ap2 Pair _ _ (closed_natCode tag_ax)
      (closed_ap2 Pair _ _ (closed_natCode N7) (codeFun2_closed h))

  packAx10_R_F1 : Fun1 -> Fun2 -> Fun2 -> Fun1
  packAx10_R_F1 g h1 h2 = kF1 (packAx10_R_T g h1 h2)

  packAx10_R_F1_eq :
    (g : Fun1) (h1 h2 : Fun2) (p : Term) ->
    Deriv (eqF (ap1 (packAx10_R_F1 g h1 h2) p) (packAx10_R_T g h1 h2))
  packAx10_R_F1_eq g h1 h2 p =
    kF1_eq_closed (packAx10_R_T g h1 h2) (closed_packAx10_R g h1 h2) p

  packAx6_F1 : Fun2 -> Fun1
  packAx6_F1 h = kF1 (packAx6_T h)

  packAx6_F1_eq :
    (h : Fun2) (p : Term) ->
    Deriv (eqF (ap1 (packAx6_F1 h) p) (packAx6_T h))
  packAx6_F1_eq h p = kF1_eq_closed (packAx6_T h) (closed_packAx6 h) p

  packAx7_F1 : Fun2 -> Fun1
  packAx7_F1 h = kF1 (packAx7_T h)

  packAx7_F1_eq :
    (h : Fun2) (p : Term) ->
    Deriv (eqF (ap1 (packAx7_F1 h) p) (packAx7_T h))
  packAx7_F1_eq h p = kF1_eq_closed (packAx7_T h) (closed_packAx7 h) p

------------------------------------------------------------------------
-- Df_axRStep_F1 -- Fun1 wrapping Df_axRStep g h1 h2 X Y .
--
--   ap1 (Df_axRStep_F1 g h1 h2 X_F1 Y_F1) p
--      =Deriv= Df_axRStep g h1 h2 (ap1 X_F1 p) (ap1 Y_F1 p).
--
-- Note  Df_axRStep g h1 h2 X Y =
--        Pair tag_sb2
--          (Pair (spec2_at X Y) (packAx10_codeR_Term g h1 h2))
-- where  spec2_at X Y = Pair (Pair 0 (num X)) (Pair 1 (num Y)) .

Df_axRStep_F1 : (g : Fun1) (h1 h2 : Fun2) -> Fun1 -> Fun1 -> Fun1
Df_axRStep_F1 g h1 h2 X_F1 Y_F1 =
  sbLayerF1 zero (compose1U num X_F1)
    (sbLayerF1 (suc zero) (compose1U num Y_F1) (packAx10_R_F1 g h1 h2))

Df_axRStep_F1_eq :
  (g : Fun1) (h1 h2 : Fun2) (X_F1 Y_F1 : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (Df_axRStep_F1 g h1 h2 X_F1 Y_F1) p)
              (Df_axRStep g h1 h2 (ap1 X_F1 p) (ap1 Y_F1 p)))
Df_axRStep_F1_eq g h1 h2 X_F1 Y_F1 p =
  let i1 : Fun1
      i1 = sbLayerF1 (suc zero) (compose1U num Y_F1) (packAx10_R_F1 g h1 h2)

      e1 = sbLayerF1_eq (suc zero) (compose1U num Y_F1) (packAx10_R_F1 g h1 h2)
             (ap1 num (ap1 Y_F1 p)) (packAx10_R_T g h1 h2) p
             (compose1U_eq num Y_F1 p) (packAx10_R_F1_eq g h1 h2 p)
      e0 = sbLayerF1_eq zero (compose1U num X_F1) i1
             (ap1 num (ap1 X_F1 p)) _ p
             (compose1U_eq num X_F1 p) e1
  in e0

------------------------------------------------------------------------
-- Df_axEqCongL_F1 -- Fun1 wrapping Df_axEqCongL h tA tB tC.
--
--   ap1 (Df_axEqCongL_F1 h tA_F1 tB_F1 tC_F1) p
--      =Deriv= Df_axEqCongL h (ap1 tA_F1 p) (ap1 tB_F1 p) (ap1 tC_F1 p).

Df_axEqCongL_F1 : Fun2 -> Fun1 -> Fun1 -> Fun1 -> Fun1
Df_axEqCongL_F1 h tA_F1 tB_F1 tC_F1 =
  sbLayerF1 zero tA_F1
    (sbLayerF1 (suc zero) tB_F1
      (sbLayerF1 (suc (suc zero)) tC_F1 (packAx6_F1 h)))

Df_axEqCongL_F1_eq :
  (h : Fun2) (tA_F1 tB_F1 tC_F1 : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (Df_axEqCongL_F1 h tA_F1 tB_F1 tC_F1) p)
              (Df_axEqCongL h (ap1 tA_F1 p) (ap1 tB_F1 p) (ap1 tC_F1 p)))
Df_axEqCongL_F1_eq h tA_F1 tB_F1 tC_F1 p =
  let i2 : Fun1
      i2 = sbLayerF1 (suc (suc zero)) tC_F1 (packAx6_F1 h)
      i1 : Fun1
      i1 = sbLayerF1 (suc zero) tB_F1 i2

      e2 = sbLayerF1_eq (suc (suc zero)) tC_F1 (packAx6_F1 h)
             (ap1 tC_F1 p) (packAx6_T h) p
             (axRefl (ap1 tC_F1 p)) (packAx6_F1_eq h p)
      e1 = sbLayerF1_eq (suc zero) tB_F1 i2
             (ap1 tB_F1 p) _ p
             (axRefl (ap1 tB_F1 p)) e2
      e0 = sbLayerF1_eq zero tA_F1 i1
             (ap1 tA_F1 p) _ p
             (axRefl (ap1 tA_F1 p)) e1
  in e0

------------------------------------------------------------------------
-- Df_axEqCongR_F1 -- Fun1 wrapping Df_axEqCongR h tA tB tC.

Df_axEqCongR_F1 : Fun2 -> Fun1 -> Fun1 -> Fun1 -> Fun1
Df_axEqCongR_F1 h tA_F1 tB_F1 tC_F1 =
  sbLayerF1 zero tA_F1
    (sbLayerF1 (suc zero) tB_F1
      (sbLayerF1 (suc (suc zero)) tC_F1 (packAx7_F1 h)))

Df_axEqCongR_F1_eq :
  (h : Fun2) (tA_F1 tB_F1 tC_F1 : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (Df_axEqCongR_F1 h tA_F1 tB_F1 tC_F1) p)
              (Df_axEqCongR h (ap1 tA_F1 p) (ap1 tB_F1 p) (ap1 tC_F1 p)))
Df_axEqCongR_F1_eq h tA_F1 tB_F1 tC_F1 p =
  let i2 : Fun1
      i2 = sbLayerF1 (suc (suc zero)) tC_F1 (packAx7_F1 h)
      i1 : Fun1
      i1 = sbLayerF1 (suc zero) tB_F1 i2

      e2 = sbLayerF1_eq (suc (suc zero)) tC_F1 (packAx7_F1 h)
             (ap1 tC_F1 p) (packAx7_T h) p
             (axRefl (ap1 tC_F1 p)) (packAx7_F1_eq h p)
      e1 = sbLayerF1_eq (suc zero) tB_F1 i2
             (ap1 tB_F1 p) _ p
             (axRefl (ap1 tB_F1 p)) e2
      e0 = sbLayerF1_eq zero tA_F1 i1
             (ap1 tA_F1 p) _ p
             (axRefl (ap1 tA_F1 p)) e1
  in e0

------------------------------------------------------------------------
-- Term-slot congruences for the nested-sb Df builders (replace the old
-- tag_sb2 / tag_sb3 manual reconstructions in the stepF1 soundness proof).

Df_axRStep_cong :
  (g : Fun1) (h1 h2 : Fun2) (X X' Y Y' : Term) ->
  Deriv (eqF X X') -> Deriv (eqF Y Y') ->
  Deriv (eqF (Df_axRStep g h1 h2 X Y) (Df_axRStep g h1 h2 X' Y'))
Df_axRStep_cong g h1 h2 X X' Y Y' eX eY =
  sbLayer_cong zero (ap1 num X) (ap1 num X') _ _ (cong1 num eX)
    (sbLayer_cong (suc zero) (ap1 num Y) (ap1 num Y')
      (packAx10_R_T g h1 h2) (packAx10_R_T g h1 h2)
      (cong1 num eY) (axRefl (packAx10_R_T g h1 h2)))

Df_axEqCongL_cong :
  (h : Fun2) (tA tA' tB tB' tC tC' : Term) ->
  Deriv (eqF tA tA') -> Deriv (eqF tB tB') -> Deriv (eqF tC tC') ->
  Deriv (eqF (Df_axEqCongL h tA tB tC) (Df_axEqCongL h tA' tB' tC'))
Df_axEqCongL_cong h tA tA' tB tB' tC tC' eA eB eC =
  sbLayer_cong zero tA tA' _ _ eA
    (sbLayer_cong (suc zero) tB tB' _ _ eB
      (sbLayer_cong (suc (suc zero)) tC tC' (packAx6_T h) (packAx6_T h) eC
        (axRefl (packAx6_T h))))

Df_axEqCongR_cong :
  (h : Fun2) (tA tA' tB tB' tC tC' : Term) ->
  Deriv (eqF tA tA') -> Deriv (eqF tB tB') -> Deriv (eqF tC tC') ->
  Deriv (eqF (Df_axEqCongR h tA tB tC) (Df_axEqCongR h tA' tB' tC'))
Df_axEqCongR_cong h tA tA' tB tB' tC tC' eA eB eC =
  sbLayer_cong zero tA tA' _ _ eA
    (sbLayer_cong (suc zero) tB tB' _ _ eB
      (sbLayer_cong (suc (suc zero)) tC tC' (packAx7_T h) (packAx7_T h) eC
        (axRefl (packAx7_T h))))

------------------------------------------------------------------------
-- Phase 1B Step 2 -- Df_eqSym_F1 + Df_eqTrans_F1 builders.
--
-- These wrap the Df_eqSym / Df_eqTrans patterns at the Fun1 level so
-- stepF1 can be assembled from 3 nested Df_eqTrans_F1 calls.

private
  -- Df_eqSym Term (private in EncodedEqChain, reconstructed here).
  Df_eqSym_T : Term -> Term -> Term -> Term
  Df_eqSym_T cAB tA tB =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair
        (ap2 Pair (natCode tag_mp)
          (ap2 Pair (Df_axEqTrans tA tB tA) cAB))
        (Df_refl_meta tA))

Df_eqSym_F1 : Fun1 -> Fun1 -> Fun1 -> Fun1
Df_eqSym_F1 cAB_F1 tA_F1 tB_F1 =
  mpWrapF1
    (mpWrapF1 (axEqTrans_F1 tA_F1 tB_F1 tA_F1) cAB_F1)
    (refl_meta_F1 tA_F1)

Df_eqSym_F1_eq :
  (cAB_F1 tA_F1 tB_F1 : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1) p)
              (Df_eqSym_T (ap1 cAB_F1 p) (ap1 tA_F1 p) (ap1 tB_F1 p)))
Df_eqSym_F1_eq cAB_F1 tA_F1 tB_F1 p =
  let
    tA = ap1 tA_F1 p
    tB = ap1 tB_F1 p
    cAB = ap1 cAB_F1 p

    e_aET : Deriv (eqF (ap1 (axEqTrans_F1 tA_F1 tB_F1 tA_F1) p)
                       (Df_axEqTrans tA tB tA))
    e_aET = axEqTrans_F1_eq tA_F1 tB_F1 tA_F1 p

    inner_target : Term
    inner_target =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans tA tB tA) cAB)

    e_inner :
      Deriv (eqF (ap1 (mpWrapF1 (axEqTrans_F1 tA_F1 tB_F1 tA_F1) cAB_F1) p)
                  inner_target)
    e_inner =
      ruleTrans (mpWrapF1_eq (axEqTrans_F1 tA_F1 tB_F1 tA_F1) cAB_F1 p)
        (congR Pair (natCode tag_mp)
          (congL Pair cAB e_aET))

    e_refl : Deriv (eqF (ap1 (refl_meta_F1 tA_F1) p) (Df_refl_meta tA))
    e_refl = refl_meta_F1_eq tA_F1 p

  in ruleTrans (mpWrapF1_eq (mpWrapF1 (axEqTrans_F1 tA_F1 tB_F1 tA_F1) cAB_F1) (refl_meta_F1 tA_F1) p)
       (congR Pair (natCode tag_mp)
         (ruleTrans (congL Pair (ap1 (refl_meta_F1 tA_F1) p) e_inner)
                    (congR Pair _ e_refl)))

private
  Df_eqTrans_T : Term -> Term -> Term -> Term -> Term -> Term
  Df_eqTrans_T cAB cBC tA tB tC =
    ap2 Pair (natCode tag_mp)
      (ap2 Pair
        (ap2 Pair (natCode tag_mp)
          (ap2 Pair (Df_axEqTrans tB tA tC) (Df_eqSym_T cAB tA tB)))
        cBC)

Df_eqTrans_F1 : Fun1 -> Fun1 -> Fun1 -> Fun1 -> Fun1 -> Fun1
Df_eqTrans_F1 cAB_F1 cBC_F1 tA_F1 tB_F1 tC_F1 =
  mpWrapF1
    (mpWrapF1 (axEqTrans_F1 tB_F1 tA_F1 tC_F1) (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1))
    cBC_F1

Df_eqTrans_F1_eq :
  (cAB_F1 cBC_F1 tA_F1 tB_F1 tC_F1 : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (Df_eqTrans_F1 cAB_F1 cBC_F1 tA_F1 tB_F1 tC_F1) p)
              (Df_eqTrans_T (ap1 cAB_F1 p) (ap1 cBC_F1 p)
                            (ap1 tA_F1 p) (ap1 tB_F1 p) (ap1 tC_F1 p)))
Df_eqTrans_F1_eq cAB_F1 cBC_F1 tA_F1 tB_F1 tC_F1 p =
  let
    tA = ap1 tA_F1 p
    tB = ap1 tB_F1 p
    tC = ap1 tC_F1 p
    cAB = ap1 cAB_F1 p
    cBC = ap1 cBC_F1 p

    e_aET : Deriv (eqF (ap1 (axEqTrans_F1 tB_F1 tA_F1 tC_F1) p)
                       (Df_axEqTrans tB tA tC))
    e_aET = axEqTrans_F1_eq tB_F1 tA_F1 tC_F1 p

    e_eqSym : Deriv (eqF (ap1 (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1) p)
                         (Df_eqSym_T cAB tA tB))
    e_eqSym = Df_eqSym_F1_eq cAB_F1 tA_F1 tB_F1 p

    inner_target : Term
    inner_target =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqTrans tB tA tC) (Df_eqSym_T cAB tA tB))

    e_inner :
      Deriv (eqF (ap1 (mpWrapF1 (axEqTrans_F1 tB_F1 tA_F1 tC_F1) (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1)) p)
                  inner_target)
    e_inner =
      ruleTrans (mpWrapF1_eq (axEqTrans_F1 tB_F1 tA_F1 tC_F1) (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1) p)
        (congR Pair (natCode tag_mp)
          (ruleTrans
            (congL Pair (ap1 (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1) p) e_aET)
            (congR Pair _ e_eqSym)))

  in ruleTrans
       (mpWrapF1_eq (mpWrapF1 (axEqTrans_F1 tB_F1 tA_F1 tC_F1) (Df_eqSym_F1 cAB_F1 tA_F1 tB_F1)) cBC_F1 p)
       (congR Pair (natCode tag_mp)
         (congL Pair cBC e_inner))

------------------------------------------------------------------------
-- Sub-Term Fun1 helpers used by stepF1.
--
-- All universal in X_F1, Y_F1 (and h2 / g / h1 / Fun2 parameters).

-- encH2_at_F1 h2 X_F1 Y_F1 : Fun1 producing  encH2_at h2 X Y .
-- encH2_at h2 X Y =
--   Pair tag_ap2 (Pair (codeFun2 h2) (Pair (num X) (num Y))) .

private
  encH2_at_F1 : Fun2 -> Fun1 -> Fun1 -> Fun1
  encH2_at_F1 h2 X_F1 Y_F1 =
    pairF1 (natF1 tag_ap2)
      (pairF1 (codeFun2_F1 h2)
        (pairF1 (compose1U num X_F1) (compose1U num Y_F1)))

  encH2_at_F1_eq :
    (h2 : Fun2) (X_F1 Y_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (encH2_at_F1 h2 X_F1 Y_F1) p)
                (ap2 Pair (natCode tag_ap2)
                  (ap2 Pair (codeFun2 h2)
                    (ap2 Pair (ap1 num (ap1 X_F1 p)) (ap1 num (ap1 Y_F1 p))))))
  encH2_at_F1_eq h2 X_F1 Y_F1 p =
    let
      Xp = ap1 X_F1 p
      Yp = ap1 Y_F1 p

      e_numX : Deriv (eqF (ap1 (compose1U num X_F1) p) (ap1 num Xp))
      e_numX = compose1U_eq num X_F1 p

      e_numY : Deriv (eqF (ap1 (compose1U num Y_F1) p) (ap1 num Yp))
      e_numY = compose1U_eq num Y_F1 p

      e_pair_num :
        Deriv (eqF (ap1 (pairF1 (compose1U num X_F1) (compose1U num Y_F1)) p)
                    (ap2 Pair (ap1 num Xp) (ap1 num Yp)))
      e_pair_num =
        ruleTrans (pairF1_eq (compose1U num X_F1) (compose1U num Y_F1) p)
          (ruleTrans (congL Pair _ e_numX)
                     (congR Pair _ e_numY))

      e_inner :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 h2) (pairF1 (compose1U num X_F1) (compose1U num Y_F1))) p)
                    (ap2 Pair (codeFun2 h2) (ap2 Pair (ap1 num Xp) (ap1 num Yp))))
      e_inner =
        ruleTrans (pairF1_eq (codeFun2_F1 h2) (pairF1 (compose1U num X_F1) (compose1U num Y_F1)) p)
          (ruleTrans (congL Pair _ (codeFun2_F1_eq h2 p))
                     (congR Pair _ e_pair_num))

    in ruleTrans (pairF1_eq (natF1 tag_ap2) _ p)
         (ruleTrans (congL Pair _ (natF1_eq tag_ap2 p))
                    (congR Pair _ e_inner))

  -- encR_at_F1 g h1 h2 X_F1 Y_F1 : Fun1 producing  encR_at g h1 h2 X Y .
  encR_at_F1 : Fun1 -> Fun2 -> Fun2 -> Fun1 -> Fun1 -> Fun1
  encR_at_F1 g h1 h2 X_F1 Y_F1 =
    pairF1 (natF1 tag_ap2)
      (pairF1 (codeFun2_F1 (R g h1 h2))
        (pairF1 (compose1U num X_F1) (compose1U num Y_F1)))

  encR_at_F1_eq :
    (g : Fun1) (h1 h2 : Fun2) (X_F1 Y_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (encR_at_F1 g h1 h2 X_F1 Y_F1) p)
                (ap2 Pair (natCode tag_ap2)
                  (ap2 Pair (codeFun2 (R g h1 h2))
                    (ap2 Pair (ap1 num (ap1 X_F1 p)) (ap1 num (ap1 Y_F1 p))))))
  encR_at_F1_eq g h1 h2 X_F1 Y_F1 p =
    let
      Xp = ap1 X_F1 p
      Yp = ap1 Y_F1 p

      e_numX : Deriv (eqF (ap1 (compose1U num X_F1) p) (ap1 num Xp))
      e_numX = compose1U_eq num X_F1 p

      e_numY : Deriv (eqF (ap1 (compose1U num Y_F1) p) (ap1 num Yp))
      e_numY = compose1U_eq num Y_F1 p

      e_pair_num :
        Deriv (eqF (ap1 (pairF1 (compose1U num X_F1) (compose1U num Y_F1)) p)
                    (ap2 Pair (ap1 num Xp) (ap1 num Yp)))
      e_pair_num =
        ruleTrans (pairF1_eq (compose1U num X_F1) (compose1U num Y_F1) p)
          (ruleTrans (congL Pair _ e_numX)
                     (congR Pair _ e_numY))

      e_inner :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 (R g h1 h2))
                                 (pairF1 (compose1U num X_F1) (compose1U num Y_F1))) p)
                    (ap2 Pair (codeFun2 (R g h1 h2))
                      (ap2 Pair (ap1 num Xp) (ap1 num Yp))))
      e_inner =
        ruleTrans (pairF1_eq (codeFun2_F1 (R g h1 h2))
                              (pairF1 (compose1U num X_F1) (compose1U num Y_F1)) p)
          (ruleTrans (congL Pair _ (codeFun2_F1_eq (R g h1 h2) p))
                     (congR Pair _ e_pair_num))

    in ruleTrans (pairF1_eq (natF1 tag_ap2) _ p)
         (ruleTrans (congL Pair _ (natF1_eq tag_ap2 p))
                    (congR Pair _ e_inner))

  -- num_apply2_F1  h X_F1 Y_F1 : Fun1 producing  num (h X Y) .
  -- =  compose1U num (C h X_F1 Y_F1) .
  num_apply2_F1 : Fun2 -> Fun1 -> Fun1 -> Fun1
  num_apply2_F1 h X_F1 Y_F1 = compose1U num (C h X_F1 Y_F1)

  num_apply2_F1_eq :
    (h : Fun2) (X_F1 Y_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (num_apply2_F1 h X_F1 Y_F1) p)
                (ap1 num (ap2 h (ap1 X_F1 p) (ap1 Y_F1 p))))
  num_apply2_F1_eq h X_F1 Y_F1 p =
    let e_C : Deriv (eqF (ap1 (C h X_F1 Y_F1) p)
                          (ap2 h (ap1 X_F1 p) (ap1 Y_F1 p)))
        e_C = ax_C h X_F1 Y_F1 p
        e_compose : Deriv (eqF (ap1 (compose1U num (C h X_F1 Y_F1)) p)
                                (ap1 num (ap1 (C h X_F1 Y_F1) p)))
        e_compose = compose1U_eq num (C h X_F1 Y_F1) p
    in ruleTrans e_compose (cong1 num e_C)

  -- L_i Fun1 wrappers (universal in X_F1, Y_F1).

  L1_step_F1 : Fun1 -> Fun2 -> Fun2 -> Fun1 -> Fun1 -> Fun1
  L1_step_F1 g h1 h2 X_F1 Y_F1 =
    pairF1 (natF1 tag_ap2)
      (pairF1 (codeFun2_F1 (R g h1 h2))
        (pairF1 (compose1U num X_F1)
          (pairF1 (natF1 tag_ap1)
            (pairF1 (codeFun1_F1 s) (compose1U num Y_F1)))))

  L1_step_F1_eq :
    (g : Fun1) (h1 h2 : Fun2) (X_F1 Y_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (L1_step_F1 g h1 h2 X_F1 Y_F1) p)
                (ap2 Pair (natCode tag_ap2)
                  (ap2 Pair (codeFun2 (R g h1 h2))
                    (ap2 Pair (ap1 num (ap1 X_F1 p))
                      (ap2 Pair (natCode tag_ap1)
                        (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p))))))))
  L1_step_F1_eq g h1 h2 X_F1 Y_F1 p =
    let
      Xp = ap1 X_F1 p
      Yp = ap1 Y_F1 p
      numXp = ap1 num Xp
      numYp = ap1 num Yp

      e_numY : Deriv (eqF (ap1 (compose1U num Y_F1) p) numYp)
      e_numY = compose1U_eq num Y_F1 p

      e_sencY : Deriv (eqF (ap1 (pairF1 (codeFun1_F1 s) (compose1U num Y_F1)) p)
                            (ap2 Pair (codeFun1 s) numYp))
      e_sencY =
        ruleTrans (pairF1_eq (codeFun1_F1 s) (compose1U num Y_F1) p)
          (ruleTrans (congL Pair _ (codeFun1_F1_eq s p))
                     (congR Pair _ e_numY))

      e_sencAp1 :
        Deriv (eqF (ap1 (pairF1 (natF1 tag_ap1) (pairF1 (codeFun1_F1 s) (compose1U num Y_F1))) p)
                    (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) numYp)))
      e_sencAp1 =
        ruleTrans (pairF1_eq (natF1 tag_ap1) _ p)
          (ruleTrans (congL Pair _ (natF1_eq tag_ap1 p))
                     (congR Pair _ e_sencY))

      e_numX : Deriv (eqF (ap1 (compose1U num X_F1) p) numXp)
      e_numX = compose1U_eq num X_F1 p

      e_pair_inner :
        Deriv (eqF (ap1 (pairF1 (compose1U num X_F1) (pairF1 (natF1 tag_ap1) (pairF1 (codeFun1_F1 s) (compose1U num Y_F1)))) p)
                    (ap2 Pair numXp
                      (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) numYp))))
      e_pair_inner =
        ruleTrans (pairF1_eq (compose1U num X_F1) _ p)
          (ruleTrans (congL Pair _ e_numX)
                     (congR Pair _ e_sencAp1))

      e_pair_R :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 (R g h1 h2)) _) p)
                    (ap2 Pair (codeFun2 (R g h1 h2))
                      (ap2 Pair numXp
                        (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) numYp)))))
      e_pair_R =
        ruleTrans (pairF1_eq (codeFun2_F1 (R g h1 h2)) _ p)
          (ruleTrans (congL Pair _ (codeFun2_F1_eq (R g h1 h2) p))
                     (congR Pair _ e_pair_inner))

    in ruleTrans (pairF1_eq (natF1 tag_ap2) _ p)
         (ruleTrans (congL Pair _ (natF1_eq tag_ap2 p))
                    (congR Pair _ e_pair_R))

  -- encH1_F1 h1 A_F1 B_F1 : Fun1 producing encH1_at h1 A B .
  -- encH1_at h1 A B = Pair tag_ap2 (Pair (codeFun2 h1) (Pair A B)) .
  encH1_F1 : Fun2 -> Fun1 -> Fun1 -> Fun1
  encH1_F1 h1 A_F1 B_F1 =
    pairF1 (natF1 tag_ap2)
      (pairF1 (codeFun2_F1 h1) (pairF1 A_F1 B_F1))

  encH1_F1_eq :
    (h1 : Fun2) (A_F1 B_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (encH1_F1 h1 A_F1 B_F1) p)
                (ap2 Pair (natCode tag_ap2)
                  (ap2 Pair (codeFun2 h1)
                    (ap2 Pair (ap1 A_F1 p) (ap1 B_F1 p)))))
  encH1_F1_eq h1 A_F1 B_F1 p =
    let
      Ap = ap1 A_F1 p
      Bp = ap1 B_F1 p

      e_pair_AB :
        Deriv (eqF (ap1 (pairF1 A_F1 B_F1) p) (ap2 Pair Ap Bp))
      e_pair_AB = pairF1_eq A_F1 B_F1 p

      e_inner :
        Deriv (eqF (ap1 (pairF1 (codeFun2_F1 h1) (pairF1 A_F1 B_F1)) p)
                    (ap2 Pair (codeFun2 h1) (ap2 Pair Ap Bp)))
      e_inner =
        ruleTrans (pairF1_eq (codeFun2_F1 h1) (pairF1 A_F1 B_F1) p)
          (ruleTrans (congL Pair _ (codeFun2_F1_eq h1 p))
                     (congR Pair _ e_pair_AB))

    in ruleTrans (pairF1_eq (natF1 tag_ap2) _ p)
         (ruleTrans (congL Pair _ (natF1_eq tag_ap2 p))
                    (congR Pair _ e_inner))

  -- L5_step_F1 : Fun1 producing num (h1 (h2 X Y) (R g h1 h2 X Y)) .
  L5_step_F1 : Fun1 -> Fun2 -> Fun2 -> Fun1 -> Fun1 -> Fun1
  L5_step_F1 g h1 h2 X_F1 Y_F1 =
    compose1U num (C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1))

  L5_step_F1_eq :
    (g : Fun1) (h1 h2 : Fun2) (X_F1 Y_F1 : Fun1) (p : Term) ->
    Deriv (eqF (ap1 (L5_step_F1 g h1 h2 X_F1 Y_F1) p)
                (ap1 num (ap2 h1 (ap2 h2 (ap1 X_F1 p) (ap1 Y_F1 p))
                                  (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p)))))
  L5_step_F1_eq g h1 h2 X_F1 Y_F1 p =
    let
      Xp = ap1 X_F1 p
      Yp = ap1 Y_F1 p

      e_h2 : Deriv (eqF (ap1 (C h2 X_F1 Y_F1) p) (ap2 h2 Xp Yp))
      e_h2 = ax_C h2 X_F1 Y_F1 p

      e_R : Deriv (eqF (ap1 (C (R g h1 h2) X_F1 Y_F1) p) (ap2 (R g h1 h2) Xp Yp))
      e_R = ax_C (R g h1 h2) X_F1 Y_F1 p

      e_h1 :
        Deriv (eqF (ap1 (C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1)) p)
                    (ap2 h1 (ap1 (C h2 X_F1 Y_F1) p) (ap1 (C (R g h1 h2) X_F1 Y_F1) p)))
      e_h1 = ax_C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1) p

      e_h1_bridge :
        Deriv (eqF (ap2 h1 (ap1 (C h2 X_F1 Y_F1) p) (ap1 (C (R g h1 h2) X_F1 Y_F1) p))
                    (ap2 h1 (ap2 h2 Xp Yp) (ap2 (R g h1 h2) Xp Yp)))
      e_h1_bridge =
        ruleTrans (congL h1 (ap1 (C (R g h1 h2) X_F1 Y_F1) p) e_h2)
                  (congR h1 (ap2 h2 Xp Yp) e_R)

      e_inner :
        Deriv (eqF (ap1 (C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1)) p)
                    (ap2 h1 (ap2 h2 Xp Yp) (ap2 (R g h1 h2) Xp Yp)))
      e_inner = ruleTrans e_h1 e_h1_bridge

      e_compose :
        Deriv (eqF (ap1 (compose1U num (C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1))) p)
                    (ap1 num (ap1 (C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1)) p)))
      e_compose = compose1U_eq num (C h1 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1)) p

    in ruleTrans e_compose (cong1 num e_inner)

------------------------------------------------------------------------
-- stepF1 : the Fun1 step function for Dg = R baseF1 (Post stepF1 Pair) Pair.
--
-- stepF1 is applied at  p = Pair (Pair X Y) prev , producing the
-- encoded chain  Df_R_step g h1 h2 Df_h1_inst Df_h2_inst prev X Y
-- where Df_h{i}_inst A B = ap2 Df_h{i}_F2 A B.

stepF1 : (g : Fun1) (h1 h2 : Fun2) (Df_h1_F2 Df_h2_F2 : Fun2) -> Fun1
stepF1 g h1 h2 Df_h1_F2 Df_h2_F2 =
  let
    X_F1 = extract_X_F1
    Y_F1 = extract_Y_F1
    prev_F1 = extract_prev_F1

    encH2_F1' = encH2_at_F1 h2 X_F1 Y_F1
    encR_F1' = encR_at_F1 g h1 h2 X_F1 Y_F1
    num_h2_F1' = num_apply2_F1 h2 X_F1 Y_F1
    num_R_F1' = num_apply2_F1 (R g h1 h2) X_F1 Y_F1

    L1F = L1_step_F1 g h1 h2 X_F1 Y_F1
    L2F = encH1_F1 h1 encH2_F1' encR_F1'
    L3F = encH1_F1 h1 num_h2_F1' encR_F1'
    L4F = encH1_F1 h1 num_h2_F1' num_R_F1'
    L5F = L5_step_F1 g h1 h2 X_F1 Y_F1

    d_axRStep_F1' = Df_axRStep_F1 g h1 h2 X_F1 Y_F1
    d_h2_inst_F1 = C Df_h2_F2 X_F1 Y_F1
    d_step_B_F1 =
      mpWrapF1 (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') d_h2_inst_F1
    d_step_C_F1 =
      mpWrapF1 (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') prev_F1
    d_h1_inst_F1 = C Df_h1_F2 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1)
    d_step_D_F1 = d_h1_inst_F1

    d_trans_AB_F1 = Df_eqTrans_F1 d_axRStep_F1' d_step_B_F1 L1F L2F L3F
    d_trans_AC_F1 = Df_eqTrans_F1 d_trans_AB_F1 d_step_C_F1 L1F L3F L4F
    d_trans_AD_F1 = Df_eqTrans_F1 d_trans_AC_F1 d_step_D_F1 L1F L4F L5F
  in d_trans_AD_F1

------------------------------------------------------------------------
-- Df_eqSym_T_cong / Df_eqTrans_T_cong : cong helpers on the 3/5 Term slots
-- of Df_eqSym_T / Df_eqTrans_T (Pair-encoded).

Df_eqSym_T_cong :
  (cAB cAB' tA tA' tB tB' : Term) ->
  Deriv (eqF cAB cAB') -> Deriv (eqF tA tA') -> Deriv (eqF tB tB') ->
  Deriv (eqF (Df_eqSym_T cAB tA tB) (Df_eqSym_T cAB' tA' tB'))
Df_eqSym_T_cong cAB cAB' tA tA' tB tB' eAB eA eB =
  let
    aET_cong : Deriv (eqF (Df_axEqTrans tA tB tA) (Df_axEqTrans tA' tB' tA'))
    aET_cong = Df_axEqTrans_cong tA tA' tB tB' tA tA' eA eB eA

    refl_cong : Deriv (eqF (Df_refl_meta tA) (Df_refl_meta tA'))
    refl_cong = Df_refl_meta_cong tA tA' eA

    inner_pair :
      Deriv (eqF (ap2 Pair (Df_axEqTrans tA tB tA) cAB)
                  (ap2 Pair (Df_axEqTrans tA' tB' tA') cAB'))
    inner_pair =
      ruleTrans (congL Pair cAB aET_cong)
                (congR Pair (Df_axEqTrans tA' tB' tA') eAB)

    inner_mp :
      Deriv (eqF (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tA tB tA) cAB))
                  (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tA' tB' tA') cAB')))
    inner_mp = congR Pair (natCode tag_mp) inner_pair

    outer_pair :
      Deriv (eqF (ap2 Pair (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tA tB tA) cAB))
                            (Df_refl_meta tA))
                  (ap2 Pair (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tA' tB' tA') cAB'))
                            (Df_refl_meta tA')))
    outer_pair =
      ruleTrans (congL Pair (Df_refl_meta tA) inner_mp)
                (congR Pair _ refl_cong)
  in congR Pair (natCode tag_mp) outer_pair

Df_eqTrans_T_cong :
  (cAB cAB' cBC cBC' tA tA' tB tB' tC tC' : Term) ->
  Deriv (eqF cAB cAB') -> Deriv (eqF cBC cBC') ->
  Deriv (eqF tA tA') -> Deriv (eqF tB tB') -> Deriv (eqF tC tC') ->
  Deriv (eqF (Df_eqTrans_T cAB cBC tA tB tC) (Df_eqTrans_T cAB' cBC' tA' tB' tC'))
Df_eqTrans_T_cong cAB cAB' cBC cBC' tA tA' tB tB' tC tC' eAB eBC eA eB eC =
  let
    aET_cong : Deriv (eqF (Df_axEqTrans tB tA tC) (Df_axEqTrans tB' tA' tC'))
    aET_cong = Df_axEqTrans_cong tB tB' tA tA' tC tC' eB eA eC

    eqSym_cong : Deriv (eqF (Df_eqSym_T cAB tA tB) (Df_eqSym_T cAB' tA' tB'))
    eqSym_cong = Df_eqSym_T_cong cAB cAB' tA tA' tB tB' eAB eA eB

    inner_pair :
      Deriv (eqF (ap2 Pair (Df_axEqTrans tB tA tC) (Df_eqSym_T cAB tA tB))
                  (ap2 Pair (Df_axEqTrans tB' tA' tC') (Df_eqSym_T cAB' tA' tB')))
    inner_pair =
      ruleTrans (congL Pair (Df_eqSym_T cAB tA tB) aET_cong)
                (congR Pair (Df_axEqTrans tB' tA' tC') eqSym_cong)

    inner_mp :
      Deriv (eqF (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tB tA tC) (Df_eqSym_T cAB tA tB)))
                  (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tB' tA' tC') (Df_eqSym_T cAB' tA' tB'))))
    inner_mp = congR Pair (natCode tag_mp) inner_pair

    outer_pair :
      Deriv (eqF (ap2 Pair (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tB tA tC) (Df_eqSym_T cAB tA tB))) cBC)
                  (ap2 Pair (ap2 Pair (natCode tag_mp) (ap2 Pair (Df_axEqTrans tB' tA' tC') (Df_eqSym_T cAB' tA' tB'))) cBC'))
    outer_pair =
      ruleTrans (congL Pair cBC inner_mp)
                (congR Pair _ eBC)

  in congR Pair (natCode tag_mp) outer_pair

------------------------------------------------------------------------
-- stepF1_eq : the closure equation for stepF1 at p = Pair (Pair X Y) prev.

stepF1_eq :
  (g : Fun1) (h1 h2 : Fun2) (Df_h1_F2 Df_h2_F2 : Fun2) (X Y prev : Term) ->
  Deriv (eqF (ap1 (stepF1 g h1 h2 Df_h1_F2 Df_h2_F2)
                  (ap2 Pair (ap2 Pair X Y) prev))
              (Df_R_step g h1 h2
                (\ A B -> ap2 Df_h1_F2 A B)
                (\ A B -> ap2 Df_h2_F2 A B)
                prev X Y))
stepF1_eq g h1 h2 Df_h1_F2 Df_h2_F2 X Y prev =
  let
    p = ap2 Pair (ap2 Pair X Y) prev

    X_F1 = extract_X_F1
    Y_F1 = extract_Y_F1
    prev_F1 = extract_prev_F1

    encH2_F1' = encH2_at_F1 h2 X_F1 Y_F1
    encR_F1' = encR_at_F1 g h1 h2 X_F1 Y_F1
    num_h2_F1' = num_apply2_F1 h2 X_F1 Y_F1
    num_R_F1' = num_apply2_F1 (R g h1 h2) X_F1 Y_F1

    L1F = L1_step_F1 g h1 h2 X_F1 Y_F1
    L2F = encH1_F1 h1 encH2_F1' encR_F1'
    L3F = encH1_F1 h1 num_h2_F1' encR_F1'
    L4F = encH1_F1 h1 num_h2_F1' num_R_F1'
    L5F = L5_step_F1 g h1 h2 X_F1 Y_F1

    d_axRStep_F1' = Df_axRStep_F1 g h1 h2 X_F1 Y_F1
    d_h2_inst_F1 = C Df_h2_F2 X_F1 Y_F1
    d_step_B_F1' =
      mpWrapF1 (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') d_h2_inst_F1
    d_step_C_F1' =
      mpWrapF1 (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') prev_F1
    d_h1_inst_F1 = C Df_h1_F2 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1)
    d_step_D_F1' = d_h1_inst_F1

    d_trans_AB_F1' = Df_eqTrans_F1 d_axRStep_F1' d_step_B_F1' L1F L2F L3F
    d_trans_AC_F1' = Df_eqTrans_F1 d_trans_AB_F1' d_step_C_F1' L1F L3F L4F

    -- ====================================================================
    -- Step A: extractor evals.
    -- ====================================================================
    eX : Deriv (eqF (ap1 X_F1 p) X)
    eX = extract_X_at X Y prev

    eY : Deriv (eqF (ap1 Y_F1 p) Y)
    eY = extract_Y_at X Y prev

    eprev : Deriv (eqF (ap1 prev_F1 p) prev)
    eprev = extract_prev_at X Y prev

    -- ====================================================================
    -- Step B: concrete Term values at the call site.
    -- ====================================================================
    h2_XY = ap2 h2 X Y
    R_XY  = ap2 (R g h1 h2) X Y
    encH2_concrete = ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 h2) (ap2 Pair (ap1 num X) (ap1 num Y)))
    encR_concrete = ap2 Pair (natCode tag_ap2)
                       (ap2 Pair (codeFun2 (R g h1 h2)) (ap2 Pair (ap1 num X) (ap1 num Y)))
    num_h2_concrete = ap1 num h2_XY
    num_R_concrete  = ap1 num R_XY
    L1_concrete =
      ap2 Pair (natCode tag_ap2)
        (ap2 Pair (codeFun2 (R g h1 h2))
          (ap2 Pair (ap1 num X)
            (ap2 Pair (natCode tag_ap1)
              (ap2 Pair (codeFun1 s) (ap1 num Y)))))
    L2_concrete = ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 h1)
                      (ap2 Pair encH2_concrete encR_concrete))
    L3_concrete = ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 h1)
                      (ap2 Pair num_h2_concrete encR_concrete))
    L4_concrete = ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 h1)
                      (ap2 Pair num_h2_concrete num_R_concrete))
    L5_concrete = ap1 num (ap2 h1 h2_XY R_XY)

    d_axRStep_concrete = Df_axRStep g h1 h2 X Y
    d_step_B_concrete =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqCongL h1 encH2_concrete num_h2_concrete encR_concrete)
                  (ap2 Df_h2_F2 X Y))
    d_step_C_concrete =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqCongR h1 encR_concrete num_R_concrete num_h2_concrete)
                  prev)
    d_step_D_concrete = ap2 Df_h1_F2 h2_XY R_XY

    d_trans_AB_concrete =
      Df_eqTrans_T d_axRStep_concrete d_step_B_concrete L1_concrete L2_concrete L3_concrete
    d_trans_AC_concrete =
      Df_eqTrans_T d_trans_AB_concrete d_step_C_concrete L1_concrete L3_concrete L4_concrete
    d_trans_AD_concrete =
      Df_eqTrans_T d_trans_AC_concrete d_step_D_concrete L1_concrete L4_concrete L5_concrete

    -- ====================================================================
    -- Step C: bridge eqs from Fun1-eval-at-p to concrete values.
    -- ====================================================================

    -- L1F p -> L1_concrete .
    eL1 : Deriv (eqF (ap1 L1F p) L1_concrete)
    eL1 =
      let
        e_raw : Deriv (eqF (ap1 L1F p)
                            (ap2 Pair (natCode tag_ap2)
                              (ap2 Pair (codeFun2 (R g h1 h2))
                                (ap2 Pair (ap1 num (ap1 X_F1 p))
                                  (ap2 Pair (natCode tag_ap1)
                                    (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p))))))))
        e_raw = L1_step_F1_eq g h1 h2 X_F1 Y_F1 p

        e_numXp : Deriv (eqF (ap1 num (ap1 X_F1 p)) (ap1 num X))
        e_numXp = cong1 num eX

        e_numYp : Deriv (eqF (ap1 num (ap1 Y_F1 p)) (ap1 num Y))
        e_numYp = cong1 num eY

        e_sencY :
          Deriv (eqF (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p)))
                      (ap2 Pair (codeFun1 s) (ap1 num Y)))
        e_sencY = congR Pair (codeFun1 s) e_numYp

        e_sencAp1 :
          Deriv (eqF (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p))))
                      (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num Y))))
        e_sencAp1 = congR Pair (natCode tag_ap1) e_sencY

        e_pair_inner :
          Deriv (eqF (ap2 Pair (ap1 num (ap1 X_F1 p))
                       (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p)))))
                      (ap2 Pair (ap1 num X)
                       (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num Y)))))
        e_pair_inner =
          ruleTrans
            (congL Pair (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p))))
                        e_numXp)
            (congR Pair (ap1 num X) e_sencAp1)

        e_pair_R :
          Deriv (eqF
            (ap2 Pair (codeFun2 (R g h1 h2))
              (ap2 Pair (ap1 num (ap1 X_F1 p))
                (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num (ap1 Y_F1 p))))))
            (ap2 Pair (codeFun2 (R g h1 h2))
              (ap2 Pair (ap1 num X)
                (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (ap1 num Y))))))
        e_pair_R = congR Pair (codeFun2 (R g h1 h2)) e_pair_inner

      in ruleTrans e_raw (congR Pair (natCode tag_ap2) e_pair_R)

    -- encH2_F1' p -> encH2_concrete .
    eEncH2 : Deriv (eqF (ap1 encH2_F1' p) encH2_concrete)
    eEncH2 =
      let
        e_raw : Deriv (eqF (ap1 encH2_F1' p)
                            (ap2 Pair (natCode tag_ap2)
                              (ap2 Pair (codeFun2 h2)
                                (ap2 Pair (ap1 num (ap1 X_F1 p)) (ap1 num (ap1 Y_F1 p))))))
        e_raw = encH2_at_F1_eq h2 X_F1 Y_F1 p

        e_pair_num :
          Deriv (eqF (ap2 Pair (ap1 num (ap1 X_F1 p)) (ap1 num (ap1 Y_F1 p)))
                      (ap2 Pair (ap1 num X) (ap1 num Y)))
        e_pair_num =
          ruleTrans (congL Pair (ap1 num (ap1 Y_F1 p)) (cong1 num eX))
                    (congR Pair (ap1 num X) (cong1 num eY))

        e_inner :
          Deriv (eqF (ap2 Pair (codeFun2 h2) (ap2 Pair (ap1 num (ap1 X_F1 p)) (ap1 num (ap1 Y_F1 p))))
                      (ap2 Pair (codeFun2 h2) (ap2 Pair (ap1 num X) (ap1 num Y))))
        e_inner = congR Pair (codeFun2 h2) e_pair_num

      in ruleTrans e_raw (congR Pair (natCode tag_ap2) e_inner)

    -- encR_F1' p -> encR_concrete .
    eEncR : Deriv (eqF (ap1 encR_F1' p) encR_concrete)
    eEncR =
      let
        e_raw = encR_at_F1_eq g h1 h2 X_F1 Y_F1 p

        e_pair_num :
          Deriv (eqF (ap2 Pair (ap1 num (ap1 X_F1 p)) (ap1 num (ap1 Y_F1 p)))
                      (ap2 Pair (ap1 num X) (ap1 num Y)))
        e_pair_num =
          ruleTrans (congL Pair (ap1 num (ap1 Y_F1 p)) (cong1 num eX))
                    (congR Pair (ap1 num X) (cong1 num eY))

      in ruleTrans e_raw
           (congR Pair (natCode tag_ap2)
             (congR Pair (codeFun2 (R g h1 h2)) e_pair_num))

    -- num_h2_F1' p -> num_h2_concrete .
    eNumH2 : Deriv (eqF (ap1 num_h2_F1' p) num_h2_concrete)
    eNumH2 =
      let
        e_raw : Deriv (eqF (ap1 num_h2_F1' p) (ap1 num (ap2 h2 (ap1 X_F1 p) (ap1 Y_F1 p))))
        e_raw = num_apply2_F1_eq h2 X_F1 Y_F1 p

        e_h2 : Deriv (eqF (ap2 h2 (ap1 X_F1 p) (ap1 Y_F1 p)) h2_XY)
        e_h2 =
          ruleTrans (congL h2 (ap1 Y_F1 p) eX)
                    (congR h2 X eY)

      in ruleTrans e_raw (cong1 num e_h2)

    -- num_R_F1' p -> num_R_concrete .
    eNumR : Deriv (eqF (ap1 num_R_F1' p) num_R_concrete)
    eNumR =
      let
        e_raw : Deriv (eqF (ap1 num_R_F1' p)
                           (ap1 num (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p))))
        e_raw = num_apply2_F1_eq (R g h1 h2) X_F1 Y_F1 p

        e_R : Deriv (eqF (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p)) R_XY)
        e_R =
          ruleTrans (congL (R g h1 h2) (ap1 Y_F1 p) eX)
                    (congR (R g h1 h2) X eY)

      in ruleTrans e_raw (cong1 num e_R)

    -- L2F p -> L2_concrete .
    eL2 : Deriv (eqF (ap1 L2F p) L2_concrete)
    eL2 =
      let
        e_raw : Deriv (eqF (ap1 L2F p)
                            (ap2 Pair (natCode tag_ap2)
                              (ap2 Pair (codeFun2 h1)
                                (ap2 Pair (ap1 encH2_F1' p) (ap1 encR_F1' p)))))
        e_raw = encH1_F1_eq h1 encH2_F1' encR_F1' p

        e_pair :
          Deriv (eqF (ap2 Pair (ap1 encH2_F1' p) (ap1 encR_F1' p))
                      (ap2 Pair encH2_concrete encR_concrete))
        e_pair =
          ruleTrans (congL Pair (ap1 encR_F1' p) eEncH2)
                    (congR Pair encH2_concrete eEncR)

      in ruleTrans e_raw
           (congR Pair (natCode tag_ap2)
             (congR Pair (codeFun2 h1) e_pair))

    -- L3F p -> L3_concrete .
    eL3 : Deriv (eqF (ap1 L3F p) L3_concrete)
    eL3 =
      let
        e_raw = encH1_F1_eq h1 num_h2_F1' encR_F1' p

        e_pair :
          Deriv (eqF (ap2 Pair (ap1 num_h2_F1' p) (ap1 encR_F1' p))
                      (ap2 Pair num_h2_concrete encR_concrete))
        e_pair =
          ruleTrans (congL Pair (ap1 encR_F1' p) eNumH2)
                    (congR Pair num_h2_concrete eEncR)

      in ruleTrans e_raw
           (congR Pair (natCode tag_ap2)
             (congR Pair (codeFun2 h1) e_pair))

    -- L4F p -> L4_concrete .
    eL4 : Deriv (eqF (ap1 L4F p) L4_concrete)
    eL4 =
      let
        e_raw = encH1_F1_eq h1 num_h2_F1' num_R_F1' p

        e_pair :
          Deriv (eqF (ap2 Pair (ap1 num_h2_F1' p) (ap1 num_R_F1' p))
                      (ap2 Pair num_h2_concrete num_R_concrete))
        e_pair =
          ruleTrans (congL Pair (ap1 num_R_F1' p) eNumH2)
                    (congR Pair num_h2_concrete eNumR)

      in ruleTrans e_raw
           (congR Pair (natCode tag_ap2)
             (congR Pair (codeFun2 h1) e_pair))

    -- L5F p -> L5_concrete .
    eL5 : Deriv (eqF (ap1 L5F p) L5_concrete)
    eL5 =
      let
        e_raw : Deriv (eqF (ap1 L5F p)
                            (ap1 num (ap2 h1 (ap2 h2 (ap1 X_F1 p) (ap1 Y_F1 p))
                                              (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p)))))
        e_raw = L5_step_F1_eq g h1 h2 X_F1 Y_F1 p

        e_h2 : Deriv (eqF (ap2 h2 (ap1 X_F1 p) (ap1 Y_F1 p)) h2_XY)
        e_h2 = ruleTrans (congL h2 (ap1 Y_F1 p) eX)
                          (congR h2 X eY)

        e_R : Deriv (eqF (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p)) R_XY)
        e_R = ruleTrans (congL (R g h1 h2) (ap1 Y_F1 p) eX)
                         (congR (R g h1 h2) X eY)

        e_h1 :
          Deriv (eqF (ap2 h1 (ap2 h2 (ap1 X_F1 p) (ap1 Y_F1 p))
                              (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p)))
                      (ap2 h1 h2_XY R_XY))
        e_h1 =
          ruleTrans (congL h1 (ap2 (R g h1 h2) (ap1 X_F1 p) (ap1 Y_F1 p)) e_h2)
                    (congR h1 h2_XY e_R)

      in ruleTrans e_raw (cong1 num e_h1)

    -- ====================================================================
    -- Step D: step-body Fun1 bridges.
    -- ====================================================================

    -- d_axRStep_F1' p -> d_axRStep_concrete .
    eAxRStep : Deriv (eqF (ap1 d_axRStep_F1' p) d_axRStep_concrete)
    eAxRStep =
      let
        e_raw : Deriv (eqF (ap1 d_axRStep_F1' p)
                            (Df_axRStep g h1 h2 (ap1 X_F1 p) (ap1 Y_F1 p)))
        e_raw = Df_axRStep_F1_eq g h1 h2 X_F1 Y_F1 p

        -- Df_axRStep g h1 h2 X1 Y1 is parametric on raw X1, Y1 .
        -- We need to cong from (X_F1 p, Y_F1 p) -> (X, Y) .
        -- Df_axRStep g h1 h2 X1 Y1 = Pair tag_sb2 (Pair (spec2_at X1 Y1) (packAx10)).
        -- spec2_at X1 Y1 = Pair (Pair 0 (num X1)) (Pair 1 (num Y1)) .

      in ruleTrans e_raw
           (Df_axRStep_cong g h1 h2 (ap1 X_F1 p) X (ap1 Y_F1 p) Y eX eY)

    -- d_h2_inst_F1 p -> ap2 Df_h2_F2 X Y .
    eDh2 : Deriv (eqF (ap1 d_h2_inst_F1 p) (ap2 Df_h2_F2 X Y))
    eDh2 =
      let
        e_raw : Deriv (eqF (ap1 (C Df_h2_F2 X_F1 Y_F1) p)
                            (ap2 Df_h2_F2 (ap1 X_F1 p) (ap1 Y_F1 p)))
        e_raw = ax_C Df_h2_F2 X_F1 Y_F1 p
      in ruleTrans e_raw
           (ruleTrans (congL Df_h2_F2 (ap1 Y_F1 p) eX)
                      (congR Df_h2_F2 X eY))

    -- d_step_B_F1' p -> d_step_B_concrete .
    eStepB : Deriv (eqF (ap1 d_step_B_F1' p) d_step_B_concrete)
    eStepB =
      let
        e_raw : Deriv (eqF (ap1 d_step_B_F1' p)
                            (ap2 Pair (natCode tag_mp)
                              (ap2 Pair (ap1 (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') p)
                                        (ap1 d_h2_inst_F1 p))))
        e_raw = mpWrapF1_eq (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') d_h2_inst_F1 p

        e_congL_raw :
          Deriv (eqF (ap1 (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') p)
                      (Df_axEqCongL h1 (ap1 encH2_F1' p) (ap1 num_h2_F1' p) (ap1 encR_F1' p)))
        e_congL_raw = Df_axEqCongL_F1_eq h1 encH2_F1' num_h2_F1' encR_F1' p

        -- Bridge the Df_axEqCongL's 3 Term args from Fun1-eval forms to concrete.
        -- Df_axEqCongL h1 tA tB tC = Pair tag_sb3 (Pair (spec3_at tA tB tC) (packAx6 h1)).
        -- spec3_at tA tB tC = Pair (Pair 0 tA) (Pair (Pair 1 tB) (Pair 2 tC)) .

        e_congL_concrete :
          Deriv (eqF (Df_axEqCongL h1 (ap1 encH2_F1' p) (ap1 num_h2_F1' p) (ap1 encR_F1' p))
                      (Df_axEqCongL h1 encH2_concrete num_h2_concrete encR_concrete))
        e_congL_concrete =
          Df_axEqCongL_cong h1
            (ap1 encH2_F1' p) encH2_concrete
            (ap1 num_h2_F1' p) num_h2_concrete
            (ap1 encR_F1' p) encR_concrete
            eEncH2 eNumH2 eEncR

        e_congL_full :
          Deriv (eqF (ap1 (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') p)
                      (Df_axEqCongL h1 encH2_concrete num_h2_concrete encR_concrete))
        e_congL_full = ruleTrans e_congL_raw e_congL_concrete

        e_pair :
          Deriv (eqF (ap2 Pair (ap1 (Df_axEqCongL_F1 h1 encH2_F1' num_h2_F1' encR_F1') p)
                               (ap1 d_h2_inst_F1 p))
                      (ap2 Pair (Df_axEqCongL h1 encH2_concrete num_h2_concrete encR_concrete)
                                (ap2 Df_h2_F2 X Y)))
        e_pair =
          ruleTrans (congL Pair (ap1 d_h2_inst_F1 p) e_congL_full)
                    (congR Pair (Df_axEqCongL h1 encH2_concrete num_h2_concrete encR_concrete) eDh2)

      in ruleTrans e_raw (congR Pair (natCode tag_mp) e_pair)

    -- d_step_C_F1' p -> d_step_C_concrete .
    eStepC : Deriv (eqF (ap1 d_step_C_F1' p) d_step_C_concrete)
    eStepC =
      let
        e_raw : Deriv (eqF (ap1 d_step_C_F1' p)
                            (ap2 Pair (natCode tag_mp)
                              (ap2 Pair (ap1 (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') p)
                                        (ap1 prev_F1 p))))
        e_raw = mpWrapF1_eq (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') prev_F1 p

        e_congR_raw :
          Deriv (eqF (ap1 (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') p)
                      (Df_axEqCongR h1 (ap1 encR_F1' p) (ap1 num_R_F1' p) (ap1 num_h2_F1' p)))
        e_congR_raw = Df_axEqCongR_F1_eq h1 encR_F1' num_R_F1' num_h2_F1' p

        e_congR_concrete :
          Deriv (eqF (Df_axEqCongR h1 (ap1 encR_F1' p) (ap1 num_R_F1' p) (ap1 num_h2_F1' p))
                      (Df_axEqCongR h1 encR_concrete num_R_concrete num_h2_concrete))
        e_congR_concrete =
          Df_axEqCongR_cong h1
            (ap1 encR_F1' p) encR_concrete
            (ap1 num_R_F1' p) num_R_concrete
            (ap1 num_h2_F1' p) num_h2_concrete
            eEncR eNumR eNumH2

        e_congR_full :
          Deriv (eqF (ap1 (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') p)
                      (Df_axEqCongR h1 encR_concrete num_R_concrete num_h2_concrete))
        e_congR_full = ruleTrans e_congR_raw e_congR_concrete

        e_pair :
          Deriv (eqF (ap2 Pair (ap1 (Df_axEqCongR_F1 h1 encR_F1' num_R_F1' num_h2_F1') p)
                               (ap1 prev_F1 p))
                      (ap2 Pair (Df_axEqCongR h1 encR_concrete num_R_concrete num_h2_concrete) prev))
        e_pair =
          ruleTrans (congL Pair (ap1 prev_F1 p) e_congR_full)
                    (congR Pair (Df_axEqCongR h1 encR_concrete num_R_concrete num_h2_concrete) eprev)

      in ruleTrans e_raw (congR Pair (natCode tag_mp) e_pair)

    -- d_step_D_F1' p -> d_step_D_concrete .
    eStepD : Deriv (eqF (ap1 d_step_D_F1' p) d_step_D_concrete)
    eStepD =
      let
        e_h2 : Deriv (eqF (ap1 (C h2 X_F1 Y_F1) p) h2_XY)
        e_h2 =
          ruleTrans (ax_C h2 X_F1 Y_F1 p)
            (ruleTrans (congL h2 (ap1 Y_F1 p) eX)
                       (congR h2 X eY))

        e_R : Deriv (eqF (ap1 (C (R g h1 h2) X_F1 Y_F1) p) R_XY)
        e_R =
          ruleTrans (ax_C (R g h1 h2) X_F1 Y_F1 p)
            (ruleTrans (congL (R g h1 h2) (ap1 Y_F1 p) eX)
                       (congR (R g h1 h2) X eY))

        e_raw : Deriv (eqF (ap1 d_step_D_F1' p)
                            (ap2 Df_h1_F2 (ap1 (C h2 X_F1 Y_F1) p)
                                          (ap1 (C (R g h1 h2) X_F1 Y_F1) p)))
        e_raw = ax_C Df_h1_F2 (C h2 X_F1 Y_F1) (C (R g h1 h2) X_F1 Y_F1) p

      in ruleTrans e_raw
           (ruleTrans (congL Df_h1_F2 (ap1 (C (R g h1 h2) X_F1 Y_F1) p) e_h2)
                      (congR Df_h1_F2 h2_XY e_R))

    -- ====================================================================
    -- Step E: bridge d_trans_AB_F1', d_trans_AC_F1' through Df_eqTrans_T_cong.
    -- ====================================================================

    e_trans_AB_F1 :
      Deriv (eqF (ap1 d_trans_AB_F1' p) d_trans_AB_concrete)
    e_trans_AB_F1 =
      let
        e_unfold :
          Deriv (eqF (ap1 d_trans_AB_F1' p)
                      (Df_eqTrans_T (ap1 d_axRStep_F1' p) (ap1 d_step_B_F1' p)
                                    (ap1 L1F p) (ap1 L2F p) (ap1 L3F p)))
        e_unfold = Df_eqTrans_F1_eq d_axRStep_F1' d_step_B_F1' L1F L2F L3F p

        e_cong :
          Deriv (eqF (Df_eqTrans_T (ap1 d_axRStep_F1' p) (ap1 d_step_B_F1' p)
                                    (ap1 L1F p) (ap1 L2F p) (ap1 L3F p))
                      d_trans_AB_concrete)
        e_cong = Df_eqTrans_T_cong
                    (ap1 d_axRStep_F1' p) d_axRStep_concrete
                    (ap1 d_step_B_F1' p) d_step_B_concrete
                    (ap1 L1F p) L1_concrete
                    (ap1 L2F p) L2_concrete
                    (ap1 L3F p) L3_concrete
                    eAxRStep eStepB eL1 eL2 eL3
      in ruleTrans e_unfold e_cong

    e_trans_AC_F1 :
      Deriv (eqF (ap1 d_trans_AC_F1' p) d_trans_AC_concrete)
    e_trans_AC_F1 =
      let
        e_unfold :
          Deriv (eqF (ap1 d_trans_AC_F1' p)
                      (Df_eqTrans_T (ap1 d_trans_AB_F1' p) (ap1 d_step_C_F1' p)
                                    (ap1 L1F p) (ap1 L3F p) (ap1 L4F p)))
        e_unfold = Df_eqTrans_F1_eq d_trans_AB_F1' d_step_C_F1' L1F L3F L4F p

        e_cong :
          Deriv (eqF (Df_eqTrans_T (ap1 d_trans_AB_F1' p) (ap1 d_step_C_F1' p)
                                    (ap1 L1F p) (ap1 L3F p) (ap1 L4F p))
                      d_trans_AC_concrete)
        e_cong = Df_eqTrans_T_cong
                    (ap1 d_trans_AB_F1' p) d_trans_AB_concrete
                    (ap1 d_step_C_F1' p) d_step_C_concrete
                    (ap1 L1F p) L1_concrete
                    (ap1 L3F p) L3_concrete
                    (ap1 L4F p) L4_concrete
                    e_trans_AB_F1 eStepC eL1 eL3 eL4
      in ruleTrans e_unfold e_cong

    -- ====================================================================
    -- Step F: final assembly via outermost Df_eqTrans_F1_eq + Df_eqTrans_T_cong.
    -- ====================================================================
    e_unfold :
      Deriv (eqF (ap1 (stepF1 g h1 h2 Df_h1_F2 Df_h2_F2) p)
                  (Df_eqTrans_T (ap1 d_trans_AC_F1' p) (ap1 d_step_D_F1' p)
                                (ap1 L1F p) (ap1 L4F p) (ap1 L5F p)))
    e_unfold = Df_eqTrans_F1_eq d_trans_AC_F1' d_step_D_F1' L1F L4F L5F p

    e_cong :
      Deriv (eqF (Df_eqTrans_T (ap1 d_trans_AC_F1' p) (ap1 d_step_D_F1' p)
                                (ap1 L1F p) (ap1 L4F p) (ap1 L5F p))
                  d_trans_AD_concrete)
    e_cong = Df_eqTrans_T_cong
                (ap1 d_trans_AC_F1' p) d_trans_AC_concrete
                (ap1 d_step_D_F1' p) d_step_D_concrete
                (ap1 L1F p) L1_concrete
                (ap1 L4F p) L4_concrete
                (ap1 L5F p) L5_concrete
                e_trans_AC_F1 eStepD eL1 eL4 eL5

  in ruleTrans e_unfold e_cong

------------------------------------------------------------------------
-- Phase 1B Step 3 -- Dg + dg_at_O_red + dg_at_succ_red.
--
-- Dg is the BRA primitive recursor whose base case is baseF1 and whose
-- step case is (Post stepF1 Pair) Pair.  We define Dg parametric on
-- g, h1, h2, Df_g_F1, Df_h1_F2, Df_h2_F2.

Dg :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_F1 : Fun1) (Df_h1_F2 Df_h2_F2 : Fun2) -> Fun2
Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 =
  R (baseF1 g h1 h2 Df_g_F1)
    (Post (stepF1 g h1 h2 Df_h1_F2 Df_h2_F2) Pair)
    Pair

------------------------------------------------------------------------
-- dg_at_O_red : Dg X O = baseF1 X .

dg_at_O_red :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_F1 : Fun1) (Df_h1_F2 Df_h2_F2 : Fun2) (X : Term) ->
  Deriv (eqF (ap2 (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2) X O)
              (ap1 (baseF1 g h1 h2 Df_g_F1) X))
dg_at_O_red g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 X =
  ax_R_base (baseF1 g h1 h2 Df_g_F1)
            (Post (stepF1 g h1 h2 Df_h1_F2 Df_h2_F2) Pair)
            Pair X

------------------------------------------------------------------------
-- dg_at_succ_red : Dg X (s Y) = stepF1 (Pair (Pair X Y) (Dg X Y)) .

dg_at_succ_red :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_F1 : Fun1) (Df_h1_F2 Df_h2_F2 : Fun2) (X Y : Term) ->
  Deriv (eqF (ap2 (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2) X (ap1 s Y))
              (ap1 (stepF1 g h1 h2 Df_h1_F2 Df_h2_F2)
                   (ap2 Pair (ap2 Pair X Y)
                             (ap2 (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2) X Y))))
dg_at_succ_red g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 X Y =
  let
    Dg' = Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2
    stepF1' = stepF1 g h1 h2 Df_h1_F2 Df_h2_F2

    e_R_step :
      Deriv (eqF (ap2 Dg' X (ap1 s Y))
                  (ap2 (Post stepF1' Pair) (ap2 Pair X Y) (ap2 Dg' X Y)))
    e_R_step =
      ax_R_step (baseF1 g h1 h2 Df_g_F1) (Post stepF1' Pair) Pair X Y

    e_Post :
      Deriv (eqF (ap2 (Post stepF1' Pair) (ap2 Pair X Y) (ap2 Dg' X Y))
                  (ap1 stepF1' (ap2 Pair (ap2 Pair X Y) (ap2 Dg' X Y))))
    e_Post = axPost stepF1' Pair (ap2 Pair X Y) (ap2 Dg' X Y)

  in ruleTrans e_R_step e_Post

------------------------------------------------------------------------
-- Phase 1B Step 5 -- step_proof_imp .
--
-- The Carneiro-lift of  thm12_R_step_meta  needed for the ruleIndNat
-- assembly of  thm12_R .  All four sub-step Derivs are imp-lifted ;
-- Steps A, B, D are closed so  impLift  suffices ; Step C uses
-- imp_encoded_mp with  ih_R_typed_imp = impRefl P_univ  (since the
-- IH's RHS antC = codeFTeq2 (R g h1 h2) X Y  is exactly the RHS of
-- P_univ definitionally).
--
-- The encoded_eqTrans chain is lifted via imp_encoded_eqSym +
-- imp_encoded_eqTrans (private helpers parametric on P : Formula ;
-- built atop imp_encoded_mp from BRA4.Thm12.EncodedMp).

private
  -- imp_encoded_eqSym -- Hilbert-lifted encoded_eqSym (BRA4.Thm12.EncodedEqChain).
  --
  -- Given  imp P (thmT cAB = encEq tA tB) , produce
  --   imp P (thmT (mpWrap (mpWrap (Df_axEqTrans tA tB tA) cAB) (Df_refl_meta tA))
  --          = encEq tB tA) .
  imp_encoded_eqSym :
    (P : Formula)
    (cABProof : Term) (tA tB : Term)
    (inertA : InertU tA) (inertB : InertU tB)
    (imp_ih_AB : Deriv (imp P (eqF (ap1 thmT cABProof) (encEq tA tB)))) ->
    Deriv (imp P (eqF
      (ap1 thmT
        (ap2 Pair (natCode tag_mp)
          (ap2 Pair
            (ap2 Pair (natCode tag_mp)
              (ap2 Pair (Df_axEqTrans tA tB tA) cABProof))
            (Df_refl_meta tA))))
      (encEq tB tA)))
  imp_encoded_eqSym P cABProof tA tB inertA inertB imp_ih_AB =
    let
      ih_ax_sym_imp :
        Deriv (imp P (eqF (ap1 thmT (Df_axEqTrans tA tB tA))
                           (ap2 Pair (natCode tag_imp)
                             (ap2 Pair (encEq tA tB)
                               (ap2 Pair (natCode tag_imp)
                                 (ap2 Pair (encEq tA tA) (encEq tB tA)))))))
      ih_ax_sym_imp = impLift {P} (encodedAxEqTrans tA tB tA inertB inertA)

      sym_antP1 : Term
      sym_antP1 = encEq tA tB

      sym_consP1 : Term
      sym_consP1 =
        ap2 Pair (natCode tag_imp) (ap2 Pair (encEq tA tA) (encEq tB tA))

      sym_mp1 :
        Deriv (imp P (eqF
          (ap1 thmT (ap2 Pair (natCode tag_mp)
                       (ap2 Pair (Df_axEqTrans tA tB tA) cABProof)))
          sym_consP1))
      sym_mp1 = imp_encoded_mp P (Df_axEqTrans tA tB tA) cABProof
                                 sym_antP1 sym_consP1
                                 ih_ax_sym_imp imp_ih_AB

      ih_refl_imp :
        Deriv (imp P (eqF (ap1 thmT (Df_refl_meta tA)) (encEq tA tA)))
      ih_refl_imp = impLift {P} (encoded_refl tA)

      sym_antP2 : Term
      sym_antP2 = encEq tA tA

      sym_consP2 : Term
      sym_consP2 = encEq tB tA

      sym_term : Term
      sym_term =
        ap2 Pair (natCode tag_mp)
          (ap2 Pair (Df_axEqTrans tA tB tA) cABProof)

      sym_mp2 :
        Deriv (imp P (eqF
          (ap1 thmT (ap2 Pair (natCode tag_mp)
                       (ap2 Pair sym_term (Df_refl_meta tA))))
          sym_consP2))
      sym_mp2 = imp_encoded_mp P sym_term (Df_refl_meta tA)
                                 sym_antP2 sym_consP2
                                 sym_mp1 ih_refl_imp

    in sym_mp2

  -- imp_encoded_eqTrans -- Hilbert-lifted encoded_eqTrans (BRA4.Thm12.EncodedEqChain).
  --
  -- Given  imp P (thmT cAB = encEq tA tB)  and  imp P (thmT cBC = encEq tB tC) ,
  -- produce  imp P (thmT (Df_eqTrans cAB cBC tA tB tC) = encEq tA tC) .
  imp_encoded_eqTrans :
    (P : Formula)
    (cAB cBC : Term) (tA tB tC : Term)
    (inertA : InertU tA) (inertB : InertU tB) (inertC : InertU tC)
    (imp_ih_AB : Deriv (imp P (eqF (ap1 thmT cAB) (encEq tA tB))))
    (imp_ih_BC : Deriv (imp P (eqF (ap1 thmT cBC) (encEq tB tC)))) ->
    Deriv (imp P (eqF (ap1 thmT (Df_eqTrans cAB cBC tA tB tC)) (encEq tA tC)))
  imp_encoded_eqTrans P cAB cBC tA tB tC inertA inertB inertC imp_ih_AB imp_ih_BC =
    let
      cBA : Term
      cBA = ap2 Pair (natCode tag_mp)
              (ap2 Pair
                (ap2 Pair (natCode tag_mp)
                  (ap2 Pair (Df_axEqTrans tA tB tA) cAB))
                (Df_refl_meta tA))

      imp_ih_BA : Deriv (imp P (eqF (ap1 thmT cBA) (encEq tB tA)))
      imp_ih_BA = imp_encoded_eqSym P cAB tA tB inertA inertB imp_ih_AB

      ih_ax_trans_imp :
        Deriv (imp P (eqF (ap1 thmT (Df_axEqTrans tB tA tC))
                           (ap2 Pair (natCode tag_imp)
                             (ap2 Pair (encEq tB tA)
                               (ap2 Pair (natCode tag_imp)
                                 (ap2 Pair (encEq tB tC) (encEq tA tC)))))))
      ih_ax_trans_imp = impLift {P} (encodedAxEqTrans tB tA tC inertA inertC)

      trans_antP1 : Term
      trans_antP1 = encEq tB tA

      trans_consP1 : Term
      trans_consP1 =
        ap2 Pair (natCode tag_imp) (ap2 Pair (encEq tB tC) (encEq tA tC))

      trans_mp1 :
        Deriv (imp P (eqF
          (ap1 thmT (ap2 Pair (natCode tag_mp)
                       (ap2 Pair (Df_axEqTrans tB tA tC) cBA)))
          trans_consP1))
      trans_mp1 = imp_encoded_mp P (Df_axEqTrans tB tA tC) cBA
                                   trans_antP1 trans_consP1
                                   ih_ax_trans_imp imp_ih_BA

      trans_antP2 : Term
      trans_antP2 = encEq tB tC

      trans_consP2 : Term
      trans_consP2 = encEq tA tC

      trans_term : Term
      trans_term =
        ap2 Pair (natCode tag_mp)
          (ap2 Pair (Df_axEqTrans tB tA tC) cBA)

      trans_mp2 :
        Deriv (imp P (eqF
          (ap1 thmT (ap2 Pair (natCode tag_mp)
                       (ap2 Pair trans_term cBC)))
          trans_consP2))
      trans_mp2 = imp_encoded_mp P trans_term cBC
                                   trans_antP2 trans_consP2
                                   trans_mp1 imp_ih_BC

    in trans_mp2

------------------------------------------------------------------------
-- step_proof_imp -- the induction-step proof for thm12_R, in
-- Hilbert form  imp P_univ Q  where
--   P_univ = eqF (thmT (Dg X Y)) (codeFTeq2 (R g h1 h2) X Y)
-- with X = var 1 and Y = var 0.

step_proof_imp :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_F1 : Fun1) (Df_h1_F2 Df_h2_F2 : Fun2)
  (ih_h1 : (A B : Term) ->
             Deriv (eqF (ap1 thmT (ap2 Df_h1_F2 A B)) (codeFTeq2 h1 A B)))
  (ih_h2 : (A B : Term) ->
             Deriv (eqF (ap1 thmT (ap2 Df_h2_F2 A B)) (codeFTeq2 h2 A B))) ->
  Deriv (imp
    (eqF (ap1 thmT (ap2 (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2)
                         (var (suc zero)) (var zero)))
          (codeFTeq2 (R g h1 h2) (var (suc zero)) (var zero)))
    (eqF (ap1 thmT (ap2 (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2)
                         (var (suc zero)) (ap1 s (var zero))))
          (codeFTeq2 (R g h1 h2) (var (suc zero)) (ap1 s (var zero)))))
step_proof_imp g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 ih_h1 ih_h2 =
  let
    X : Term
    X = var (suc zero)

    Y : Term
    Y = var zero

    Dg' : Fun2
    Dg' = Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2

    stepF1' : Fun1
    stepF1' = stepF1 g h1 h2 Df_h1_F2 Df_h2_F2

    prev : Term
    prev = ap2 Dg' X Y

    Df_h1_inst : Term -> Term -> Term
    Df_h1_inst A B = ap2 Df_h1_F2 A B

    Df_h2_inst : Term -> Term -> Term
    Df_h2_inst A B = ap2 Df_h2_F2 A B

    P_univ : Formula
    P_univ = eqF (ap1 thmT prev) (codeFTeq2 (R g h1 h2) X Y)

    L1 = L1_at  g h1 h2 X Y
    L2 = L2_at  g h1 h2 X Y
    L3 = L3_at  g h1 h2 X Y
    L4 = L4_at  g h1 h2 X Y
    L5 = L5_R   g h1 h2 X Y
    L1' = L1'_at g h1 h2 X Y

    encH2 = encH2_at h2 X Y
    encR  = encR_at  g h1 h2 X Y

    ---------------------------------------------------------------
    -- InertU witnesses : every substituent / L-position is num-based.
    ---------------------------------------------------------------
    ncEncH2 : NumCode encH2
    ncEncH2 = ncAp2 h2 (ap1 num X) (ap1 num Y) (ncNum X) (ncNum Y)

    ncEncR : NumCode encR
    ncEncR = ncAp2 (R g h1 h2) (ap1 num X) (ap1 num Y) (ncNum X) (ncNum Y)

    iEncR : InertU encR
    iEncR = sbt_inert_NumCode encR ncEncR

    iNumH2 : InertU (ap1 num (ap2 h2 X Y))
    iNumH2 = sbt_inert_NumCode (ap1 num (ap2 h2 X Y)) (ncNum (ap2 h2 X Y))

    iNumR : InertU (ap1 num (ap2 (R g h1 h2) X Y))
    iNumR = sbt_inert_NumCode (ap1 num (ap2 (R g h1 h2) X Y))
              (ncNum (ap2 (R g h1 h2) X Y))

    iL1 : InertU L1
    iL1 = sbt_inert_NumCode L1
            (ncAp2 (R g h1 h2) (ap1 num X) (s_enc_num Y) (ncNum X)
              (ncAp1 s (ap1 num Y) (ncNum Y)))

    iL2 : InertU L2
    iL2 = sbt_inert_NumCode L2 (ncAp2 h1 encH2 encR ncEncH2 ncEncR)

    iL3 : InertU L3
    iL3 = sbt_inert_NumCode L3
            (ncAp2 h1 (ap1 num (ap2 h2 X Y)) encR (ncNum (ap2 h2 X Y)) ncEncR)

    iL4 : InertU L4
    iL4 = sbt_inert_NumCode L4
            (ncAp2 h1 (ap1 num (ap2 h2 X Y)) (ap1 num (ap2 (R g h1 h2) X Y))
              (ncNum (ap2 h2 X Y)) (ncNum (ap2 (R g h1 h2) X Y)))

    iL5 : InertU L5
    iL5 = sbt_inert_NumCode L5
            (ncNum (ap2 h1 (ap2 h2 X Y) (ap2 (R g h1 h2) X Y)))

    ---------------------------------------------------------------
    -- Step A : enc(L1 = L2) via encodedAxRStep .  Closed.
    ---------------------------------------------------------------
    d_axRStep : Term
    d_axRStep = Df_axRStep g h1 h2 X Y

    e_step_A : Deriv (eqF (ap1 thmT d_axRStep) (encEq L1 L2))
    e_step_A = encodedAxRStep g h1 h2 X Y

    imp_e_step_A :
      Deriv (imp P_univ (eqF (ap1 thmT d_axRStep) (encEq L1 L2)))
    imp_e_step_A = impLift {P_univ} e_step_A

    ---------------------------------------------------------------
    -- Step B : enc(L2 = L3) via encoded_mp on IH_h2 .  Closed.
    ---------------------------------------------------------------
    antB : Term
    antB = encEq encH2 (ap1 num (ap2 h2 X Y))

    consB : Term
    consB = encEq L2 L3

    ih_ax_B :
      Deriv (eqF (ap1 thmT (Df_axEqCongL h1 encH2
                              (ap1 num (ap2 h2 X Y)) encR))
                  (encodedAxEqCongL_Term h1 encH2
                    (ap1 num (ap2 h2 X Y)) encR))
    ih_ax_B = encodedAxEqCongL h1 encH2
                (ap1 num (ap2 h2 X Y)) encR
                iNumH2 iEncR

    ih_h2_typed : Deriv (eqF (ap1 thmT (Df_h2_inst X Y)) antB)
    ih_h2_typed = ih_h2 X Y

    d_step_B : Term
    d_step_B =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqCongL h1 encH2 (ap1 num (ap2 h2 X Y)) encR)
                  (Df_h2_inst X Y))

    e_step_B : Deriv (eqF (ap1 thmT d_step_B) consB)
    e_step_B = encoded_mp
                 (Df_axEqCongL h1 encH2 (ap1 num (ap2 h2 X Y)) encR)
                 (Df_h2_inst X Y) antB consB ih_ax_B ih_h2_typed

    imp_e_step_B : Deriv (imp P_univ (eqF (ap1 thmT d_step_B) consB))
    imp_e_step_B = impLift {P_univ} e_step_B

    ---------------------------------------------------------------
    -- Step C : enc(L3 = L4) via imp_encoded_mp on ih_R_typed_imp .
    --
    -- antC = encEq encR (num R(X,Y)) = codeFTeq2 (R g h1 h2) X Y  (RHS of P_univ).
    -- ih_R_typed_imp : imp P_univ (thmT prev = antC) = imp P_univ P_univ
    --                = impRefl P_univ .
    ---------------------------------------------------------------
    antC : Term
    antC = encEq encR (ap1 num (ap2 (R g h1 h2) X Y))

    consC : Term
    consC = encEq L3 L4

    ih_ax_C :
      Deriv (eqF (ap1 thmT (Df_axEqCongR h1 encR
                              (ap1 num (ap2 (R g h1 h2) X Y))
                              (ap1 num (ap2 h2 X Y))))
                  (encodedAxEqCongR_Term h1 encR
                    (ap1 num (ap2 (R g h1 h2) X Y))
                    (ap1 num (ap2 h2 X Y))))
    ih_ax_C = encodedAxEqCongR h1 encR
                 (ap1 num (ap2 (R g h1 h2) X Y))
                 (ap1 num (ap2 h2 X Y))
                 iNumR iNumH2

    ih_R_typed_imp : Deriv (imp P_univ (eqF (ap1 thmT prev) antC))
    ih_R_typed_imp = impRefl P_univ

    d_step_C : Term
    d_step_C =
      ap2 Pair (natCode tag_mp)
        (ap2 Pair (Df_axEqCongR h1 encR
                     (ap1 num (ap2 (R g h1 h2) X Y))
                     (ap1 num (ap2 h2 X Y)))
                  prev)

    imp_e_step_C : Deriv (imp P_univ (eqF (ap1 thmT d_step_C) consC))
    imp_e_step_C = imp_encoded_mp P_univ
                     (Df_axEqCongR h1 encR
                       (ap1 num (ap2 (R g h1 h2) X Y))
                       (ap1 num (ap2 h2 X Y)))
                     prev antC consC
                     (impLift {P_univ} ih_ax_C)
                     ih_R_typed_imp

    ---------------------------------------------------------------
    -- Step D : enc(L4 = L5) via IH_h1 .  Closed.
    ---------------------------------------------------------------
    d_step_D : Term
    d_step_D = Df_h1_inst (ap2 h2 X Y) (ap2 (R g h1 h2) X Y)

    e_step_D : Deriv (eqF (ap1 thmT d_step_D) (encEq L4 L5))
    e_step_D = ih_h1 (ap2 h2 X Y) (ap2 (R g h1 h2) X Y)

    imp_e_step_D : Deriv (imp P_univ (eqF (ap1 thmT d_step_D) (encEq L4 L5)))
    imp_e_step_D = impLift {P_univ} e_step_D

    ---------------------------------------------------------------
    -- Chain via imp_encoded_eqTrans (3 times) .
    ---------------------------------------------------------------
    d_trans_AB : Term
    d_trans_AB = Df_eqTrans d_axRStep d_step_B L1 L2 L3

    imp_e_trans_AB : Deriv (imp P_univ (eqF (ap1 thmT d_trans_AB) (encEq L1 L3)))
    imp_e_trans_AB = imp_encoded_eqTrans P_univ
                        d_axRStep d_step_B L1 L2 L3
                        iL1 iL2 iL3
                        imp_e_step_A imp_e_step_B

    d_trans_AC : Term
    d_trans_AC = Df_eqTrans d_trans_AB d_step_C L1 L3 L4

    imp_e_trans_AC : Deriv (imp P_univ (eqF (ap1 thmT d_trans_AC) (encEq L1 L4)))
    imp_e_trans_AC = imp_encoded_eqTrans P_univ
                        d_trans_AB d_step_C L1 L3 L4
                        iL1 iL3 iL4
                        imp_e_trans_AB imp_e_step_C

    d_trans_AD : Term
    d_trans_AD = Df_eqTrans d_trans_AC d_step_D L1 L4 L5

    imp_e_trans_AD : Deriv (imp P_univ (eqF (ap1 thmT d_trans_AD) (encEq L1 L5)))
    imp_e_trans_AD = imp_encoded_eqTrans P_univ
                        d_trans_AC d_step_D L1 L4 L5
                        iL1 iL4 iL5
                        imp_e_trans_AC imp_e_step_D

    ---------------------------------------------------------------
    -- Closed RHS-bridge:  encEq L1 L5  ->  codeFTeq2 (R g h1 h2) X (s Y) .
    ---------------------------------------------------------------
    s_enc_to_num_sY : Deriv (eqF (s_enc_num Y) (ap1 num (ap1 s Y)))
    s_enc_to_num_sY = ruleSym (num_at_S Y)

    inner_pair_bridge :
      Deriv (eqF (ap2 Pair (ap1 num X) (s_enc_num Y))
                  (ap2 Pair (ap1 num X) (ap1 num (ap1 s Y))))
    inner_pair_bridge = congR Pair (ap1 num X) s_enc_to_num_sY

    inner2_pair_bridge :
      Deriv (eqF (ap2 Pair (codeFun2 (R g h1 h2))
                          (ap2 Pair (ap1 num X) (s_enc_num Y)))
                  (ap2 Pair (codeFun2 (R g h1 h2))
                          (ap2 Pair (ap1 num X) (ap1 num (ap1 s Y)))))
    inner2_pair_bridge = congR Pair (codeFun2 (R g h1 h2)) inner_pair_bridge

    LHS_slot_bridge : Deriv (eqF L1 L1')
    LHS_slot_bridge = congR Pair (natCode tag_ap2) inner2_pair_bridge

    axRStep_eq :
      Deriv (eqF (ap2 (R g h1 h2) X (ap1 s Y))
                  (ap2 h1 (ap2 h2 X Y) (ap2 (R g h1 h2) X Y)))
    axRStep_eq = ax_R_step g h1 h2 X Y

    RHS_slot_bridge :
      Deriv (eqF L5 (ap1 num (ap2 (R g h1 h2) X (ap1 s Y))))
    RHS_slot_bridge = cong1 num (ruleSym axRStep_eq)

    pair_inner :
      Deriv (eqF (ap2 Pair L1 L5)
                  (ap2 Pair L1' (ap1 num (ap2 (R g h1 h2) X (ap1 s Y)))))
    pair_inner =
      ruleTrans (congL Pair L5 LHS_slot_bridge)
                (congR Pair L1' RHS_slot_bridge)

    outer_bridge :
      Deriv (eqF (encEq L1 L5)
                  (codeFTeq2 (R g h1 h2) X (ap1 s Y)))
    outer_bridge = congR Pair (natCode tag_eq) pair_inner

    imp_outer_bridge :
      Deriv (imp P_univ (eqF (encEq L1 L5)
                              (codeFTeq2 (R g h1 h2) X (ap1 s Y))))
    imp_outer_bridge = impLift {P_univ} outer_bridge

    imp_chain_to_codeFTeq2 :
      Deriv (imp P_univ (eqF (ap1 thmT d_trans_AD)
                              (codeFTeq2 (R g h1 h2) X (ap1 s Y))))
    imp_chain_to_codeFTeq2 =
      impEqTrans {P_univ} (ap1 thmT d_trans_AD)
                          (encEq L1 L5)
                          (codeFTeq2 (R g h1 h2) X (ap1 s Y))
                          imp_e_trans_AD imp_outer_bridge

    ---------------------------------------------------------------
    -- LHS-bridge:  ap1 thmT (Dg' X (s Y))  ->  ap1 thmT d_trans_AD .
    -- Uses dg_at_succ_red + stepF1_eq under cong1 thmT .
    ---------------------------------------------------------------
    dg_succ_bridge :
      Deriv (eqF (ap2 Dg' X (ap1 s Y))
                  (ap1 stepF1' (ap2 Pair (ap2 Pair X Y) prev)))
    dg_succ_bridge =
      dg_at_succ_red g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 X Y

    stepF1_bridge :
      Deriv (eqF (ap1 stepF1' (ap2 Pair (ap2 Pair X Y) prev))
                  (Df_R_step g h1 h2 Df_h1_inst Df_h2_inst prev X Y))
    stepF1_bridge =
      stepF1_eq g h1 h2 Df_h1_F2 Df_h2_F2 X Y prev

    dg_to_DfR :
      Deriv (eqF (ap2 Dg' X (ap1 s Y))
                  (Df_R_step g h1 h2 Df_h1_inst Df_h2_inst prev X Y))
    dg_to_DfR = ruleTrans dg_succ_bridge stepF1_bridge

    thmT_dg_to_DfR :
      Deriv (eqF (ap1 thmT (ap2 Dg' X (ap1 s Y)))
                  (ap1 thmT (Df_R_step g h1 h2 Df_h1_inst Df_h2_inst prev X Y)))
    thmT_dg_to_DfR = cong1 thmT dg_to_DfR

    imp_thmT_dg_to_DfR :
      Deriv (imp P_univ (eqF (ap1 thmT (ap2 Dg' X (ap1 s Y)))
                              (ap1 thmT d_trans_AD)))
    imp_thmT_dg_to_DfR = impLift {P_univ} thmT_dg_to_DfR

  in impEqTrans {P_univ}
       (ap1 thmT (ap2 Dg' X (ap1 s Y)))
       (ap1 thmT d_trans_AD)
       (codeFTeq2 (R g h1 h2) X (ap1 s Y))
       imp_thmT_dg_to_DfR imp_chain_to_codeFTeq2

------------------------------------------------------------------------
-- Substitution-bridge helpers used by thm12_R.
--
-- Needed because  substT  distribution gets stuck at opaque
-- codeFun2 (R g h1 h2)  inside codeFTeq2 (R g h1 h2) X Y , i.e. when
-- g, h1, h2 are universally quantified.  We use
--   closedAt (codeFun2_closed (R g h1 h2)) k b
-- to discharge the codeFun2 position via an Eq witness, then lift
-- structurally through codeFTeq2's Pair-of-Pair shape via Eq.cong .
--
-- For ruleInst2 we additionally need  simSubstT_pres : closed Terms
-- are simSubst-stable.  Ported from BRA3.Thm.Thm12.PartR.simSubstT_pres .

private
  ap1_get_arg_R : Term -> Term
  ap1_get_arg_R O           = O
  ap1_get_arg_R (var _)     = O
  ap1_get_arg_R (ap1 _ x)   = x
  ap1_get_arg_R (ap2 _ _ _) = O

  ap2_get_arg1_R : Term -> Term
  ap2_get_arg1_R O           = O
  ap2_get_arg1_R (var _)     = O
  ap2_get_arg1_R (ap1 _ _)   = O
  ap2_get_arg1_R (ap2 _ x _) = x

  ap2_get_arg2_R : Term -> Term
  ap2_get_arg2_R O           = O
  ap2_get_arg2_R (var _)     = O
  ap2_get_arg2_R (ap1 _ _)   = O
  ap2_get_arg2_R (ap2 _ _ y) = y

  ap1_inj_eq_R : {f : Fun1} {x y : Term} -> Eq (ap1 f x) (ap1 f y) -> Eq x y
  ap1_inj_eq_R h = eqCong ap1_get_arg_R h

  ap2_inj_l_eq_R : {gg : Fun2} {x y u v : Term} ->
                    Eq (ap2 gg x y) (ap2 gg u v) -> Eq x u
  ap2_inj_l_eq_R h = eqCong ap2_get_arg1_R h

  ap2_inj_r_eq_R : {gg : Fun2} {x y u v : Term} ->
                    Eq (ap2 gg x y) (ap2 gg u v) -> Eq y v
  ap2_inj_r_eq_R h = eqCong ap2_get_arg2_R h

  closed_ap1_inv_R : (f : Fun1) (a : Term) -> Closed (ap1 f a) -> Closed a
  closed_ap1_inv_R f a c =
    mkClosed (\ k b -> ap1_inj_eq_R {f = f} (closedAt c k b))

  closed_ap2_inv_l_R : (gg : Fun2) (a b : Term) -> Closed (ap2 gg a b) -> Closed a
  closed_ap2_inv_l_R gg a b c =
    mkClosed (\ k b' -> ap2_inj_l_eq_R {gg = gg} (closedAt c k b'))

  closed_ap2_inv_r_R : (gg : Fun2) (a b : Term) -> Closed (ap2 gg a b) -> Closed b
  closed_ap2_inv_r_R gg a b c =
    mkClosed (\ k b' -> ap2_inj_r_eq_R {gg = gg} (closedAt c k b'))

  simSubstT_pres :
    (t : Term) -> Closed t ->
    (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term) ->
    Eq (simSubstT k1 t1 k2 t2 t) t
  simSubstT_pres O       ct k1 t1 k2 t2 = refl
  simSubstT_pres (var m) ct k1 t1 k2 t2 =
    emptyElim (closed_var_absurd m ct)
  simSubstT_pres (ap1 f a) ct k1 t1 k2 t2 =
    eqCong (ap1 f) (simSubstT_pres a (closed_ap1_inv_R f a ct) k1 t1 k2 t2)
  simSubstT_pres (ap2 gg a b) ct k1 t1 k2 t2 =
    eqTrans (eqCong (\ x -> ap2 gg x (simSubstT k1 t1 k2 t2 b))
                     (simSubstT_pres a (closed_ap2_inv_l_R gg a b ct) k1 t1 k2 t2))
            (eqCong (ap2 gg a)
                     (simSubstT_pres b (closed_ap2_inv_r_R gg a b ct) k1 t1 k2 t2))

------------------------------------------------------------------------
-- Phase 1B Step 6 -- thm12_R .
--
-- The R-case of Theorem 12 (universal in X, Y : Term ; no Closed) :
--
--   thm12_R :
--     (g : Fun1) (h1 h2 : Fun2)
--     (Df_g_F1 : Fun1) (Df_h1_F2 Df_h2_F2 : Fun2)
--     (ih_g  : (X : Term) -> Deriv (eqF (thmT (ap1 Df_g_F1 X))  (codeFTeq1 g X)))
--     (ih_h1 : (A B : Term) -> Deriv (eqF (thmT (ap2 Df_h1_F2 A B)) (codeFTeq2 h1 A B)))
--     (ih_h2 : (A B : Term) -> Deriv (eqF (thmT (ap2 Df_h2_F2 A B)) (codeFTeq2 h2 A B)))
--     (X Y : Term) ->
--     Deriv (eqF (thmT (Dg ... X Y)) (codeFTeq2 (R g h1 h2) X Y))
--
-- Construction.  ruleIndNat + ruleInst2 .  substF / simSubstF gets stuck
-- at opaque  codeFun2 (R g h1 h2)  positions inside  codeFTeq2 ; we
-- use the closedAt + simSubstT_pres bridges to relate
--   substF 0 r P_univ           with  P_concrete_at r
--   simSubstF 0 Y 1 X P_univ    with  the final goal eqF .

thm12_R :
  (g : Fun1) (h1 h2 : Fun2)
  (Df_g_F1 : Fun1) (Df_h1_F2 Df_h2_F2 : Fun2)
  (ih_g  : (X : Term) ->
             Deriv (eqF (ap1 thmT (ap1 Df_g_F1 X)) (codeFTeq1 g X)))
  (ih_h1 : (A B : Term) ->
             Deriv (eqF (ap1 thmT (ap2 Df_h1_F2 A B)) (codeFTeq2 h1 A B)))
  (ih_h2 : (A B : Term) ->
             Deriv (eqF (ap1 thmT (ap2 Df_h2_F2 A B)) (codeFTeq2 h2 A B)))
  (X Y : Term) ->
  Deriv (eqF (ap1 thmT (ap2 (Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2) X Y))
              (codeFTeq2 (R g h1 h2) X Y))
thm12_R g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 ih_g ih_h1 ih_h2 X Y =
  let
    Dg' : Fun2
    Dg' = Dg g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2

    Df_g_inst : Term -> Term
    Df_g_inst Z = ap1 Df_g_F1 Z

    a_var : Term
    a_var = var (suc zero)

    n_var : Term
    n_var = var zero

    -- The universal hypothesis  P_univ  with  a_var = var 1  and  n_var = var 0 .
    P_univ : Formula
    P_univ = eqF (ap1 thmT (ap2 Dg' a_var n_var))
                  (codeFTeq2 (R g h1 h2) a_var n_var)

    -- The "concrete" formula obtained from P_univ by replacing  n_var  with  r .
    P_concrete_at : Term -> Formula
    P_concrete_at r =
      eqF (ap1 thmT (ap2 Dg' a_var r))
           (codeFTeq2 (R g h1 h2) a_var r)

    -------------------------------------------------------------
    -- bridge_codeFTeq2 r :  substT 0 r (codeFTeq2 (R g h1 h2) a_var n_var)
    --                      = codeFTeq2 (R g h1 h2) a_var r .
    -- Single closedAt witness at the  codeFun2 (R g h1 h2)  position ;
    -- structural Pair-of-Pair lift via Eq.cong .
    -------------------------------------------------------------
    bridge_codeFTeq2 :
      (r : Term) ->
      Eq (substT zero r (codeFTeq2 (R g h1 h2) a_var n_var))
         (codeFTeq2 (R g h1 h2) a_var r)
    bridge_codeFTeq2 r =
      eqCong
        (\ X' ->
          ap2 Pair (natCode tag_eq)
            (ap2 Pair (ap2 Pair (natCode tag_ap2)
                          (ap2 Pair X' (ap2 Pair (ap1 num a_var) (ap1 num r))))
                      (ap1 num (ap2 (R g h1 h2) a_var r))))
        (closedAt (codeFun2_closed (R g h1 h2)) zero r)

    formula_eq_at :
      (r : Term) -> Eq (substF zero r P_univ) (P_concrete_at r)
    formula_eq_at r =
      eqCong (\ X' -> eqF (ap1 thmT (ap2 Dg' a_var r)) X')
              (bridge_codeFTeq2 r)

    -------------------------------------------------------------
    -- base_concrete : Deriv (P_concrete_at O) ;
    -- then transport via  eqSym (formula_eq_at O) .
    -------------------------------------------------------------
    base_dg_O_red :
      Deriv (eqF (ap2 Dg' a_var O) (ap1 (baseF1 g h1 h2 Df_g_F1) a_var))
    base_dg_O_red =
      dg_at_O_red g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 a_var

    base_baseF1_eq :
      Deriv (eqF (ap1 (baseF1 g h1 h2 Df_g_F1) a_var)
                  (Df_R_at_O g h1 h2 Df_g_inst a_var))
    base_baseF1_eq = baseF1_eq g h1 h2 Df_g_F1 a_var

    base_dg_to_DfRO :
      Deriv (eqF (ap2 Dg' a_var O) (Df_R_at_O g h1 h2 Df_g_inst a_var))
    base_dg_to_DfRO = ruleTrans base_dg_O_red base_baseF1_eq

    base_thmT_dg_to_DfRO :
      Deriv (eqF (ap1 thmT (ap2 Dg' a_var O))
                  (ap1 thmT (Df_R_at_O g h1 h2 Df_g_inst a_var)))
    base_thmT_dg_to_DfRO = cong1 thmT base_dg_to_DfRO

    base_thmT_R_at_O :
      Deriv (eqF (ap1 thmT (Df_R_at_O g h1 h2 Df_g_inst a_var))
                  (codeFTeq2 (R g h1 h2) a_var O))
    base_thmT_R_at_O = thm12_R_at_O g h1 h2 Df_g_inst ih_g a_var

    base_concrete : Deriv (P_concrete_at O)
    base_concrete = ruleTrans base_thmT_dg_to_DfRO base_thmT_R_at_O

    base_proof : Deriv (substF zero O P_univ)
    base_proof = eqSubst Deriv (eqSym (formula_eq_at O)) base_concrete

    -------------------------------------------------------------
    -- step_proof_imp_substF : transport step_proof_imp through
    --   eqSym (formula_eq_at (ap1 s n_var)) .
    -------------------------------------------------------------
    step_proof_imp_inst :
      Deriv (imp P_univ
        (eqF (ap1 thmT (ap2 Dg' a_var (ap1 s n_var)))
              (codeFTeq2 (R g h1 h2) a_var (ap1 s n_var))))
    step_proof_imp_inst =
      step_proof_imp g h1 h2 Df_g_F1 Df_h1_F2 Df_h2_F2 ih_h1 ih_h2

    step_proof_imp_substF :
      Deriv (imp P_univ (substF zero (ap1 s n_var) P_univ))
    step_proof_imp_substF =
      eqSubst (\ Q -> Deriv (imp P_univ Q))
              (eqSym (formula_eq_at (ap1 s n_var)))
              step_proof_imp_inst

    -------------------------------------------------------------
    -- univ_proof via ruleIndNat .
    -------------------------------------------------------------
    univ_proof : Deriv P_univ
    univ_proof = ruleIndNat zero {P_univ} base_proof step_proof_imp_substF

    -------------------------------------------------------------
    -- thm12_R via ruleInst2 + simSubstF bridge .
    --
    --   simSubstT 0 Y 1 X (var 0) = Y     (natEq 0 0 = true)
    --   simSubstT 0 Y 1 X (var 1) = X     (natEq 0 1 = false ; natEq 1 1 = true)
    -- The codeFun2 (R g h1 h2)  position is simSubst-stable via
    -- simSubstT_pres .
    -------------------------------------------------------------
    bridge_simSubst_codeFTeq2 :
      Eq (simSubstT zero Y (suc zero) X (codeFTeq2 (R g h1 h2) a_var n_var))
         (codeFTeq2 (R g h1 h2) X Y)
    bridge_simSubst_codeFTeq2 =
      eqCong
        (\ X' ->
          ap2 Pair (natCode tag_eq)
            (ap2 Pair (ap2 Pair (natCode tag_ap2)
                          (ap2 Pair X' (ap2 Pair (ap1 num X) (ap1 num Y))))
                      (ap1 num (ap2 (R g h1 h2) X Y))))
        (simSubstT_pres (codeFun2 (R g h1 h2)) (codeFun2_closed (R g h1 h2))
                         zero Y (suc zero) X)

    bridge_simSubstF :
      Eq (simSubstF zero Y (suc zero) X P_univ)
         (eqF (ap1 thmT (ap2 Dg' X Y)) (codeFTeq2 (R g h1 h2) X Y))
    bridge_simSubstF =
      eqCong (\ X' -> eqF (ap1 thmT (ap2 Dg' X Y)) X')
              bridge_simSubst_codeFTeq2

    raw : Deriv (simSubstF zero Y (suc zero) X P_univ)
    raw = ruleInst2 zero Y (suc zero) X refl {P_univ} univ_proof

  in eqSubst Deriv bridge_simSubstF raw
