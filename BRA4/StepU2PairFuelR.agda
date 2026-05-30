{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2PairFuelR -- the algebra of paired_R : Fun2 .
--
-- For a given Fun2-R(g, h1, h2) with completeness sub-bundles  bG, bH1,
-- bH2 , we construct a Fun2  paired_R  whose application to (x, y)
-- yields a Term-level pair  pi (R-value at (x,y)) (fuel at (x,y)) .
--
-- This module proves ONLY the two projection equations:
--
--   Fst_paired_R_eq : ap1 Fst (ap2 paired_R x y) = ap2 (R g h1 h2) x y
--   Snd_paired_R_eq : ap1 Snd (ap2 paired_R x y) = ap2 fuelR_combinator x y
--
-- BRA4.StepU2CorrectR  consumes these to discharge the main R-case
-- completeness Deriv via a small  ruleIndNat 2  proof.
--
-- The Snd equation is AUTOMATIC: we set  fuelR_combinator := Post Snd
-- paired_R  so  axPost  gives the equation directly.  The Fst equation
-- requires  ruleIndNat 2  on  var 2  (= y) with motive  Pform .

module BRA4.StepU2PairFuelR where

open import BRA4.Base
open import BRA4.StepU2
open import BRA4.StepU2CorrectAPI

open import BRA3.Church          using ( pi ; sigma )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq
  ; Post ; axPost )
open import BRA3.Fan             using
  ( Lift1 ; Lift1_eq ; Lift2 ; Lift2_eq ; Fan ; Fan_eq )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.Logic            using ( impTrans ; prependEqLeft ; appendEqRight )

------------------------------------------------------------------------
-- Inner module parametric in g, h1, h2 and the completeness bundles.

module Construct
  (g : Fun1) (h1 h2 : Fun2)
  (bG : Correct1 g) (bH1 : Correct2 h1) (bH2 : Correct2 h2)
  where

  fG : Fun1
  fG = fuelF bG

  fH1 : Fun2
  fH1 = fuelG bH1

  fH2 : Fun2
  fH2 = fuelG bH2

  ----------------------------------------------------------------------
  -- The components of paired_R .

  -- F1 : Fun1 base.    F1(x) = pi (g x) (sigma (constN 1 x) (fG x))
  -- The fuel form  sigma (constN 1 x) (fG x)  matches the  reach_trans-
  -- generated fuel  sigma (ap1 (constN 1) x) (ap1 fG x)  literally.
  F1 : Fun1
  F1 = C pi g (C sigma (constN 1) fG)

  -- F3 : Fun2.    F3(x, y) = pi (h2 x y) (fH2 x y)
  F3 : Fun2
  F3 = Fan h2 fH2 pi

  -- val_next_Fun2 : Fun2.
  --   val_next_Fun2(A, B) = h1 (Fst A) (Fst B)
  --                       = h1 (h2_val) (val_prev)             via Fst's of F3-output and prev pair
  val_next_Fun2 : Fun2
  val_next_Fun2 = Fan (Lift1 Fst) (Lift2 Fst) h1

  -- The constant-1 leaf, as a Fun2:  Lift2 (constN 1) gives  natCode 1 = ap1 s O .
  oneFun2 : Fun2
  oneFun2 = Lift2 (constN 1)

  -- Helper for sigma-combination:  addSigma p q  in Fun2.
  addSigma : Fun2 -> Fun2 -> Fun2
  addSigma p q = Fan p q sigma

  -- Components of  fuel_next_Fun2 .
  fuelH2_proj : Fun2          -- Snd of A  (= fuelH2 x y)
  fuelH2_proj = Lift1 Snd

  fuelPrev_proj : Fun2        -- Snd of B  (= fuel_prev)
  fuelPrev_proj = Lift2 Snd

  -- fuelH1 at (Fst A, Fst B) = fuelH1 (h2_val) (val_prev)
  fuelH1_at_Fun2 : Fun2
  fuelH1_at_Fun2 = Fan (Lift1 Fst) (Lift2 Fst) fH1

  -- The 5-deep sigma sum.
  fuel_next_Fun2 : Fun2
  fuel_next_Fun2 =
    addSigma (addSigma (addSigma (addSigma (addSigma oneFun2 fuelH2_proj) oneFun2)
                                 fuelPrev_proj) oneFun2)
             fuelH1_at_Fun2

  -- F2 : Fun2 step.    F2(A, B) = pi (val_next) (fuel_next)
  F2 : Fun2
  F2 = Fan val_next_Fun2 fuel_next_Fun2 pi

  ----------------------------------------------------------------------
  -- paired_R : Fun2.

  paired_R : Fun2
  paired_R = R F1 F2 F3

  -- The fuel combinator: fuelR_combinator(x, y) = Snd (paired_R x y) .

  fuelR_combinator : Fun2
  fuelR_combinator = Post Snd paired_R

  ----------------------------------------------------------------------
  -- Snd projection equation (automatic via axPost).

  Snd_paired_R_eq : (x y : Term) ->
    Deriv (eqF (ap1 Snd (ap2 paired_R x y)) (ap2 fuelR_combinator x y))
  Snd_paired_R_eq x y = ruleSym (axPost Snd paired_R x y)

  ----------------------------------------------------------------------
  -- Fst projection equation, proved by  ruleIndNat 2  on  var 2  (y).
  --
  --   Pform := eqF (ap1 Fst (ap2 paired_R (var 0) (var 2)))
  --                (ap2 (R g h1 h2) (var 0) (var 2)) .

  private
    Pform : Formula
    Pform = eqF (ap1 Fst (ap2 paired_R (var 0) (var 2)))
                (ap2 (R g h1 h2) (var 0) (var 2))

    ------------------------------------------------------------------
    -- baseCase :  Pform[var 2 := O] .
    --
    --   LHS = Fst (paired_R (var 0) O)
    --       = Fst (F1 (var 0))                 [ax_R_base on paired_R]
    --       = Fst (pi (g (var 0)) (s (fG (var 0))))   [ax_C on F1 = C pi g (compose1U s fG)]
    --       = g (var 0)                         [axFst]
    --   RHS = R g h1 h2 (var 0) O = g (var 0)   [ax_R_base on R]
    baseCase : Deriv (eqF (ap1 Fst (ap2 paired_R (var 0) O))
                          (ap2 (R g h1 h2) (var 0) O))
    baseCase =
      let -- ap2 paired_R (var 0) O = ap1 F1 (var 0)
          e1 : Deriv (eqF (ap2 paired_R (var 0) O) (ap1 F1 (var 0)))
          e1 = ax_R_base F1 F2 F3 (var 0)

          -- ap1 F1 (var 0) = ap2 pi (ap1 g (var 0)) (ap1 (C sigma (constN 1) fG) (var 0))
          e2 : Deriv (eqF (ap1 F1 (var 0))
                          (ap2 pi (ap1 g (var 0)) (ap1 (C sigma (constN 1) fG) (var 0))))
          e2 = ax_C pi g (C sigma (constN 1) fG) (var 0)

          chain_paired : Deriv (eqF (ap2 paired_R (var 0) O)
                                     (ap2 pi (ap1 g (var 0))
                                              (ap1 (C sigma (constN 1) fG) (var 0))))
          chain_paired = ruleTrans e1 e2

          -- Fst (the pair) = ap1 g (var 0)  [axFst]
          eFst : Deriv (eqF (ap1 Fst (ap2 pi (ap1 g (var 0))
                                              (ap1 (C sigma (constN 1) fG) (var 0))))
                            (ap1 g (var 0)))
          eFst = axFst (ap1 g (var 0)) (ap1 (C sigma (constN 1) fG) (var 0))

          lhs_eq : Deriv (eqF (ap1 Fst (ap2 paired_R (var 0) O)) (ap1 g (var 0)))
          lhs_eq = ruleTrans (cong1 Fst chain_paired) eFst

          -- RHS:  R g h1 h2 (var 0) O = ap1 g (var 0)  via ax_R_base.
          rhs_eq : Deriv (eqF (ap2 (R g h1 h2) (var 0) O) (ap1 g (var 0)))
          rhs_eq = ax_R_base g h1 h2 (var 0)
      in ruleTrans lhs_eq (ruleSym rhs_eq)

    ------------------------------------------------------------------
    -- stepCase :  imp Pform (Pform [var 2 := s (var 2)]) .
    --
    -- Hypothesis Pform : Fst (paired_R x y) = R g h1 h2 x y  (at vars 0 = x, 2 = y).
    -- Conclusion       : Fst (paired_R x (s y)) = R g h1 h2 x (s y) .
    --
    -- Chain (independent of hypothesis):
    --   pre  : Fst (paired_R x (s y)) = ap2 h1 (h2 x y) (Fst (paired_R x y))
    --   post : ap2 h1 (h2 x y) (R g h1 h2 x y) = R g h1 h2 x (s y)         [reverse ax_R_step]
    --
    -- And via  ax_eqCongR h1  combined with Pform:
    --   core : imp Pform (ap2 h1 (h2 x y) (Fst (paired_R x y)) = ap2 h1 (h2 x y) (R g h1 h2 x y))
    --
    -- Then prependEqLeft + appendEqRight + impTrans combine.

    -- Abbreviate the universal terms.
    Xvar : Term
    Xvar = var 0
    Yvar : Term
    Yvar = var 2

    -- prev_paired := ap2 paired_R Xvar Yvar
    prev_paired : Term
    prev_paired = ap2 paired_R Xvar Yvar

    h2val : Term
    h2val = ap2 h2 Xvar Yvar

    fuelH2val : Term
    fuelH2val = ap2 fH2 Xvar Yvar

    -- The output of F3 at (Xvar, Yvar) :  pi h2val fuelH2val .
    F3_at : Term
    F3_at = ap2 pi h2val fuelH2val

    -- The lhs of conclusion before any rewrite.
    lhsConcl : Term
    lhsConcl = ap1 Fst (ap2 paired_R Xvar (ap1 s Yvar))

    rhsConcl : Term
    rhsConcl = ap2 (R g h1 h2) Xvar (ap1 s Yvar)

    -- The "pivot" value : h1 (h2val) (Fst prev_paired) .
    pivotLHS : Term
    pivotLHS = ap2 h1 h2val (ap1 Fst prev_paired)

    -- The "pivot" : h1 (h2val) (R g h1 h2 Xvar Yvar) — after hypothesis rewrite.
    pivotRHS : Term
    pivotRHS = ap2 h1 h2val (ap2 (R g h1 h2) Xvar Yvar)

    -- pre : Deriv (eqF lhsConcl pivotLHS) .  Pure rewriting; no hypothesis.
    --
    -- Chain:
    --   ap2 paired_R Xvar (s Yvar) = ap2 F2 (ap2 F3 Xvar Yvar) prev_paired   [ax_R_step on paired_R]
    --   = ap2 F2 F3_at prev_paired                                            [via axFan on F3 + cong]
    --   = ap2 pi (ap2 val_next_Fun2 F3_at prev_paired) (ap2 fuel_next_Fun2 ...)  [via axFan on F2]
    --   Fst (...) = ap2 val_next_Fun2 F3_at prev_paired                         [axFst]
    --   val_next_Fun2 F3_at prev_paired = ap2 h1 (Fst F3_at) (Fst prev_paired)  [Fan + Lift1/Lift2]
    --                                   = ap2 h1 h2val (Fst prev_paired)         [axFst on F3_at]
    pre : Deriv (eqF lhsConcl pivotLHS)
    pre =
      let -- ax_R_step:  paired_R x (s y) = F2 (F3 x y) (paired_R x y)
          eR : Deriv (eqF (ap2 paired_R Xvar (ap1 s Yvar))
                          (ap2 F2 (ap2 F3 Xvar Yvar) prev_paired))
          eR = ax_R_step F1 F2 F3 Xvar Yvar

          -- F3 x y = pi (h2 x y) (fH2 x y)
          eF3 : Deriv (eqF (ap2 F3 Xvar Yvar) F3_at)
          eF3 = Fan_eq h2 fH2 pi Xvar Yvar

          eR2 : Deriv (eqF (ap2 paired_R Xvar (ap1 s Yvar))
                            (ap2 F2 F3_at prev_paired))
          eR2 = ruleTrans eR (congL F2 prev_paired eF3)

          -- F2 (F3_at) prev_paired = ap2 pi (ap2 val_next_Fun2 ...) (ap2 fuel_next_Fun2 ...)
          eF2 : Deriv (eqF (ap2 F2 F3_at prev_paired)
                            (ap2 pi (ap2 val_next_Fun2 F3_at prev_paired)
                                    (ap2 fuel_next_Fun2 F3_at prev_paired)))
          eF2 = Fan_eq val_next_Fun2 fuel_next_Fun2 pi F3_at prev_paired

          eR3 : Deriv (eqF (ap2 paired_R Xvar (ap1 s Yvar))
                            (ap2 pi (ap2 val_next_Fun2 F3_at prev_paired)
                                    (ap2 fuel_next_Fun2 F3_at prev_paired)))
          eR3 = ruleTrans eR2 eF2

          -- Fst of the pi gives ap2 val_next_Fun2 F3_at prev_paired
          eFst1 : Deriv (eqF lhsConcl (ap2 val_next_Fun2 F3_at prev_paired))
          eFst1 = ruleTrans (cong1 Fst eR3)
                            (axFst (ap2 val_next_Fun2 F3_at prev_paired)
                                   (ap2 fuel_next_Fun2 F3_at prev_paired))

          -- val_next_Fun2 F3_at prev_paired = h1 (Lift1 Fst F3_at prev_paired) (Lift2 Fst F3_at prev_paired)
          eVN : Deriv (eqF (ap2 val_next_Fun2 F3_at prev_paired)
                            (ap2 h1 (ap2 (Lift1 Fst) F3_at prev_paired)
                                    (ap2 (Lift2 Fst) F3_at prev_paired)))
          eVN = Fan_eq (Lift1 Fst) (Lift2 Fst) h1 F3_at prev_paired

          -- Lift1 Fst F3_at prev_paired = ap1 Fst F3_at
          eL1 : Deriv (eqF (ap2 (Lift1 Fst) F3_at prev_paired) (ap1 Fst F3_at))
          eL1 = Lift1_eq Fst F3_at prev_paired

          -- ap1 Fst F3_at = h2val   (F3_at = pi h2val fuelH2val ; axFst)
          eFstF3 : Deriv (eqF (ap1 Fst F3_at) h2val)
          eFstF3 = axFst h2val fuelH2val

          -- Combined: Lift1 Fst F3_at prev_paired = h2val
          eL1' : Deriv (eqF (ap2 (Lift1 Fst) F3_at prev_paired) h2val)
          eL1' = ruleTrans eL1 eFstF3

          -- Lift2 Fst F3_at prev_paired = ap1 Fst prev_paired
          eL2 : Deriv (eqF (ap2 (Lift2 Fst) F3_at prev_paired) (ap1 Fst prev_paired))
          eL2 = Lift2_eq Fst F3_at prev_paired

          -- Combine:  ap2 h1 (Lift1 Fst ...) (Lift2 Fst ...) = ap2 h1 h2val (ap1 Fst prev_paired)
          eH1 : Deriv (eqF (ap2 h1 (ap2 (Lift1 Fst) F3_at prev_paired)
                                   (ap2 (Lift2 Fst) F3_at prev_paired))
                            (ap2 h1 h2val (ap1 Fst prev_paired)))
          eH1 = ruleTrans (congL h1 (ap2 (Lift2 Fst) F3_at prev_paired) eL1')
                          (congR h1 h2val eL2)

          -- Combined: val_next_Fun2 F3_at prev_paired = pivotLHS
          eVN2 : Deriv (eqF (ap2 val_next_Fun2 F3_at prev_paired) pivotLHS)
          eVN2 = ruleTrans eVN eH1
      in ruleTrans eFst1 eVN2

    -- post : Deriv (eqF pivotRHS rhsConcl) .
    -- pivotRHS = h1 (h2val) (R g h1 h2 x y), rhsConcl = R g h1 h2 x (s y).
    -- By ax_R_step (reversed):  R g h1 h2 x (s y) = h1 (h2 x y) (R g h1 h2 x y) = pivotRHS .
    post : Deriv (eqF pivotRHS rhsConcl)
    post = ruleSym (ax_R_step g h1 h2 Xvar Yvar)

    -- core : imp Pform (eqF pivotLHS pivotRHS)
    --   via ax_eqCongR h1 (Fst prev_paired) (R g h1 h2 x y) h2val.
    core : Deriv (imp Pform (eqF pivotLHS pivotRHS))
    core = ax_eqCongR h1 (ap1 Fst prev_paired) (ap2 (R g h1 h2) Xvar Yvar) h2val

  private
    stepCase : Deriv (imp Pform (eqF lhsConcl rhsConcl))
    stepCase =
      let s1 : Deriv (imp (eqF pivotLHS pivotRHS) (eqF lhsConcl pivotRHS))
          s1 = prependEqLeft lhsConcl pivotLHS pivotRHS pre

          s2 : Deriv (imp Pform (eqF lhsConcl pivotRHS))
          s2 = impTrans core s1

          s3 : Deriv (imp (eqF lhsConcl pivotRHS) (eqF lhsConcl rhsConcl))
          s3 = appendEqRight lhsConcl pivotRHS rhsConcl post
      in impTrans s2 s3

    universal : Deriv Pform
    universal = ruleIndNat 2 {P = Pform} baseCase stepCase

  ----------------------------------------------------------------------
  -- Specialise  var 0 := x , var 2 := y .

  Fst_paired_R_eq : (x y : Term) ->
    Deriv (eqF (ap1 Fst (ap2 paired_R x y)) (ap2 (R g h1 h2) x y))
  Fst_paired_R_eq x y =
    ruleInst2 zero x (suc (suc zero)) y refl universal

  ----------------------------------------------------------------------
  -- Snd-projection at base and step: explicit forms of the fuel.

  -- Snd (paired_R x O) = sigma (ap1 (constN 1) x) (ap1 fG x) .
  Snd_paired_R_at_O : (x : Term) ->
    Deriv (eqF (ap1 Snd (ap2 paired_R x O))
                (ap2 sigma (ap1 (constN 1) x) (ap1 fG x)))
  Snd_paired_R_at_O x =
    let -- ap2 paired_R x O = ap1 F1 x
        e1 : Deriv (eqF (ap2 paired_R x O) (ap1 F1 x))
        e1 = ax_R_base F1 F2 F3 x

        -- ap1 F1 x = pi (g x) (C sigma (constN 1) fG (x))
        e2 : Deriv (eqF (ap1 F1 x)
                        (ap2 pi (ap1 g x) (ap1 (C sigma (constN 1) fG) x)))
        e2 = ax_C pi g (C sigma (constN 1) fG) x

        chain : Deriv (eqF (ap2 paired_R x O)
                            (ap2 pi (ap1 g x) (ap1 (C sigma (constN 1) fG) x)))
        chain = ruleTrans e1 e2

        eSnd : Deriv (eqF (ap1 Snd (ap2 pi (ap1 g x) (ap1 (C sigma (constN 1) fG) x)))
                          (ap1 (C sigma (constN 1) fG) x))
        eSnd = axSnd (ap1 g x) (ap1 (C sigma (constN 1) fG) x)

        -- ap1 (C sigma (constN 1) fG) x = ap2 sigma (ap1 (constN 1) x) (ap1 fG x)
        eC : Deriv (eqF (ap1 (C sigma (constN 1) fG) x)
                         (ap2 sigma (ap1 (constN 1) x) (ap1 fG x)))
        eC = ax_C sigma (constN 1) fG x

    in ruleTrans (cong1 Snd chain) (ruleTrans eSnd eC)

  -- Snd (paired_R x (s y)) = sigma (sigma (sigma (sigma (sigma  ONE  fH2_xy)  ONE)  Snd-prev) ONE) (fH1 h2val val_prev)
  --
  -- where ONE = ap1 (constN 1) (ap2 paired_R x y) = Lift2 (constN 1) (F3-output) (paired_R prev).
  -- We don't unfold ONE here; CorrectR will bridge ONE = ap1 (constN 1) x via constN_eq.

  -- The fuel-next expression at args (A, B).
  fuel_next_at : (A B : Term) -> Term
  fuel_next_at A B = ap2 fuel_next_Fun2 A B

  -- The "one" expression at args (A, B) under  Lift2 (constN 1) :
  oneTerm_at : (A B : Term) -> Term
  oneTerm_at A B = ap1 (constN 1) B

  -- Snd (paired_R x (s y)) = ap2 fuel_next_Fun2 (F3(x, y)) (paired_R x y) .
  Snd_paired_R_at_s : (x y : Term) ->
    Deriv (eqF (ap1 Snd (ap2 paired_R x (ap1 s y)))
                (ap2 fuel_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y)))
  Snd_paired_R_at_s x y =
    let -- ax_R_step : paired_R x (s y) = F2 (F3 x y) (paired_R x y)
        eR : Deriv (eqF (ap2 paired_R x (ap1 s y))
                         (ap2 F2 (ap2 F3 x y) (ap2 paired_R x y)))
        eR = ax_R_step F1 F2 F3 x y

        -- F2 (F3 x y) (paired_R x y) = pi (val_next ...) (fuel_next ...)
        eF2 : Deriv (eqF (ap2 F2 (ap2 F3 x y) (ap2 paired_R x y))
                          (ap2 pi (ap2 val_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))
                                  (ap2 fuel_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))))
        eF2 = Fan_eq val_next_Fun2 fuel_next_Fun2 pi (ap2 F3 x y) (ap2 paired_R x y)

        eSnd : Deriv (eqF (ap1 Snd (ap2 pi (ap2 val_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))
                                            (ap2 fuel_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))))
                           (ap2 fuel_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y)))
        eSnd = axSnd (ap2 val_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))
                     (ap2 fuel_next_Fun2 (ap2 F3 x y) (ap2 paired_R x y))
    in ruleTrans (cong1 Snd (ruleTrans eR eF2)) eSnd
