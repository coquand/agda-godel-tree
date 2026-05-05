{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12Schematic
--
-- Structural recursion on Fun1 / Fun2 producing SCHEMATIC Theorem 12
-- results: a Deriv P_schematic with var 0 (or var 0, var 1) free.
--
-- Mirrors  BRA.Thm12.FromBridges  but at the schematic level, where
-- closure args (IfLf_xeq1, TreeEq_xeq1) trivially hold by  refl
-- because all internal sub-terms only mention  var 0  and  var 1
-- (no IfLf-style "free var captured" issue).
--
-- Atomic constructors: dispatch to existing schematic Th12_F1_*,
-- Th12_F2_* lemmas.  Composite constructors: dispatch to the existing
-- per-case modules ( Th12LiftCase , Th12CompCase , Th12Comp2Case ,
-- Th12FanCase , Th12PostCase , Th12TreeRecInternal.Construction ),
-- supplying universal IH derived from schematic IH via a
-- closed-combinator transport (the only closure needed: thClosed +
-- Fun1_closed / Fun2_closed -- both already proved).
--
-- Output:  thm12_F1_schematic, thm12_F2_schematic  closed total
-- functions (no postulates, no module parameters).

module BRA.Thm12Schematic where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor          using (cor)

open import BRA.Thm.ThmT     using (thmT ; thClosed)
open import BRA.SubstClosure using (Fun1_closed ; Fun2_closed ; subst_reify)

open import BRA.Thm12
  using (Thm12_F1_Result ; Thm12_F2_Result
       ; codeFTeq1 ; codeFTeq2 ; mkR1 ; mkR2)

------------------------------------------------------------------------
-- Helper: from a SCHEMATIC Deriv at  (var 0)  for a singular functor,
-- derive the UNIVERSAL  (x : Term) -> Deriv  form via ruleInst +
-- closed-combinator transport.
--
-- The ONLY closures needed are:
--   * thClosed         : substF1 k r thmT = thmT       (already proved).
--   * Fun1_closed Df   : substF1 k r Df   = Df         (already proved).
--   * Fun1_closed f    : substF1 k r f    = f          (already proved).
--   * Fun1_closed cor  : substF1 k r cor  = cor        (already proved).
--   * subst_reify  for closed Tree constants            (already proved).
--
-- No IfLf-style closure required.

private

  ----------------------------------------------------------------------
  -- subst zero x (codeFTeq1 f (var 0)) = codeFTeq1 f x .
  --
  -- Proof: codeFTeq1 f (var 0) is built from ap2 Pair, reify (closed
  -- Trees), and ap1 cor / ap1 f at  var 0 .  subst zero x distributes
  -- through ap2/ap1 and:
  --   * leaves  Pair  invariant (definitional: substF2 zero x Pair = Pair).
  --   * leaves  reify tagAp1  /  reify (codeF1 f)  invariant (subst_reify).
  --   * rewrites  ap1 cor (var 0)   to  ap1 cor x          (Fun1_closed cor).
  --   * rewrites  ap1 cor (ap1 f (var 0))  to  ap1 cor (ap1 f x)
  --                                              (Fun1_closed cor + Fun1_closed f).

  codeFTeq1_subst : (f : Fun1) (x : Term) ->
    Eq (subst zero x (codeFTeq1 f (var zero))) (codeFTeq1 f x)
  codeFTeq1_subst f x =
    let
      -- Pieces we'll combine:
      eqTagAp1 : Eq (subst zero x (reify tagAp1)) (reify tagAp1)
      eqTagAp1 = subst_reify zero x tagAp1

      eqCodeF1f : Eq (subst zero x (reify (codeF1 f))) (reify (codeF1 f))
      eqCodeF1f = subst_reify zero x (codeF1 f)

      eqCor : Eq (substF1 zero x cor) cor
      eqCor = Fun1_closed zero x cor

      eqF : Eq (substF1 zero x f) f
      eqF = Fun1_closed zero x f

      -- ap1 cor (var 0)  →  ap1 cor x .
      -- subst zero x (ap1 cor (var 0))
      --   = ap1 (substF1 zero x cor) (subst zero x (var 0))     [subst on ap1]
      --   = ap1 (substF1 zero x cor) x                          [subst zero x (var 0) = x]
      -- Then eqCong on ap1 with eqCor.
      eqCorVar0 :
        Eq (subst zero x (ap1 cor (var zero))) (ap1 cor x)
      eqCorVar0 = eqCong (\ F -> ap1 F x) eqCor

      -- ap1 cor (ap1 f (var 0))  →  ap1 cor (ap1 f x) .
      eqCorFVar0 :
        Eq (subst zero x (ap1 cor (ap1 f (var zero)))) (ap1 cor (ap1 f x))
      eqCorFVar0 =
        eqCong2 (\ F G -> ap1 F (ap1 G x)) eqCor eqF

      -- inner Pair: ap2 Pair tagAp1 (ap2 Pair codeF1f (cor (var 0)))
      -- After subst, all three pieces transform:
      --   subst tagAp1   →  tagAp1     [eqTagAp1]
      --   subst codeF1f  →  codeF1f    [eqCodeF1f]
      --   subst (cor (var 0)) →  cor x [eqCorVar0]
      eqInnerPair :
        Eq (subst zero x
              (ap2 Pair (reify tagAp1)
                        (ap2 Pair (reify (codeF1 f)) (ap1 cor (var zero)))))
           (ap2 Pair (reify tagAp1)
                     (ap2 Pair (reify (codeF1 f)) (ap1 cor x)))
      eqInnerPair =
        eqCong3 (\ A B C -> ap2 Pair A (ap2 Pair B C))
                eqTagAp1 eqCodeF1f eqCorVar0

      -- Final: ap2 Pair (innerPair) (ap1 cor (ap1 f (var 0)))
      -- After subst, both halves transform.
    in
      eqCong2 (\ A B -> ap2 Pair A B) eqInnerPair eqCorFVar0

  ----------------------------------------------------------------------
  -- LHS substitution: subst zero x (ap1 thmT (ap1 Df (var 0))) = ap1 thmT (ap1 Df x).
  --
  -- subst zero x (ap1 thmT (ap1 Df (var 0)))
  --   = ap1 (substF1 zero x thmT) (subst zero x (ap1 Df (var 0)))
  --   = ap1 (substF1 zero x thmT) (ap1 (substF1 zero x Df) (subst zero x (var 0)))
  --   = ap1 (substF1 zero x thmT) (ap1 (substF1 zero x Df) x)
  -- After eqSubst with thClosed and Fun1_closed Df: ap1 thmT (ap1 Df x).

  lhs_subst_F1 : (Df : Fun1) (x : Term) ->
    Eq (subst zero x (ap1 thmT (ap1 Df (var zero)))) (ap1 thmT (ap1 Df x))
  lhs_subst_F1 Df x =
    let eqTh : Eq (substF1 zero x thmT) thmT
        eqTh = thClosed zero x

        eqDf : Eq (substF1 zero x Df) Df
        eqDf = Fun1_closed zero x Df

    in eqCong2 (\ A B -> ap1 A (ap1 B x)) eqTh eqDf

------------------------------------------------------------------------
-- The converter.

schematicToUniversal_F1 :
  (f Df : Fun1) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 Df (var zero))) (codeFTeq1 f (var zero)))) ->
  (x : Term) -> Deriv (atomic (eqn (ap1 thmT (ap1 Df x)) (codeFTeq1 f x)))
schematicToUniversal_F1 f Df proof_at_var0 x =
  let
    inst : Deriv (atomic (eqn (subst zero x (ap1 thmT (ap1 Df (var zero))))
                              (subst zero x (codeFTeq1 f (var zero)))))
    inst = ruleInst zero x proof_at_var0

    lhs_eq = lhs_subst_F1 Df x
    rhs_eq = codeFTeq1_subst f x

  in eqSubst (\ EQ -> Deriv (atomic EQ)) (eqCong2 eqn lhs_eq rhs_eq) inst
