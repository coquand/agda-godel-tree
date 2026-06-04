{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ImpExtras -- additional Carneiro-lifted (imp P) combinators that
-- compose ImpHelpers + closed BRA3 Hilbert primitives.
--
-- Used by KdefRecogImp, FirstHitImp, ChaitinG1DischargeKdefImp etc.

module T4.ImpExtras where

open import T4.Base
open import T4.Code        using ( falseF )

open import T4.Thm12.ImpHelpers
  using ( impLift ; impMp )
open import T4.Counting        using ( impFalseToNeg_imp )

open import BRA3.Logic           using ( impTrans )
open import BRA3.Contrapositive  using ( DNE ; bComb ; liftP ; axExFalso ; axContrapos )

------------------------------------------------------------------------
-- imp_compI :  imp-lifted compI .
--
-- Given F : imp Rf (imp X Y)  and  G : imp Rf (imp Y W) , produce
--      H : imp Rf (imp X W) .
--
-- Derived from axK + axS via two impTrans steps.

imp_compI :
  {Rf X Y W : Formula} ->
  Deriv (imp Rf (imp X Y)) -> Deriv (imp Rf (imp Y W)) ->
  Deriv (imp Rf (imp X W))
imp_compI {Rf} {X} {Y} {W} F G =
  let G' : Deriv (imp Rf (imp X (imp Y W)))
      G' = impTrans G (axK (imp Y W) X)
      G'' : Deriv (imp Rf (imp (imp X Y) (imp X W)))
      G'' = impTrans G' (axS X Y W)
  in impMp {Rf} G'' F

------------------------------------------------------------------------
-- imp2_mp :  two-level imp-lifted modus ponens.
--
-- Given F : imp Rf (imp P (imp X Y))  and  G : imp Rf (imp P X) , produce
--       H : imp Rf (imp P Y) .

imp2_mp :
  {Rf P X Y : Formula} ->
  Deriv (imp Rf (imp P (imp X Y))) ->
  Deriv (imp Rf (imp P X)) ->
  Deriv (imp Rf (imp P Y))
imp2_mp {Rf} {P} {X} {Y} F G =
  impMp {Rf} (impMp {Rf} (impLift {Rf} (axS P X Y)) F) G

------------------------------------------------------------------------
-- imp_negIntro :  Carneiro-lifted  negIntro .
--
-- Given F : imp Rf (imp P Q)  and  G : imp Rf (imp P (neg Q)) ,
-- produce H : imp Rf (neg P) .
--
-- Original (PHP.agda):
--   negIntro P Q h1 h2 =
--     let pf : Deriv (imp P falseF)
--         pf = bComb (bComb (liftP P (axExFalso Q falseF)) h1) h2
--     in impFalseToNeg P pf
--
-- We re-derive the chain under  imp Rf .

imp_negIntro :
  (Rf P Q : Formula) ->
  Deriv (imp Rf (imp P Q)) -> Deriv (imp Rf (imp P (neg Q))) ->
  Deriv (imp Rf (neg P))
imp_negIntro Rf P Q h1_imp h2_imp =
  let -- The closed "double-axExFalso" axiom:
      --   imp Q (imp (neg Q) falseF)  -- this is axExFalso Q falseF.
      ex_ax : Deriv (imp Q (imp (neg Q) falseF))
      ex_ax = axExFalso Q falseF

      -- Lift to imp P:  imp P (imp Q (imp (neg Q) falseF))  -- closed.
      ex_axP : Deriv (imp P (imp Q (imp (neg Q) falseF)))
      ex_axP = liftP P ex_ax

      -- Imp-lift further to imp Rf.
      ex_ax_imp : Deriv (imp Rf (imp P (imp Q (imp (neg Q) falseF))))
      ex_ax_imp = impLift {Rf} ex_axP

      -- Apply h1_imp to discharge Q under imp P.
      step1 : Deriv (imp Rf (imp P (imp (neg Q) falseF)))
      step1 = imp2_mp {Rf} {P} {Q} {imp (neg Q) falseF} ex_ax_imp h1_imp

      -- Apply h2_imp to discharge (neg Q).
      step2 : Deriv (imp Rf (imp P falseF))
      step2 = imp2_mp {Rf} {P} {neg Q} {falseF} step1 h2_imp

      -- impFalseToNeg : imp (imp P falseF) (neg P).
  in impMp {Rf} (impLift {Rf} (impFalseToNeg_imp P)) step2

------------------------------------------------------------------------
-- imp_byCases :  Carneiro-lifted  byCases .
--
-- Given h1_imp : imp Rf (imp A Goal)  and  h2_imp : imp Rf (imp (neg A) Goal) ,
-- produce Deriv (imp Rf Goal) .

imp_byCases :
  (Rf A Goal : Formula) ->
  Deriv (imp Rf (imp A Goal)) -> Deriv (imp Rf (imp (neg A) Goal)) ->
  Deriv (imp Rf Goal)
imp_byCases Rf A Goal h1_imp h2_imp =
  let e1_imp : Deriv (imp Rf (imp (neg Goal) (neg A)))
      e1_imp = impMp {Rf} (impLift {Rf} (axContrapos A Goal)) h1_imp

      e2_imp : Deriv (imp Rf (imp (neg Goal) (neg (neg A))))
      e2_imp = impMp {Rf} (impLift {Rf} (axContrapos (neg A) Goal)) h2_imp

      nng_imp : Deriv (imp Rf (neg (neg Goal)))
      nng_imp = imp_negIntro Rf (neg Goal) (neg A) e1_imp e2_imp

  in impMp {Rf} (impLift {Rf} (DNE Goal)) nng_imp

------------------------------------------------------------------------
-- imp_impTrans :  Carneiro-lifted  impTrans  (transitivity of  imp ).
--
-- Given F : imp Rf (imp A B)  and  G : imp Rf (imp B C) , produce
--       H : imp Rf (imp A C) .
--
-- (Synonym of  imp_compI ; provided under this name for readability.)

imp_impTrans :
  {Rf A B C : Formula} ->
  Deriv (imp Rf (imp A B)) -> Deriv (imp Rf (imp B C)) ->
  Deriv (imp Rf (imp A C))
imp_impTrans = imp_compI

------------------------------------------------------------------------
-- imp_eqTrans_imp :  implicit-args alias for  impEqTrans .
--
-- The explicit Term args of  impEqTrans  force Agda to unfold heavy
-- Term expressions during unification.  This implicit-args form lets
-- Agda infer  a, b, c  cheaply from the input Deriv types -- avoiding
-- the slow-typecheck pattern flagged by
-- feedback_slow_typecheck_means_abstract_constants .

imp_eqTrans_imp :
  {Rf : Formula} {a b c : Term} ->
  Deriv (imp Rf (eqF a b)) -> Deriv (imp Rf (eqF b c)) ->
  Deriv (imp Rf (eqF a c))
imp_eqTrans_imp {Rf} {a} {b} {c} = T4.Thm12.ImpHelpers.impEqTrans {Rf} a b c
  where import T4.Thm12.ImpHelpers
