{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefBigConjNumBridge -- the NUMERAL bridge connecting the framework's
-- proven formula  KdefBigConj M enum (natCode r)  to the recogniser's
-- num-raw code-builder  KcodeBC enum (var zero) M  (T4.KdefBigConjRecog).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   numBridge :
--     (M r : Nat) ->
--     Deriv (eqF (codeFormula (KdefBigConj M enum (natCode r)))
--                (ap1 (KcodeBC enum (var zero) M) (natCode r)))
--
-- The two terms have IDENTICAL Pair-tree structure EXCEPT at the subject
-- leaf of each of the  M+1  per-program conjuncts : the framework's
-- codeFormula  carries  codeTerm (natCode r)  in the  ap1 s -output slot,
-- while  KcodeBC  ( being num-raw, for an arbitrary subject ) carries
--  ap1 num (natCode r) .   The two agree on numerals by
--  T4.IsNat.num_eq_code  ( num t = codeTerm t  for  isNat t ), lifted
-- through the Pair structure by  congL / congR  and through the  cAnd
-- spine by induction on  M .
--
-- This is the "num-raw subject install at the numeral" the dayClash
-- handoff (plan A's better sub-option / plan B's prerequisite) calls for,
-- done as a downstream code-bridge so the verified framework
-- ( StagePredF / StepFrontEnd / StageBaseFormula ) is NOT re-touched.

module T4.KdefBigConjNumBridge where

open import T4.Base
open import T4.Tags using ( tag_neg ; tag_eq ; tag_imp ; tag_ap1 ; tag_s )
open import T4.Code using ( codeFormula ; codeTerm )
open import T4.Num  using ( num )
open import T4.IsNat using ( num_eq_code )
open import T4.NumContract using ( isNat_natCode )
open import T4.SurpriseG2.KdefBigConj using ( KdefBigConj ; perProgNeg )
open import T4.KdefBigConjRecog
  using ( KBCcode ; perProgNegCodeBC ; lhsCode
        ; KcodeBC ; KcodeBC_eval )

open import BRA3.PairAlgebra using ( Pair )

module _ (enum : Fun1) where

  ----------------------------------------------------------------------
  -- The subject-leaf equality :  codeTerm (natCode r) = ap1 num (natCode r) .

  subjEq : (r : Nat) -> Deriv (eqF (codeTerm (natCode r)) (ap1 num (natCode r)))
  subjEq r = ruleSym (num_eq_code (natCode r) (isNat_natCode r))

  ----------------------------------------------------------------------
  -- Per-conjunct bridge :  codeFormula (perProgNeg enum (natCode r) k)
  --                       = perProgNegCodeBC enum (var zero) (natCode r) k .
  -- Identical except the subject leaf, nested 5 deep under
  --   Pair tag_neg (Pair tag_eq (Pair (lhsCode enum (var zero) k)
  --     (Pair tag_ap1 (Pair tag_s [_])))) .

  perProgBridge :
    (r k : Nat) ->
    Deriv (eqF (codeFormula (perProgNeg enum (natCode r) k))
               (perProgNegCodeBC enum (var zero) (natCode r) k))
  perProgBridge r k =
    congR Pair (natCode tag_neg)
      (congR Pair (natCode tag_eq)
        (congR Pair (lhsCode enum (var zero) k)
          (congR Pair (natCode tag_ap1)
            (congR Pair (natCode tag_s) (subjEq r)))))

  ----------------------------------------------------------------------
  -- The full bridge, by induction on the conjunct count  M .

  codeFormToKBC :
    (M r : Nat) ->
    Deriv (eqF (codeFormula (KdefBigConj M enum (natCode r)))
               (KBCcode enum (var zero) M (natCode r)))
  codeFormToKBC zero    r = perProgBridge r zero
  codeFormToKBC (suc M) r =
    let a : Term
        a = natCode r

        e_head : Deriv (eqF (codeFormula (perProgNeg enum a (suc M)))
                            (perProgNegCodeBC enum (var zero) a (suc M)))
        e_head = perProgBridge r (suc M)

        e_tail : Deriv (eqF (codeFormula (KdefBigConj M enum a))
                            (KBCcode enum (var zero) M a))
        e_tail = codeFormToKBC M r

        -- the tail wrapper  Pair tag_neg [codeFormula (KdefBigConj M)] .
        TT : Term
        TT = ap2 Pair (natCode tag_neg) (codeFormula (KdefBigConj M enum a))

        innerHead :
          Deriv (eqF (ap2 Pair (codeFormula (perProgNeg enum a (suc M))) TT)
                     (ap2 Pair (perProgNegCodeBC enum (var zero) a (suc M)) TT))
        innerHead = congL Pair TT e_head

        innerTail :
          Deriv (eqF (ap2 Pair (perProgNegCodeBC enum (var zero) a (suc M)) TT)
                     (ap2 Pair (perProgNegCodeBC enum (var zero) a (suc M))
                        (ap2 Pair (natCode tag_neg) (KBCcode enum (var zero) M a))))
        innerTail =
          congR Pair (perProgNegCodeBC enum (var zero) a (suc M))
            (congR Pair (natCode tag_neg) e_tail)

        inner :
          Deriv (eqF (ap2 Pair (codeFormula (perProgNeg enum a (suc M))) TT)
                     (ap2 Pair (perProgNegCodeBC enum (var zero) a (suc M))
                        (ap2 Pair (natCode tag_neg) (KBCcode enum (var zero) M a))))
        inner = ruleTrans innerHead innerTail
    in congR Pair (natCode tag_neg)
         (congR Pair (natCode tag_imp) inner)

  ----------------------------------------------------------------------
  -- The headline bridge :  codeFormula(...) = ap1 (KcodeBC enum (var zero) M) (natCode r) .

  numBridge :
    (M r : Nat) ->
    Deriv (eqF (codeFormula (KdefBigConj M enum (natCode r)))
               (ap1 (KcodeBC enum (var zero) M) (natCode r)))
  numBridge M r =
    ruleTrans (codeFormToKBC M r) (ruleSym (KcodeBC_eval enum (var zero) M (natCode r)))
