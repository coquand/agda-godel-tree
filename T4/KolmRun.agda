{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmRun -- the Kolmogorov upper bound, RUN form:
--
--   for every x there is a program number p and a fuel N with
--     * p < 3 ^ (nodes (mcode1 (horner (digits3 x))) + 1)      -- p is short
--     * runProgN (natCode p) (natCode N) = s (natCode x)        -- p describes x
--
-- p = diagRank (mcode1 (horner (digits3 x))) = rank (treeToDigits ...) .
-- The program is the base-3 Horner code for x; its run is discharged by the
-- universal-machine correctness theorem evalU_correct_num, and the size by the
-- honest combinatorial bound n0_lt_pow3.  The "nodes ... = O(log_3 x)" reading
-- of the bound is the separate size file.

module T4.KolmRun where

open import T4.Base
open import T4.EvalUCorrect using ( EvalsTo ; fuel ; ev ; evalN1 ; evalN1_sound
                                  ; evalU_correct_num )
open import T4.EvalUEval    using ( evalU )
open import T4.EvalU        using ( mcode1 )
open import T4.ParseN       using ( runProgN ; diagRank ; runProgN_at_diag )
open import T4.McodeInAlph  using ( inAlph_mcode1 )
open import T4.TreeDigitsSize using ( pow3 ; n0_lt_pow3 )
open import T4.ProgEnc        using ( nodes )
open import BRA3.RuleInst2   using ( NatLe )
open import T4.KolmHorner    using ( horner ; horner_correct )
open import T4.KolmDigits    using ( digits3 ; digits3_correct )

------------------------------------------------------------------------
-- Local pair / sigma (the project defines these per-file).

record Sg (A : Set) (B : A -> Set) : Set where
  constructor sg
  field
    fstS : A
    sndS : B fstS

record Pr (A B : Set) : Set where
  constructor pr
  field
    fstP : A
    sndP : B

------------------------------------------------------------------------
-- The bound.

-- "program p, fuel N, describes x" :  runProgN (natCode p) (natCode N) = s (natCode x).
Describes : Nat -> Nat -> Nat -> Set
Describes p N x =
  Deriv (eqF (ap2 runProgN (natCode p) (natCode N)) (ap1 s (natCode x)))

kolmRun :
  (x : Nat) ->
  Sg Nat (\ p ->
    Pr (NatLe (suc p) (pow3 (suc (nodes (mcode1 (horner (digits3 x)))))))
       (Sg Nat (\ N -> Describes p N x)))
kolmRun x =
  let fx : Fun1
      fx = horner (digits3 x)

      gL : Term
      gL = mcode1 fx

      p : Nat
      p = diagRank gL

      -- value:  ap1 fx O = natCode x .
      valueEq : Deriv (eqF (ap1 fx O) (natCode x))
      valueEq =
        eqSubst (\ m -> Deriv (eqF (ap1 fx O) (natCode m)))
                (digits3_correct x)
                (horner_correct (digits3 x))

      -- universal-machine run:  evalU gL (natCode N) = s (natCode (evalN1 fx 0)) .
      et : EvalsTo gL (ap1 s (natCode (evalN1 fx zero)))
      et = evalU_correct_num fx

      N : Nat
      N = fuel et

      -- s (natCode (evalN1 fx 0)) = s (natCode x)  [evalN1_sound + valueEq ;
      --   natCode zero reduces to O].
      valEq2 : Deriv (eqF (natCode (evalN1 fx zero)) (natCode x))
      valEq2 = ruleTrans (evalN1_sound fx zero) valueEq

      evalU_eq : Deriv (eqF (ap2 evalU gL (natCode N)) (ap1 s (natCode x)))
      evalU_eq = ruleTrans (ev et) (cong1 s valEq2)

      -- runProgN at the diagonal program number = evalU gL .
      runEq : Deriv (eqF (ap2 runProgN (natCode p) (natCode N)) (ap2 evalU gL (natCode N)))
      runEq = runProgN_at_diag gL (inAlph_mcode1 fx) (natCode N)

      finalRun : Describes p N x
      finalRun = ruleTrans runEq evalU_eq

      -- size:  p = rank (treeToDigits gL) < 3 ^ (nodes gL + 1) .
      sizeLt : NatLe (suc p) (pow3 (suc (nodes gL)))
      sizeLt = n0_lt_pow3 gL
  in sg p (pr sizeLt (sg N finalRun))
