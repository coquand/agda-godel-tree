{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmBerry -- brick C of the non-computability proof: the runnable Berry
-- program and the  Kle  witness it produces.
--
--   berry Kf L  =  compose1U (BerryF Kf) (horner (digits3 L))
--
-- a closed mu-free Fun1 that, on input 0, computes  BerryF Kf  applied to L
-- (the constant L being printed by the Horner code  horner (digits3 L)).  Its
-- meta value is  bfun Kf L  (the Berry search result), so running it through
-- the universal machine ( evalU_correct_num ) and lifting to  runProgN
-- ( runProgN_at_diag ) -- exactly as T4.KolmRun does -- yields a program of size
-- O(log L) describing  bfun Kf L :
--
--   berryRun :  Kle (nodes (mcode1 (berry Kf L))) (bfun Kf L)
--
-- and the linear size accounting (mirroring T4.KolmSize) bounds that length.

module T4.KolmBerry where

open import T4.Base
open import T4.EvalUCorrect using
  ( EvalsTo ; fuel ; ev ; evalN1 ; evalN1_sound ; evalU_correct_num )
open import T4.EvalUEval    using ( evalU )
open import T4.EvalU        using ( mcode1 )
open import T4.ParseN       using ( runProgN ; diagRank ; runProgN_at_diag )
open import T4.McodeInAlph  using ( inAlph_mcode1 )
open import T4.TreeDigitsSize using ( pow3 ; n0_lt_pow3 )
open import T4.ProgEnc        using ( nodes )
open import BRA3.RuleInst2   using ( NatLe ; le-zero ; le-suc )
open import BRA3.Code.Tag    using ( addN )
open import T4.KolmHorner    using ( horner ; horner_correct )
open import T4.KolmDigits    using ( digits3 ; digits3_correct )
open import T4.KolmSize      using
  ( gnodes ; gnodes_eq ; Wf ; baseN ; PDmax ; repAdd ; lenDL
  ; nodes_horner_bound ; le_addN_1st )
open import T4.KolmLog       using ( allLt3_digits3 )
open import T4.KolmBoundedSearch using ( BerryF ; bfun ; berryMeta )
open import T4.KolmCount     using ( Kle ; And ; and )
open import T4.KolmNumReflect using ( Sg ; mkSg )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS )
open import T4.SurpriseG2.NumNeq using ( Not )
open import T4.Code          using ( falseF )

------------------------------------------------------------------------
-- NatLe (suc p) Q  ->  Lt p Q   (Kle wants the  Lt  order).

le_to_lt : {p Q : Nat} -> NatLe (suc p) Q -> Lt p Q
le_to_lt {zero}   (le-suc h) = ltZ _
le_to_lt {suc p'} (le-suc h) = ltS p' _ (le_to_lt h)

------------------------------------------------------------------------
-- The Berry program.

berry : Fun1 -> Nat -> Fun1
berry Kf L = compose1U (BerryF Kf) (horner (digits3 L))

------------------------------------------------------------------------
-- Running it:  Kle (nodes (mcode1 (berry Kf L))) (bfun Kf L) .

berryRun :
  Not (Deriv falseF) -> (Kf : Fun1) (L : Nat) ->
  Kle (nodes (mcode1 (berry Kf L))) (bfun Kf L)
berryRun con Kf L =
  let fx : Fun1
      fx = berry Kf L
      gL : Term
      gL = mcode1 fx
      p : Nat
      p = diagRank gL
      x : Nat
      x = bfun Kf L

      -- ap1 (horner (digits3 L)) O = natCode L .
      hornerO : Deriv (eqF (ap1 (horner (digits3 L)) O) (natCode L))
      hornerO =
        eqSubst (\ m -> Deriv (eqF (ap1 (horner (digits3 L)) O) (natCode m)))
                (digits3_correct L)
                (horner_correct (digits3 L))

      -- ap1 (BerryF Kf) (natCode L) = natCode (bfun Kf L)  (from berryMeta + soundness).
      objBerry : Deriv (eqF (ap1 (BerryF Kf) (natCode L)) (natCode x))
      objBerry =
        eqSubst (\ t -> Deriv (eqF (ap1 (BerryF Kf) (natCode L)) t))
                (eqCong natCode (berryMeta con Kf L))
                (ruleSym (evalN1_sound (BerryF Kf) L))

      -- ap1 fx O = natCode (bfun Kf L) .
      valueEq : Deriv (eqF (ap1 fx O) (natCode x))
      valueEq =
        ruleTrans (axComp (BerryF Kf) (horner (digits3 L)) O)
          (ruleTrans (cong1 (BerryF Kf) hornerO) objBerry)

      et : EvalsTo gL (ap1 s (natCode (evalN1 fx zero)))
      et = evalU_correct_num fx
      N : Nat
      N = fuel et

      valEq2 : Deriv (eqF (natCode (evalN1 fx zero)) (natCode x))
      valEq2 = ruleTrans (evalN1_sound fx zero) valueEq

      evalU_eq : Deriv (eqF (ap2 evalU gL (natCode N)) (ap1 s (natCode x)))
      evalU_eq = ruleTrans (ev et) (cong1 s valEq2)

      runEq : Deriv (eqF (ap2 runProgN (natCode p) (natCode N)) (ap2 evalU gL (natCode N)))
      runEq = runProgN_at_diag gL (inAlph_mcode1 fx) (natCode N)

      finalRun : Deriv (eqF (ap2 runProgN (natCode p) (natCode N)) (ap1 s (natCode x)))
      finalRun = ruleTrans runEq evalU_eq

      sizeLt : NatLe (suc p) (pow3 (suc (nodes gL)))
      sizeLt = n0_lt_pow3 gL
  in mkSg p (and (le_to_lt sizeLt) (mkSg N finalRun))

------------------------------------------------------------------------
-- The size of the Berry program is linear in the digit-length of L.
--
--   nodes (mcode1 (berry Kf L))  =  m0 + Wf (BerryF Kf)
--      with  m0 = nodes (mcode1 (horner (digits3 L)))  <=  baseN + PDmax * D ,
-- where  D = lenDL (digits3 L) .  (The  compose1U  layer adds the constant
-- Wf (BerryF Kf) ; this is exactly the refl-decomposition KolmSize uses.)

berrySize :
  (Kf : Fun1) (L : Nat) ->
  NatLe (nodes (mcode1 (berry Kf L)))
        (addN (addN baseN (repAdd PDmax (lenDL (digits3 L)))) (Wf (BerryF Kf)))
berrySize Kf L =
  let m0 : Nat
      m0 = nodes (mcode1 (horner (digits3 L)))
      -- nodes (mcode1 (berry Kf L)) = gnodes (BerryF Kf) m0 = addN m0 (Wf (BerryF Kf)) .
      decomp : Eq (nodes (mcode1 (berry Kf L))) (addN m0 (Wf (BerryF Kf)))
      decomp = gnodes_eq (BerryF Kf) m0
      nh : NatLe m0 (addN baseN (repAdd PDmax (lenDL (digits3 L))))
      nh = nodes_horner_bound (digits3 L) (allLt3_digits3 L)
      bound : NatLe (addN m0 (Wf (BerryF Kf)))
                    (addN (addN baseN (repAdd PDmax (lenDL (digits3 L)))) (Wf (BerryF Kf)))
      bound = le_addN_1st (Wf (BerryF Kf)) nh
  in eqSubst (\ z -> NatLe z (addN (addN baseN (repAdd PDmax (lenDL (digits3 L)))) (Wf (BerryF Kf))))
             (eqSym decomp) bound
