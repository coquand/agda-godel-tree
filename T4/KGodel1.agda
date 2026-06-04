{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KGodel1 -- Phase E4: the standalone conditional Chaitin-Goedel-I barrier
-- ASSEMBLED with dEval DERIVED (not assumed).  Connects the abstract equational
-- mu-loop + C-wrapper (T4.EvalUMu) to the clash wiring (T4.KSearch):
--
--   * dEval = ev (gLEvalU ...)  -- evalU(⌜g_L⌝, num N) = s (num z0) for the
--     diagonal g_L = out_L o (mu-search), built EQUATIONALLY from the shipped
--     stepU reductions (mu-loop muReaches + the C-wrapper evC/rtC1/u/rtApp2),
--     with SYMBOLIC fuel and the predicate / out_L evaluations as black boxes --
--     NEVER traversing thmT, NEVER depending on Agda's evaluation strategy.
--   * dNeg from the firing at the hit position (KSearch.kr_godel1_from_firing).
--   * kr_clash (T4.KClash) closes ⟹ falseF.
--
-- COHERENCE NOTE (the standard route uses the mu FIRST-hit for BOTH legs).  The
-- mu-program halts at the FIRST k with predicate(k)=O, i.e. the first hit; g_L's
-- output is  out_L(k0)  and the proof it "found" is at the SAME position k0.  So
-- the firing for dNeg is at  w0 := num k0  (the mu witness), NOT the last-hit of
-- T4.LastPosSearch -- which for this route is superseded (the mu-loop is the
-- canonical search evalU actually runs).  Here  w0 := num k0  is passed directly.
--
-- The remaining inputs are the genuine E4-concrete coherence facts (all abstract
-- here): predReaches (the predicate's per-position evaluation), outLReaches
-- (out_L's evaluation = out_L k0 = z0), the search witness (dHalt/dBelow giving
-- the first hit k0), and the antecedents dSubj / dLen / fire.

module T4.KGodel1 where

open import T4.Base
open import T4.ConInj      using ( ConSchema )
open import T4.KFormula    using ( szLeqApp )
open import T4.KOut        using ( out_L )
open import T4.Code        using ( falseF )
open import T4.EvalUEval   using ( evalU )
open import T4.EvalU       using ( cfgEV ; cfgRT )
open import T4.EvalUCorrect using ( Reaches ; EvalsTo ; fuel ; ev )
open import T4.ProgEnc      using ( enc )
open import T4.ProgParse    using ( parse )

import T4.EvalUMu
import T4.KSearch

open import BRA3.Church      using ( pi )

------------------------------------------------------------------------
-- The assembly, parametric in Con, L, the (opaque) predicate code and Fun2
-- code, the first-hit witness, and the two evaluation black boxes.

module G1
  (con : Deriv ConSchema) (L : Term)
  (gc : Term) (predVal predPre : Nat -> Term)
  (predReaches : (k : Nat) (K : Term) ->
                 Reaches (cfgEV gc (natCode k) K) (cfgRT (predVal k) K))
  (gCode : Term) (k0 z0 : Nat)
  (dHalt : Deriv (eqF (predVal k0) O))
  (dBelow : (i : Nat) -> T4.EvalUMu.Lt i k0 ->
            Deriv (eqF (predVal i) (ap1 s (predPre i))))
  (outLReaches : (K : Term) ->
                 Reaches (cfgEV gCode (ap2 pi (natCode k0) O) K) (cfgRT (natCode z0) K))
  where

  open T4.EvalUMu.Mu gc predVal predPre predReaches
    using ( gLCodeOf ; gLEvalU )
  open T4.KSearch.Build con L using ( hitL ; kr_godel1_from_firing )

  -- the diagonal program code  ⌜g_L⌝ .
  gLcode : Term
  gLcode = gLCodeOf gCode

  -- dEval, DERIVED equationally (symbolic fuel  N = fuel evc ).
  evc : EvalsTo gLcode (ap1 s (natCode z0))
  evc = gLEvalU gCode k0 z0 dHalt dBelow outLReaches

  dEval : Deriv (eqF (ap2 evalU gLcode (natCode (fuel evc))) (ap1 s (natCode z0)))
  dEval = ev evc

  -- THE standalone conditional Chaitin-Goedel-I barrier, now FAITHFUL: the
  -- subject is the NAME  nm := enc ⌜g_L⌝  (a description string), its size is
  -- lenR(nm) (Chaitin's length, T4.ProgEnc.lenR_enc), and the machine runs
  -- parse(nm) = ⌜g_L⌝  (the round-trip  dRT , T4.ProgParse.parse_enc -- left
  -- abstract here, discharged where  ⌜g_L⌝ ∈ InAlph  is concrete, R4).
  -- dEval (about ⌜g_L⌝) is lifted across the round-trip to dEval' (about parse(nm)).
  chaitin_G1 :
    Deriv (eqF (ap1 parse (enc gLcode)) gLcode) ->            -- dRT: parse(enc ⌜g_L⌝) = ⌜g_L⌝
    Deriv (eqF (ap1 (out_L L) (natCode k0)) (natCode z0)) ->   -- dSubj
    Deriv (eqF (szLeqApp L (enc gLcode)) (ap1 s O)) ->         -- dLen (faithful: lenR of the NAME)
    Deriv (eqF (ap1 hitL (natCode k0)) (ap1 s O)) ->           -- fire (the proof at the hit)
    Deriv falseF
  chaitin_G1 dRT dSubj dLen fire =
    let dEval' : Deriv (eqF (ap2 evalU (ap1 parse (enc gLcode)) (natCode (fuel evc)))
                            (ap1 s (natCode z0)))
        dEval' = ruleTrans (congL evalU (natCode (fuel evc)) dRT) dEval
    in kr_godel1_from_firing (enc gLcode) z0 (natCode k0) (natCode (fuel evc))
         (closed_natCode (fuel evc)) dSubj dEval' dLen fire
