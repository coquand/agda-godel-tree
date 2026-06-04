{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1Theorem -- compose  T4.ChaitinG1Final.Assemble.chaitin_G1
-- with the run-derivation shipped in  T4.ChaitinG1RunDischarge.Discharge
-- to obtain the FULL conditional Chaitin-Goedel I , freed from the dEval
-- hypothesis:
--
--   chaitin_G1_full :
--     (x : Term) (nx : isNat x) (d : Deriv (Kgt Lstar x)) ->
--     isNat   (ap1 (out_L Lstar) (firstProof x nx d)) ->
--     Closed  (ap1 (out_L Lstar) (firstProof x nx d)) ->
--     Closed  (encode d) ->
--     ((a b : Term) -> Eq (simSubstT zero a (suc zero) b (encode d)) (encode d)) ->
--     Deriv falseF
--
-- Standing assumptions (surprise.pdf-granted):
--   * con   -- consistency of T (consumed by the clash inside chaitin_G1).
--   * nOut, clOut -- the read-off subject is an integer and closed.
--   * cl_encD, sim_encD -- the encoded proof is closed (substT/simSubstT
--                          stability), valid whenever  d  uses only closed
--                          substituents (= the surprise.pdf working scope).

module T4.ChaitinG1Theorem where

open import T4.Base
open import T4.ConInj          using ( ConSchema )
open import T4.Code            using ( falseF )
open import T4.IsNat           using ( isNat )
open import T4.KFormula        using ( Kgt )
open import T4.KOut            using ( out_L )
open import T4.KGodel1Bridge   using ( Lstar )
open import T4.Encode          using ( encode )
open import BRA3.Dispatch        using ( Closed )
open import BRA3.RuleInst2       using ( simSubstT )

import T4.ChaitinG1Final
import T4.ChaitinG1Discharge
import T4.ChaitinG1Chain

------------------------------------------------------------------------
-- The full conditional Chaitin-Goedel I.

module Final (con : Deriv ConSchema) where

  open T4.ChaitinG1Final.Assemble con using ( chaitin_G1 ; firstProof )

  chaitin_G1_full :
    (x : Term) (nx : isNat x) (d : Deriv (Kgt Lstar x)) ->
    isNat   (ap1 (out_L Lstar) (firstProof x nx d)) ->
    Closed  (ap1 (out_L Lstar) (firstProof x nx d)) ->
    Closed  (encode d) ->
    ((a b : Term) ->
       Eq (simSubstT zero a (suc zero) b (encode d)) (encode d)) ->
    Deriv falseF
  chaitin_G1_full x nx d nOut clOut cl_encD sim_encD =
    let open T4.ChaitinG1Chain.Chain
              x nx d cl_encD sim_encD
          using ( nTerm ; clN ; dEval_witness )
    in chaitin_G1 x nx d nOut clOut nTerm clN dEval_witness
