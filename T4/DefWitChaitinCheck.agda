{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DefWitChaitinCheck -- verification that the T4.DefWit definability
-- layer DE-ABSTRACTS the D1-necessitation leg of  SpikeChaitin.chaitin_thm .
--
-- SpikeChaitin abstracted the WHOLE KR-A layer as parameters.  This file
-- instantiates  SpikeChaitin.Search  with the REAL  DefWit.atomForm  and
-- calls  chaitin_thm  supplying the REAL  DefWit.cExF / DefWit.dExF  for the
-- Stage-2 D1 (necessitated  axExFalso ) argument.  Only the genuinely-future
-- pieces stay abstract module parameters:
--
--   hit / out / enum   -- the bounded search functors (KR-B);
--   hit_le_one / bridge -- isIncomprProof + its soundness (KR-B);
--   con / B / p0 / hp0  -- the Con + (FIT) witness (KR-D);
--   cPos / dPos         -- compress_canonical (KR-A, the remaining content).
--
-- That this typechecks confirms the  atomForm  shape and the  dExF
-- necessitation are correct drop-ins for the spike -- i.e. the D1 leg of
-- Chaitin's barrier is no longer abstract.

module T4.DefWitChaitinCheck where

open import T4.Base
open import T4.ThmT using ( thmT )
open import T4.Code using ( codeFormula ; falseF )
open import T4.DefWit using ( atomForm ; cExF ; dExF )
import T4.SpikeChaitin as SC

open import BRA3.ChurchLeq using ( leq )

module Check
  (ell : Term)
  (hit out enum : Fun1)
  (hit_le_one : (j : Term) -> Deriv (leq (ap1 hit j) (ap1 s O)))
  (bridge : (j : Term) ->
     Deriv (imp (eqF (ap1 hit j) (ap1 s O))
                (eqF (ap1 thmT (ap1 enum j))
                     (codeFormula (neg (atomForm ell (ap1 out j)))))))
  where

  -- instantiate the spike's search assembly at the REAL atomForm.
  open SC.Search hit out enum (atomForm ell) hit_le_one bridge

  -- chaitin_thm with the D1 leg (cExF / dExF) realised by DefWit; cPos / dPos
  -- (compress_canonical) and the Con/(FIT) witness remain the inputs.
  chaitin_barrier :
    Deriv ConSchema ->
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (leq p0 B) ->
    Deriv (eqF (ap1 hit p0) (ap1 s O)) ->
    (cPos : Term) ->
    Deriv (eqF (ap1 thmT cPos)
               (codeFormula (atomForm ell (ap1 out (ap2 lastPosRec O B))))) ->
    Deriv falseF
  chaitin_barrier con B p0 clB clP0 leqp0B hp0 cPos dPos =
    chaitin_thm con B p0 clB clP0 leqp0B hp0
      cPos (cExF ell (ap1 out (ap2 lastPosRec O B))) dPos
      (dExF ell (ap1 out (ap2 lastPosRec O B)))
