{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.LenGLcodeProbe -- Phase E4 task #7, QUESTION 1 (CHAITIN-G1-LPIN-DESIGN.md).
--
-- Settle the size measure FIRST: compute  lenR (gLcode L)  and see whether it
-- depends on  L .
--
-- gLcode L  (T4.KDiag) is the right-spine
--
--   pi (natCode tag_C) ( pi (gCodeOf L) ( pi (mcodeMu (mcode1 (predFlip L))) (mcode1 u) ) )
--
-- a 4-node spine.  lenR counts one per right-spine node whose head (Fst /
-- left child) is a SUCCESSOR -- and it IGNORES the left child entirely.  Every
-- head here is positive (tag numerals  natCode 7/u , or compound codes
-- gCodeOf L / mcodeMu ... which are pi-nodes = s-shaped via pi_at_succ), so
-- lenR descends all 4 nodes; but  L  sits ONLY inside the left children
-- (gCodeOf L  and  mcodeMu (mcode1 (predFlip L))), which lenR throws away.
--
-- CONCLUSION (machine-checked below):  lenR (gLcode L) = natCode 4 , for ALL L.
-- So lenR is OUTCOME (A): not L-dependent, hence NOT a faithful code-size
-- measure (countless distinct programs share lenR = 4).  dLen is trivial under
-- lenR (pick any L >= 4), but the measure is wrong -- go to Question 2.

module T4.LenGLcodeProbe where

open import T4.Base
open import T4.LenR        using ( lenR ; lenR_at_O ; lenR_at_node )
open import T4.PiPositivity using ( pi_at_succ ; pi_succ_outer )
open import T4.KDiag       using ( gLcode ; gCodeOf ; predFlip )
open import T4.KOut        using ( out_L )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu )

open import BRA3.Church      using ( pi )

------------------------------------------------------------------------
-- The right-spine pieces (definitional unfoldings of  gLcode L ).

-- the Snd-payload of  gCodeOf L = mcode2 (Lift1 (out_L L)) = mcode2 (R (out_L L) v v).
gBody : Term -> Term
gBody L = ap2 pi (mcode1 (out_L L)) (ap2 pi (mcode2 v) (mcode2 v))

muBody : Term -> Term
muBody L = mcode1 (predFlip L)

rest1 : Term -> Term
rest1 L = ap2 pi (mcodeMu (muBody L)) (mcode1 u)

rest0 : Term -> Term
rest0 L = ap2 pi (gCodeOf L) (rest1 L)

------------------------------------------------------------------------
-- A compound-head version of  lenR_at_node :  if the head  P  is provably a
-- successor  ap1 s A , then  lenR (pi P b) = s (lenR b) .

lenR_at_compound :
  (P b A : Term) -> Deriv (eqF P (ap1 s A)) ->
  Deriv (eqF (ap1 lenR (ap2 pi P b)) (ap1 s (ap1 lenR b)))
lenR_at_compound P b A hp =
  ruleTrans (cong1 lenR (congL pi b hp)) (lenR_at_node A b)

------------------------------------------------------------------------
-- The four node steps.

-- mcode1 u = pi (natCode 6) O ;  head is the numeral tag (literally s _).
lenR_mcode1_u : Deriv (eqF (ap1 lenR (mcode1 u)) (ap1 s O))
lenR_mcode1_u = ruleTrans (lenR_at_node _ O) (cong1 s lenR_at_O)

-- rest1 : head  mcodeMu (...) = pi (natCode 13) (...)  -- s-shaped via pi_at_succ.
lenR_rest1 : (L : Term) ->
  Deriv (eqF (ap1 lenR (rest1 L)) (ap1 s (ap1 lenR (mcode1 u))))
lenR_rest1 L =
  lenR_at_compound (mcodeMu (muBody L)) (mcode1 u) _
    (pi_at_succ _ (muBody L))

-- rest0 : head  gCodeOf L = pi (natCode 9) (gBody L)  -- s-shaped via pi_at_succ.
lenR_rest0 : (L : Term) ->
  Deriv (eqF (ap1 lenR (rest0 L)) (ap1 s (ap1 lenR (rest1 L))))
lenR_rest0 L =
  lenR_at_compound (gCodeOf L) (rest1 L) _
    (pi_at_succ _ (gBody L))

-- node0 : head  natCode 7  -- literally s _.
lenR_node0 : (L : Term) ->
  Deriv (eqF (ap1 lenR (gLcode L)) (ap1 s (ap1 lenR (rest0 L))))
lenR_node0 L = lenR_at_node _ (rest0 L)

------------------------------------------------------------------------
-- HEADLINE :  lenR (gLcode L) = natCode 4 , independent of  L .

lenR_gLcode :
  (L : Term) ->
  Deriv (eqF (ap1 lenR (gLcode L)) (natCode (suc (suc (suc (suc zero))))))
lenR_gLcode L =
  ruleTrans (lenR_node0 L)
    (ruleTrans (cong1 s (lenR_rest0 L))
      (ruleTrans (cong1 s (cong1 s (lenR_rest1 L)))
        (cong1 s (cong1 s (cong1 s lenR_mcode1_u)))))
