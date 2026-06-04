{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BridgeComp -- the Chaitin search's  bridge  soundness for the CORRECTED
-- (computation-naming) atom (NEXT-SESSION-CHAITIN-G1.md Step 2c).  The  num
-- -single companion of  T4.Bridge  (which built it for the OLD self-naming
-- atom).  Same numeric-equality core, new code-builder.
--
-- The comparison is the shipped numeric equality indicator  eqInd  (codes are
-- naturals under the injective Pair/pi pairing, so  eqF  IS numeric equality --
-- no structural Pair-tree recursion).  The reflection  eqInd_sound  (eqInd a b
-- = s O => a = b) is REUSED VERBATIM from  T4.Bridge  (it is generic over the
-- terms  a , b ).  The ONLY new content is composing it with the Step-2b
-- PROVED  negAtomCompOf_correct :
--
--   bridgeCompCore : a firing numeric match at position  proofCode  (between
--   thmT proofCode  and the expected incompressibility code  negAtomCompOf ell
--   srch (natCode n)) means  thmT proofCode = codeFormula (neg (atomFormCompAt
--   ell (canonName srch ell) (canonPrf srch ell) (natCode n))) .
--
-- This RHS is exactly  codeFormula (neg (CompressComp.atomComp ell srch (natCode
-- n)))  (same canonical name / proof slots) -- so it is the  dNeg  the Chaitin
-- barrier consumes, once the enumerator pins  proofCode := enum j  and the
-- subject  := out j  (Step 2d, with the concrete  pairEnum  of Step 3).  Every
-- step here is a PROVED Deriv.

module T4.BridgeComp where

open import T4.Base
open import T4.Code using ( codeFormula )
open import T4.ThmT using ( thmT )
open import T4.DefWitComp using ( atomFormCompAt )
open import T4.NegAtomComp
  using ( negAtomCompOf ; negAtomCompOf_correct ; canonName ; canonPrf )
open import T4.Bridge using ( eqInd_sound )
open import T4.Counting using ( eqInd ; eqInd_le_one )

open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- SECTION 1.  bridgeCompCore -- the bridge for a numeral subject  natCode n .
--
-- Reflection (eqInd_sound, reused) + the Step-2b PROVED  negAtomCompOf_correct .

bridgeCompCore :
  (ell : Term) (srch : Fun1) (n : Nat) (proofCode : Term) ->
  Deriv (eqF (eqInd (ap1 thmT proofCode) (ap1 (negAtomCompOf ell srch) (natCode n)))
             (ap1 s O)) ->
  Deriv (eqF (ap1 thmT proofCode)
             (codeFormula (neg (atomFormCompAt ell (canonName srch ell)
                                               (canonPrf srch ell) (natCode n)))))
bridgeCompCore ell srch n proofCode hmatch =
  ruleTrans (eqInd_sound (ap1 thmT proofCode)
                         (ap1 (negAtomCompOf ell srch) (natCode n)) hmatch)
            (negAtomCompOf_correct ell srch n)

------------------------------------------------------------------------
-- SECTION 2.  The 0/1 bound (= hit_le_one once  hit  is wired through enum):
-- the numeric indicator is in {0, s O}, the shipped  eqInd_le_one .

hitBound :
  (a b : Term) -> Deriv (leq (eqInd a b) (ap1 s O))
hitBound = eqInd_le_one
