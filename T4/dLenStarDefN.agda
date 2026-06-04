{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.dLenStarDefN -- the number-code re-pointing of T4.dLenStarDef : the OBJECT
-- size pin for the honest p<N diagonal.   Mirrors dLenStarDef/dLen_gen but the
-- guard is  leq p N = (sub p N = O) , N = NthrN = 3^(L*+1) :
--
--   sizePinN : Deriv (leq (natCode n0) NthrN)        ( n0 = diagRank gLN )
--
-- i.e. T proves "the diagonal's number is < N".   Built from the META size fact
--   n0 < 3^(nodes gL + 1)  (TreeDigitsSize.n0_lt_pow3) and the fixed point
--   nodes gL <= L* = 2^k  (KGodel1BridgeDefN.domBDefN), via pow3-monotonicity,
--   then sub_le_zero on the numeral after evaluating NthrN = natCode (3^(2^k+1)).
-- This is exactly Chaitin's  c + log n < n  -- it CLOSES, no assumption.

module T4.dLenStarDefN where

open import T4.Base
open import T4.ProgEnc using ( nodes )
open import T4.ParseN  using ( diagRank )
open import T4.CandidateCover using ( rank )
open import T4.TreeToDigits using ( treeToDigits )
open import T4.TreeDigitsSize using ( pow3 ; n0_lt_pow3 )
open import T4.Exp  using ( exp2 ; powN ; exp2_natCode )
open import T4.Exp3 using ( exp3 ; exp3_natCode )
open import T4.SubLeq using ( sub_le_zero )
open import T4.KGodel1BridgeDefN using ( NthrN ; boundDefN ; domBDefN )

import T4.KdefDiagN

open import BRA3.Church using ( sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.Code.Tag using ( addN )
open import BRA3.RuleInst2 using
  ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans )
open import T4.NatExp using ( fst ; addN_mono ; le_self_addN_l )

------------------------------------------------------------------------
-- SECTION 0.  pow3 positivity + monotonicity ( meta ).

pow3_pos : (k : Nat) -> NatLe (suc zero) (pow3 k)
pow3_pos zero    = le-refl (suc zero)
pow3_pos (suc k) =
  le-trans (pow3_pos k) (le_self_addN_l (pow3 k) (addN (pow3 k) (pow3 k)))

pow3_mono : (a b : Nat) -> NatLe a b -> NatLe (pow3 a) (pow3 b)
pow3_mono .zero    b       (le-zero .b)      = pow3_pos b
pow3_mono (suc a') (suc b') (le-suc le')      =
  addN_mono (pow3_mono a' b' le')
            (addN_mono (pow3_mono a' b' le') (pow3_mono a' b' le'))

------------------------------------------------------------------------
-- SECTION 1.  The diagonal, its number, and the size inequality.

kk : Nat
kk = fst boundDefN

-- SEALED so  diagRank gLN = rank (treeToDigits gLN)  and  nodes gLN  stay NEUTRAL
-- (symbolic) -- otherwise  gLN  ( concrete, embedding thmT ) reduces, and worse
-- the diagonal's NUMBER  n0  becomes a concrete astronomical numeral, so
-- le-refl n0 / sub_le_zero recurse on its value.  Only  gLN_eq  is exposed for
-- bridging;  everything else uses the OPAQUE  gLN  so  n0  is an inert symbol.
abstract
  gLN : Term
  gLN = T4.KdefDiagN.gLcodeDefN NthrN

  gLN_eq : Eq gLN (T4.KdefDiagN.gLcodeDefN NthrN)
  gLN_eq = refl

n0 : Nat
n0 = diagRank gLN                          -- = rank (treeToDigits gLN) , INERT ( gLN opaque )

-- the bound, transported to the SEALED gLN OUTSIDE the block ( nodes sits in the
-- non-computing NatLe wrapper, never forced ).
domB_gLN : NatLe (nodes gLN) (powN kk)
domB_gLN = eqSubst (\ g -> NatLe (nodes g) (powN kk)) (eqSym gLN_eq) domBDefN

-- GENERIC bound lemma ( t ABSTRACT ): result type carries  pow3 (suc b)  -- NOT
--  pow3 (suc (nodes t)) -- so applying it to gLN never FORCES  nodes / rank .
rank_lt_bound :
  (t : Term) (b : Nat) ->
  NatLe (nodes t) b -> NatLe (suc (rank (treeToDigits t))) (pow3 (suc b))
rank_lt_bound t b bd =
  le-trans (n0_lt_pow3 t) (pow3_mono (suc (nodes t)) (suc b) (le-suc bd))

-- suc n0 <= 3^(2^k+1)  ( = N as a value ) -- gLN opaque ⇒ all inert.
n0_lt_N : NatLe (suc n0) (pow3 (suc (powN kk)))
n0_lt_N = rank_lt_bound gLN (powN kk) domB_gLN

n0_le_N : NatLe n0 (pow3 (suc (powN kk)))
n0_le_N = le-trans (le-suc-right (le-refl n0)) n0_lt_N

------------------------------------------------------------------------
-- SECTION 2.  NthrN evaluates to the numeral  natCode (3^(2^k+1)) .

NthrN_eval : Deriv (eqF NthrN (natCode (pow3 (suc (powN kk)))))
NthrN_eval =
  ruleTrans (cong1 exp3 (cong1 s (exp2_natCode kk)))
            (exp3_natCode (suc (powN kk)))

------------------------------------------------------------------------
-- SECTION 3.  THE OBJECT SIZE PIN.   T proves  n0 <= N  ( leq (natCode n0) N ).

sizePinN : Deriv (eqF (ap2 sub (natCode n0) NthrN) O)
sizePinN =
  ruleTrans (congR sub (natCode n0) NthrN_eval) (sub_le_zero n0_le_N)
