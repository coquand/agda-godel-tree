{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KGodel1Canon -- Phase R6: the standalone conditional Chaitin-Goedel-I
-- barrier with  dLen  DISCHARGED at the canonical threshold  L* = 2^(fst bound),
-- and -- new -- the two interpreter-correctness black boxes  predReaches /
-- outLReaches  DISCHARGED via the symbolic per-position lemmas
-- (T4.EvalUReachSym).
--
-- The barrier T4.KDiag.chaitin_G1_diag is parametric in ONE program (the
-- diagonal  gLcode L ); we pin  L := L*  (T4.KGodel1Bridge) and:
--   * supply  dLen  via the abstract generic  Size.dLen_gen  at  e := enc (gLcode L*)
--     with (A) lenR_enc and (B) the domination transported at the NUMBER level;
--   * supply  predReaches  =  ev1_reaches (predFlip L*)  -- the universal machine
--     run on the predicate code reaches the SYMBOLIC value  predFlip L* (k) ;
--   * supply  outLReaches  from  dSubj  +  ev2_reaches (Lift1 (out_L L*))  +  Lift1_eq .
--
-- ev1_reaches / ev2_reaches are GENERIC in the function and SEALED abstract, so
-- instantiating at the concrete  predFlip L* / out_L L*  (which embed  thmT ) is a
-- NEUTRAL application -- the interpreter correctness is INSTANTIATED, never run,
-- so  thmT  is never traversed.  This is the same discipline as the size feed.
--
-- The remaining inputs are exactly the genuine search-exists facts (Con + the
-- firing  hitAtK0 , its firstness  noHitBelow , and the subject  dSubj ).

module T4.KGodel1Canon where

open import T4.Base
open import T4.ConInj       using ( ConSchema )
open import T4.Code         using ( falseF )
open import T4.KFormula     using ( szLeqApp )
open import T4.KRecog       using ( hitK )
open import T4.KOut         using ( out_L )
open import T4.KDiag        using ( gLcode ; predFlip ; gCodeOf ; chaitin_G1_diag )
open import T4.EvalU        using ( mcode1 ; mcode2 ; cfgEV ; cfgRT )
open import T4.EvalUCorrect using ( Reaches ; reach_eq_target ; cfgRT_val )
open import T4.EvalUReachSym using ( ev1_reaches ; ev2_reaches )
open import T4.EvalUMu      using ( Lt )
open import T4.ProgNodes    using ( plug )
open import T4.ProgEnc      using ( nodes ; enc ; lenR_enc )
open import T4.Exp          using ( exp2 ; powN )
open import T4.GLCodeNodes  using ( H )
open import T4.NatExp       using ( Sg ; fst ; snd )

open import BRA3.Church       using ( pi )
open import BRA3.Fan          using ( Lift1 ; Lift1_eq )
open import BRA3.RuleInst2    using ( NatLe )

open import T4.KGodel1Bridge using ( Lstar ; bridge ; Cmcodeb ; bound ; dLen_gen )

------------------------------------------------------------------------
-- (B) THE DOMINATION, transported to the built form at the NUMBER level.
-- GENERIC + SEALED transport: with the two programs as VARIABLES X, Y, the
-- eqSubst body type-checks with  nodes X / nodes Y  NEUTRAL; sealed, so at the
-- concrete instantiation it is a NEUTRAL application -- nodes is never reduced.
abstract
  transportNodes :
    (X Y : Term) (c : Nat) -> Eq X Y -> NatLe (nodes X) c -> NatLe (nodes Y) c
  transportNodes X Y c eq le = eqSubst (\ m -> NatLe m c) (eqCong nodes eq) le

domB : NatLe (nodes (gLcode Lstar)) (powN (fst bound))
domB =
  transportNodes (plug Cmcodeb (H (fst bound))) (gLcode Lstar) (powN (fst bound))
                 (eqSym bridge) (snd bound)

------------------------------------------------------------------------
-- dLen at the built form, via the abstract generic  dLen_gen  applied at
--   e := enc (gLcode L*) ,  n := nodes (gLcode L*) ,  k := fst bound .
dLenStar :
  Deriv (eqF (szLeqApp Lstar (enc (gLcode Lstar))) (ap1 s O))
dLenStar =
  dLen_gen (nodes (gLcode Lstar)) (fst bound) (enc (gLcode Lstar))
           (lenR_enc (gLcode Lstar)) domB

------------------------------------------------------------------------
-- The interpreter-correctness facts, DISCHARGED symbolically.

-- predReaches: the machine on the predicate code reaches  predFlip L* (k) .
predReachesStar :
  (k : Nat) (K : Term) ->
  Reaches (cfgEV (mcode1 (predFlip Lstar)) (natCode k) K)
          (cfgRT (ap1 (predFlip Lstar) (natCode k)) K)
predReachesStar k K = ev1_reaches (predFlip Lstar) k K

-- outLReaches: the output-extraction  gCodeOf L* = mcode2 (Lift1 (out_L L*))
-- run at  (k0, 0)  reaches  z0 .  ev2_reaches gives the symbolic  ap2 (Lift1 ..)
-- value; Lift1_eq drops the (ignored) second argument; dSubj closes to  z0 .
outLReachesStar :
  (k0 z0 : Nat) ->
  Deriv (eqF (ap1 (out_L Lstar) (natCode k0)) (natCode z0)) ->
  (K : Term) ->
  Reaches (cfgEV (gCodeOf Lstar) (ap2 pi (natCode k0) O) K) (cfgRT (natCode z0) K)
outLReachesStar k0 z0 dSubj K =
  reach_eq_target (ev2_reaches (Lift1 (out_L Lstar)) k0 zero K)
    (cfgRT_val (ap2 (Lift1 (out_L Lstar)) (natCode k0) (natCode zero)) (natCode z0) K
       (ruleTrans (Lift1_eq (out_L Lstar) (natCode k0) (natCode zero)) dSubj))

------------------------------------------------------------------------
-- THE CAPSTONE.  The standalone conditional Chaitin-Goedel-I, with the size
-- threshold  dLen  AND the interpreter-correctness facts DISCHARGED.  The only
-- remaining inputs are the genuine search-exists facts:
--   con        -- T is consistent;
--   hitAtK0    -- the search FIRES at position k0 (T proves K(z0)>L*);
--   noHitBelow -- k0 is the FIRST hit;
--   dSubj      -- the search subject read off at k0 is the numeral z0.
chaitin_G1_canonical :
  Deriv ConSchema -> (k0 z0 : Nat) ->
  Deriv (eqF (ap1 (hitK Lstar (out_L Lstar)) (natCode k0)) (ap1 s O)) ->
  ((i : Nat) -> Lt i k0 ->
     Deriv (eqF (ap1 (hitK Lstar (out_L Lstar)) (natCode i)) O)) ->
  Deriv (eqF (ap1 (out_L Lstar) (natCode k0)) (natCode z0)) ->
  Deriv falseF
chaitin_G1_canonical con k0 z0 hitAtK0 noHitBelow dSubj =
  chaitin_G1_diag con Lstar k0 z0
    predReachesStar
    (outLReachesStar k0 z0 dSubj)
    hitAtK0 noHitBelow dSubj dLenStar
