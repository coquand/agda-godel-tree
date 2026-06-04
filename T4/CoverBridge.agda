{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CoverBridge -- the surprise-GII Step "conjunction => open-Pi_1 K-formula",
-- the SMALL-diagonal replacement for  T4.EnumCorrBridge.incBridge .
--
-- =====================================================================
-- THE POINT ( the size fix, via  internalCover ).
-- =====================================================================
--
-- EnumCorrBridge.incBridge  collapses the big conjunction to the single CK-atom
-- CK(r,x1)<>0 -- correct, but CK embeds the whole  enum  table, so its Chaitin
-- diagonal is  >> L*  ( the size wall ).   Here instead we collapse the
-- conjunction to the OPEN-Pi_1  K -formula over a FREE program  var 0 :
--
--   coverBridge :
--     Deriv (imp (KdefBigConjF enum (var 1) M (natCode r))                 -- /\_{k<=M} ¬def_{enum k}(r)
--                (imp (eqF (ap1 (checkAlphN Lstar_meta) (var 0)) (s O))    -- p = var 0 is a valid code, |p| <= L*
--                     (neg (eqF (ap2 runProg (var 0) (var 1)) (s (natCode r))))))   -- ¬def_p(r)
--
-- whose formula code embeds NO enumeration ( the program is  var 0 ), so the
-- shipped SMALL-diagonal Chaitin closer applies.   The collapse is exactly
-- internal enum-coverage ( T4.InternalCover.internalCover ) : the conjunction
-- says every ENUMERATED program fails to define  r ;  internalCover says every
-- VALID short  p  IS an enumerated program ;  so every valid short  p  fails --
-- which is the open  K -formula.   No surjective pairing ( see T4.InternalCover ).
--
-- Requires  M = Bnat - 1  ( supplied as  bnatEq : Eq Bnat (suc M) ), so the
-- conjunction's indices  0..M  are exactly  { k : k < Bnat } .

open import T4.Base

module T4.CoverBridge (Lstar_meta : Nat) where

open import T4.Kdef        using ( runProg )
open import T4.CheckAlphN  using ( checkAlphN )
open import T4.InternalCover Lstar_meta using ( internalCover )
open import T4.KdefBigConjFuelBridge using ( perProgNegF ; KdefBigConjF )
open import T4.SurpriseG2.AndLemmas using ( fstAndImp ; sndAndImp )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS )
open import T4.EnumProg Lstar_meta using ( enum ; Bnat ; Or ; inl ; inr )

open import T4.Thm12.ImpHelpers using ( impLift ; impCongL ; impRuleSym )
open import T4.RunProgMono using ( impEqTrans2 )
open import BRA3.Contrapositive using ( identP ; compI ; bComb ; axContrapos )
open import BRA3.ChurchT80 using ( impFlip )

------------------------------------------------------------------------
-- SECTION 0.  Two generic helpers.

-- A bounded  Lt  splits into "equal to the top" or "strictly below it".
ltSplit : (k m : Nat) -> Lt k (suc m) -> Or (Eq k m) (Lt k m)
ltSplit zero    zero     _              = inl refl
ltSplit zero    (suc m') _              = inr (ltZ m')
ltSplit (suc k') zero    (ltS .k' .zero ())
ltSplit (suc k') (suc m') (ltS .k' .(suc m') h) with ltSplit k' m' h
... | inl e  = inl (eqCong suc e)
... | inr h' = inr (ltS k' m' h')

-- Composition of two implications, threaded under a context  H .
impCompUnder :
  {H A B Cf : Formula} ->
  Deriv (imp H (imp A B)) -> Deriv (imp H (imp B Cf)) ->
  Deriv (imp H (imp A Cf))
impCompUnder {H} {A} {B} {Cf} f g =
  bComb (compI (compI g (axK (imp B Cf) A)) (axS A B Cf)) f

F1 : Term
F1 = var (suc zero)

------------------------------------------------------------------------
-- SECTION 1.  Conjunct extraction from the right-nested big conjunction.
--   projConj m k :  the conjunction of size  m  ( indices  0..m )  implies
--   its  k -th conjunct  ( k <= m ).

module _ (r : Nat) where

  -- NOTE: the case split passes the  Or  as an EXPLICIT argument
  -- ( projConjB / projConjS ), NOT via  with  -- a  with  on  ltSplit  would
  -- abstract the huge  KdefBigConjF / perProgNegF  goal ( which embeds  runProg
  -- = the universal machine ) over the scrutinee and normalise it, blowing up.
  projConjB :
    (k : Nat) -> Or (Eq k zero) (Lt k zero) ->
    Deriv (imp (KdefBigConjF enum F1 zero (natCode r))
               (perProgNegF enum F1 (natCode r) k))
  projConjB .zero (inl refl) = identP (perProgNegF enum F1 (natCode r) zero)
  projConjB k     (inr ())

  projConj :
    (m k : Nat) -> Lt k (suc m) ->
    Deriv (imp (KdefBigConjF enum F1 m (natCode r))
               (perProgNegF enum F1 (natCode r) k))

  projConjS :
    (m' k : Nat) -> Or (Eq k (suc m')) (Lt k (suc m')) ->
    Deriv (imp (KdefBigConjF enum F1 (suc m') (natCode r))
               (perProgNegF enum F1 (natCode r) k))
  projConjS m' .(suc m') (inl refl) =
    fstAndImp (perProgNegF enum F1 (natCode r) (suc m'))
              (KdefBigConjF enum F1 m' (natCode r))
  projConjS m' k (inr lt') =
    compI (sndAndImp (perProgNegF enum F1 (natCode r) (suc m'))
                     (KdefBigConjF enum F1 m' (natCode r)))
          (projConj m' k lt')

  projConj zero     k lt = projConjB k    (ltSplit k zero lt)
  projConj (suc m') k lt = projConjS m' k (ltSplit k (suc m') lt)

------------------------------------------------------------------------
-- SECTION 2.  The bridge.

module _ (M : Nat) (r : Nat) (bnatEq : Eq Bnat (suc M)) where

  KBC : Formula
  KBC = KdefBigConjF enum F1 M (natCode r)

  -- the open-Pi_1 consequent  ¬def_p(r)  at the free program  var 0 .
  Cf : Formula
  Cf = neg (eqF (ap2 runProg (var zero) F1) (ap1 s (natCode r)))

  -- per-index continuation :  p = enum k  =>  ( conjunction  =>  ¬def_p(r) ).
  cont :
    (k : Nat) -> Lt k Bnat ->
    Deriv (imp (eqF (var zero) (ap1 enum (natCode k))) (imp KBC Cf))
  cont k klt =
    let Hk : Formula
        Hk = eqF (var zero) (ap1 enum (natCode k))

        klt' : Lt k (suc M)
        klt' = eqSubst (\ b -> Lt k b) bnatEq klt

        projk : Deriv (imp KBC (perProgNegF enum F1 (natCode r) k))
        projk = projConj r M k klt'

        runK : Term
        runK = ap2 runProg (ap1 enum (natCode k)) F1
        runV : Term
        runV = ap2 runProg (var zero) F1
        sr : Term
        sr = ap1 s (natCode r)
        E1 : Formula                          -- enum k defines r
        E1 = eqF runK sr
        E2 : Formula                          -- var 0 defines r
        E2 = eqF runV sr
        -- perProgNegF ... k  =  neg E1 ;   Cf  =  neg E2 .

        congRun : Deriv (imp Hk (eqF runK runV))
        congRun = impRuleSym (impCongL {Hk} runProg (var zero) (ap1 enum (natCode k)) F1
                                (identP Hk))

        impE2E1 : Deriv (imp Hk (imp E2 E1))
        impE2E1 =
          impEqTrans2 {Hk} {E2} runK runV sr
            (compI congRun (axK (eqF runK runV) E2))
            (impLift {Hk} (identP E2))

        rewriteImp : Deriv (imp Hk (imp (perProgNegF enum F1 (natCode r) k) Cf))
        rewriteImp = bComb (impLift {Hk} (axContrapos E2 E1)) impE2E1
    in impCompUnder {Hk} {KBC} {perProgNegF enum F1 (natCode r) k} {Cf}
         (impLift {Hk} projk) rewriteImp

  coverBridge :
    Deriv (imp KBC
               (imp (eqF (ap1 (checkAlphN Lstar_meta) (var zero)) (ap1 s O)) Cf))
  coverBridge = impFlip (internalCover (imp KBC Cf) cont)
