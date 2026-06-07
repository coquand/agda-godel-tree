{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CoverBridgeN -- the number-code conjunction -> open-Pi_1 bridge
--   ( the  enum -blocker-free  T4.CoverBridge ).
--
--   coverBridgeN M r :
--     Deriv (imp (KdefBigConjNF F1 M r)                                  -- /\_{k<=M} ~def_k(r)
--                (imp (leq (var 0) (natCode M))                          -- p <= M
--                     (neg (eqF (ap2 runProgN (var 0) F1)                -- ~def_p(r)
--                               (ap1 s (natCode r))))))                  -- = KdefN(natCode r) @ predN:=natCode M
--
-- "if every program  k <= M  fails to describe day  r , then every program
--  p <= M  fails" -- the finite conjunction collapses to the bounded- forall .
-- With the IDENTITY enumeration the old surjective-pairing  internalCover  is just
-- T4.BoundedCases.boundedCases ( the program  IS  its index ), so the bridge is the
-- verbatim mirror of  T4.CoverBridge  with  enum k -> natCode k ,  runProg ->
-- runProgN ,  internalCover -> boundedCases .   The consequent is  T4.KdefN.KdefN
-- (natCode r)  at  predN := natCode M ( supply that on instantiation ).

open import T4.Base
open import BRA3.RuleInst2 using ( NatLe )
open import BRA3.ChurchLeq using ( leq )
open import T4.ParseN using ( runProgN )
open import T4.BoundedCases using ( boundedCases )
open import T4.SurpriseG2.AndLemmas using ( fstAndImp ; sndAndImp )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS ; Or ; inl ; inr )
open import T4.StageBaseFN using ( natLe_to_lt )
open import T4.Thm12.ImpHelpers using ( impLift ; impCongL ; impRuleSym )
open import T4.RunProgMono using ( impEqTrans2 )
open import BRA3.Contrapositive using ( identP ; compI ; bComb ; axContrapos )
open import BRA3.ChurchT80 using ( impFlip )
open import T4.StagePredFN using ( describeAtN )
open import T4.StepFrontEnd2N using ( perProgNegNF ; KdefBigConjNF ; F1 )

module T4.CoverBridgeN where

------------------------------------------------------------------------
-- ltSplit + impCompUnder ( verbatim from CoverBridge ).

ltSplitStep :
  (k' m' : Nat) -> Or (Eq k' m') (Lt k' m') ->
  Or (Eq (suc k') (suc m')) (Lt (suc k') (suc m'))
ltSplitStep k' m' (inl e)  = inl (eqCong suc e)
ltSplitStep k' m' (inr h') = inr (ltS k' m' h')

ltSplit : (k m : Nat) -> Lt k (suc m) -> Or (Eq k m) (Lt k m)
ltSplit zero    zero     _              = inl refl
ltSplit zero    (suc m') _              = inr (ltZ m')
ltSplit (suc k') zero    (ltS .k' .zero ())
ltSplit (suc k') (suc m') (ltS .k' .(suc m') h) =
  ltSplitStep k' m' (ltSplit k' m' h)

impCompUnder :
  {H A B Cf : Formula} ->
  Deriv (imp H (imp A B)) -> Deriv (imp H (imp B Cf)) ->
  Deriv (imp H (imp A Cf))
impCompUnder {H} {A} {B} {Cf} f g =
  bComb (compI (compI g (axK (imp B Cf) A)) (axS A B Cf)) f

------------------------------------------------------------------------
-- Conjunct extraction from the right-nested big conjunction.

module _ (r : Nat) where

  projConjB :
    (k : Nat) -> Or (Eq k zero) (Lt k zero) ->
    Deriv (imp (KdefBigConjNF F1 zero r) (perProgNegNF F1 r k))
  projConjB .zero (inl refl) = identP (perProgNegNF F1 r zero)
  projConjB k     (inr ())

  projConj :
    (m k : Nat) -> Lt k (suc m) ->
    Deriv (imp (KdefBigConjNF F1 m r) (perProgNegNF F1 r k))

  projConjS :
    (m' k : Nat) -> Or (Eq k (suc m')) (Lt k (suc m')) ->
    Deriv (imp (KdefBigConjNF F1 (suc m') r) (perProgNegNF F1 r k))
  projConjS m' .(suc m') (inl refl) =
    fstAndImp (perProgNegNF F1 r (suc m')) (KdefBigConjNF F1 m' r)
  projConjS m' k (inr lt') =
    compI (sndAndImp (perProgNegNF F1 r (suc m')) (KdefBigConjNF F1 m' r))
          (projConj m' k lt')

  projConj zero     k lt = projConjB k    (ltSplit k zero lt)
  projConj (suc m') k lt = projConjS m' k (ltSplit k (suc m') lt)

------------------------------------------------------------------------
-- The bridge.

module _ (M r : Nat) where

  KBC : Formula
  KBC = KdefBigConjNF F1 M r

  Cf : Formula
  Cf = neg (eqF (ap2 runProgN (var zero) F1) (ap1 s (natCode r)))

  cont :
    (k : Nat) -> NatLe k M ->
    Deriv (imp (eqF (var zero) (natCode k)) (imp KBC Cf))
  cont k kle =
    let Hk : Formula
        Hk = eqF (var zero) (natCode k)

        klt : Lt k (suc M)
        klt = natLe_to_lt M k kle

        projk : Deriv (imp KBC (perProgNegNF F1 r k))
        projk = projConj r M k klt

        runK : Term
        runK = ap2 runProgN (natCode k) F1
        runV : Term
        runV = ap2 runProgN (var zero) F1
        sr : Term
        sr = ap1 s (natCode r)
        E1 : Formula
        E1 = eqF runK sr
        E2 : Formula
        E2 = eqF runV sr

        congRun : Deriv (imp Hk (eqF runK runV))
        congRun = impRuleSym (impCongL {Hk} runProgN (var zero) (natCode k) F1
                                (identP Hk))

        impE2E1 : Deriv (imp Hk (imp E2 E1))
        impE2E1 =
          impEqTrans2 {Hk} {E2} runK runV sr
            (compI congRun (axK (eqF runK runV) E2))
            (impLift {Hk} (identP E2))

        rewriteImp : Deriv (imp Hk (imp (perProgNegNF F1 r k) Cf))
        rewriteImp = bComb (impLift {Hk} (axContrapos E2 E1)) impE2E1
    in impCompUnder {Hk} {KBC} {perProgNegNF F1 r k} {Cf}
         (impLift {Hk} projk) rewriteImp

  coverBridgeN :
    Deriv (imp KBC (imp (leq (var zero) (natCode M)) Cf))
  coverBridgeN = impFlip (boundedCases (var zero) M (imp KBC Cf) cont)
