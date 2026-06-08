{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmCount -- the converse COUNTING bound for Kolmogorov complexity:
--
--   #{ x : K(x) <= L }  <=  3 ^ (L+1) .
--
-- "K(x) <= L" = x is described by some program p < 3^(L+1) :
--   Kle L x = exists p < 3^(L+1), exists N, runProgN p N = s (natCode x) .
--
-- Stated constructively: any sequence xs of values all with K<=L has a repeat
-- among its first 3^(L+1)+1 entries ( a Collide ).  The argument: each value
-- picks a describing program in [0,3^(L+1)) ; by the meta pigeonhole two values
-- share a program ; and a program describes at most ONE value -- ON PAIN OF
-- INCONSISTENCY ( the only hypothesis: simple consistency con : Not (Deriv
-- falseF) ; the lower bound genuinely needs soundness ).  Determinism uses
-- run-monotonicity to a common fuel + sigma-commutativity.

module T4.KolmCount where

open import T4.Base
open import T4.ParseN          using ( runProgN )
open import BRA3.Church        using ( sigma )
open import BRA3.Numerals      using ( sigma_natCode )
open import BRA3.Code.Tag      using ( addN )
open import BRA3.Code.CantorGrowth using ( addN_comm )
open import T4.RunProgMonoN    using ( runProgMonoPlusN )
open import T4.TreeDigitsSize  using ( pow3 )
open import T4.KolmLog         using ( pow3_ge1 )
open import T4.Code            using ( falseF )
open import BRA3.RuleInst2      using ( NatLe )
open import T4.KolmNumReflect  using ( Sg ; mkSg ; numEqToFalse )
open import T4.SurpriseG2.NumNeq using ( Not )
open import T4.SurpriseG2.MetaPigeonhole using
  ( Lt ; ltSelf ; Collide ; mkCollide ; pigeonhole
  ; NatDec ; natYes ; natNo ; natDecEq ; sucInj )

------------------------------------------------------------------------
-- local conjunction.

record And (A B : Set) : Set where
  constructor and
  field
    p1 : A
    p2 : B

------------------------------------------------------------------------
-- K(x) <= L.

Kle : Nat -> Nat -> Set
Kle L x =
  Sg Nat (\ p ->
    And (Lt p (pow3 (suc L)))
        (Sg Nat (\ N ->
          Deriv (eqF (ap2 runProgN (natCode p) (natCode N)) (ap1 s (natCode x))))))

------------------------------------------------------------------------
-- determinism: one program describes at most one value.

runDet :
  (p xi xj Ni Nj : Nat) ->
  Deriv (eqF (ap2 runProgN (natCode p) (natCode Ni)) (ap1 s (natCode xi))) ->
  Deriv (eqF (ap2 runProgN (natCode p) (natCode Nj)) (ap1 s (natCode xj))) ->
  Deriv (eqF (ap1 s (natCode xi)) (ap1 s (natCode xj)))
runDet p xi xj Ni Nj hi hj =
  let -- push both runs to fuel  sigma N _  , then collapse sigma to natCode (addN _ _).
      pii : Deriv (eqF (ap2 runProgN (natCode p) (ap2 sigma (natCode Ni) (natCode Nj)))
                       (ap1 s (natCode xi)))
      pii = runProgMonoPlusN (natCode p) (natCode xi) (natCode Ni) (natCode Nj) hi
      pjj : Deriv (eqF (ap2 runProgN (natCode p) (ap2 sigma (natCode Nj) (natCode Ni)))
                       (ap1 s (natCode xj)))
      pjj = runProgMonoPlusN (natCode p) (natCode xj) (natCode Nj) (natCode Ni) hj
      -- sigma (natCode Ni) (natCode Nj) = natCode (addN Ni Nj)
      pii2 : Deriv (eqF (ap2 runProgN (natCode p) (natCode (addN Ni Nj))) (ap1 s (natCode xi)))
      pii2 = ruleTrans (ruleSym (congR runProgN (natCode p) (sigma_natCode Ni Nj))) pii
      pjj2 : Deriv (eqF (ap2 runProgN (natCode p) (natCode (addN Nj Ni))) (ap1 s (natCode xj)))
      pjj2 = ruleTrans (ruleSym (congR runProgN (natCode p) (sigma_natCode Nj Ni))) pjj
      -- addN Nj Ni = addN Ni Nj  (meta), so both runs share fuel  natCode (addN Ni Nj).
      pjj3 : Deriv (eqF (ap2 runProgN (natCode p) (natCode (addN Ni Nj))) (ap1 s (natCode xj)))
      pjj3 = eqSubst (\ m -> Deriv (eqF (ap2 runProgN (natCode p) (natCode m)) (ap1 s (natCode xj))))
                     (addN_comm Nj Ni) pjj2
  in ruleTrans (ruleSym pii2) pjj3

valEq :
  Not (Deriv falseF) ->
  (p xi xj Ni Nj : Nat) ->
  Deriv (eqF (ap2 runProgN (natCode p) (natCode Ni)) (ap1 s (natCode xi))) ->
  Deriv (eqF (ap2 runProgN (natCode p) (natCode Nj)) (ap1 s (natCode xj))) ->
  Eq xi xj
valEq con p xi xj Ni Nj hi hj = decide (natDecEq xi xj)
  where
    det : Deriv (eqF (natCode (suc xi)) (natCode (suc xj)))
    det = runDet p xi xj Ni Nj hi hj
    decide : NatDec xi xj -> Eq xi xj
    decide (natYes e) = e
    decide (natNo  ne) =
      emptyElim (con (numEqToFalse (suc xi) (suc xj) (\ e -> ne (sucInj e)) det))

------------------------------------------------------------------------
-- a positive number is a successor.

pos_to_suc : {K : Nat} -> NatLe (suc zero) K -> Sg Nat (\ M -> Eq K (suc M))
pos_to_suc {zero}  ()
pos_to_suc {suc M} _ = mkSg M refl

------------------------------------------------------------------------
-- THE COUNTING BOUND.

countingBound :
  Not (Deriv falseF) ->
  (L : Nat) (xs : Nat -> Nat) ->
  ((i : Nat) -> Kle L (xs i)) ->
  Collide xs (pow3 (suc L))
countingBound con L xs ws =
  mkCollide i0 j0
    (Collide.i_lt coll) (Collide.j_lt coll) (Collide.i_neq coll)
    valsEq
  where
    N0 : Nat
    N0 = pow3 (suc L)

    posN0 : Sg Nat (\ M -> Eq N0 (suc M))
    posN0 = pos_to_suc (pow3_ge1 (suc L))
    M0 : Nat
    M0 = Sg.fst posN0
    eN0 : Eq N0 (suc M0)
    eN0 = Sg.snd posN0

    prog : Nat -> Nat
    prog i = Sg.fst (ws i)

    fuelOf : (i : Nat) -> Nat
    fuelOf i = Sg.fst (And.p2 (Sg.snd (ws i)))

    descOf : (i : Nat) ->
      Deriv (eqF (ap2 runProgN (natCode (prog i)) (natCode (fuelOf i)))
                 (ap1 s (natCode (xs i))))
    descOf i = Sg.snd (And.p2 (Sg.snd (ws i)))

    bd : (i : Nat) -> Lt i (suc N0) -> Lt (prog i) (suc M0)
    bd i _ = eqSubst (\ z -> Lt (prog i) z) eN0 (And.p1 (Sg.snd (ws i)))

    ltMN : Lt M0 N0
    ltMN = eqSubst (\ z -> Lt M0 z) (eqSym eN0) (ltSelf M0)

    coll : Collide prog N0
    coll = pigeonhole prog N0 M0 bd ltMN

    i0 : Nat
    i0 = Collide.i_idx coll
    j0 : Nat
    j0 = Collide.j_idx coll

    -- same program describes xs i0 and xs j0 .
    progEq : Eq (prog i0) (prog j0)
    progEq = Collide.ix_eq coll

    descJ_at_i : Deriv (eqF (ap2 runProgN (natCode (prog i0)) (natCode (fuelOf j0)))
                            (ap1 s (natCode (xs j0))))
    descJ_at_i =
      eqSubst (\ q -> Deriv (eqF (ap2 runProgN (natCode q) (natCode (fuelOf j0)))
                                 (ap1 s (natCode (xs j0)))))
              (eqSym progEq) (descOf j0)

    valsEq : Eq (xs i0) (xs j0)
    valsEq = valEq con (prog i0) (xs i0) (xs j0) (fuelOf i0) (fuelOf j0)
                   (descOf i0) descJ_at_i
