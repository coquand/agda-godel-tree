{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmAbundance -- abundance of incompressible numbers (the quantitative
-- strengthening of T4.KolmIncompress).
--
-- The compressible numbers are FEW: there is no injective sequence of
-- 3^(L+1)+1 distinct numbers that are all K <= L.  Equivalently, every block of
-- 3^(L+1)+1 DISTINCT numbers contains an incompressible one -- so incompressible
-- numbers are unavoidable in any large distinct collection (e.g. tiling
-- [0, 3^(L+c)) into 3^(c-1) such blocks yields that many incompressibles).
--
--   compressibleBounded : con -> (L) (xs) (xs injective on [0,3^(L+1)]) ->
--                         NOT (all of xs 0 .. xs 3^(L+1) are K <= L)
--
-- Setting xs = id recovers T4.KolmIncompress.incompressible.  Only simple
-- consistency is used.  ( A literal POSITIVE count of incompressibles is not
-- constructively available -- Kle quantifies over unbounded fuel, hence is not
-- decidable -- so the cardinality bound on the COMPRESSIBLE side is the honest
-- form. )

module T4.KolmAbundance where

open import T4.Base
open import T4.ParseN          using ( runProgN )
open import T4.TreeDigitsSize  using ( pow3 )
open import T4.KolmLog         using ( pow3_ge1 )
open import T4.Code            using ( falseF )
open import T4.KolmNumReflect  using ( Sg ; mkSg )
open import T4.SurpriseG2.NumNeq using ( Not )
open import T4.SurpriseG2.MetaPigeonhole using
  ( Lt ; ltSelf ; ltIrrefl ; ltTrans
  ; NatCmp ; ltC ; eqC ; gtC ; natCmp
  ; Collide ; pigeonhole )
open import T4.KolmCount       using ( And ; Kle ; valEq ; pos_to_suc )

------------------------------------------------------------------------
-- injectivity of xs on the index range [0, suc N).

Injective : (Nat -> Nat) -> Nat -> Set
Injective xs N =
  (i j : Nat) -> Lt i (suc N) -> Lt j (suc N) -> Eq (xs i) (xs j) -> Eq i j

------------------------------------------------------------------------
-- THE abundance bound: no injective block of 3^(L+1)+1 compressible values.

compressibleBounded :
  Not (Deriv falseF) -> (L : Nat) (xs : Nat -> Nat) ->
  Injective xs (pow3 (suc L)) ->
  ((i : Nat) -> Lt i (suc (pow3 (suc L))) -> Kle L (xs i)) ->
  Empty
compressibleBounded con L xs inj allK = Collide.i_neq coll i0eqj0
  where
    N0 : Nat
    N0 = pow3 (suc L)

    posN0 : Sg Nat (\ M -> Eq N0 (suc M))
    posN0 = pos_to_suc (pow3_ge1 (suc L))
    M0 : Nat
    M0 = Sg.fst posN0
    eN0 : Eq N0 (suc M0)
    eN0 = Sg.snd posN0

    progAt : (i : Nat) -> NatCmp i (suc N0) -> Nat
    progAt i (ltC h) = Sg.fst (allK i h)
    progAt i (eqC _) = zero
    progAt i (gtC _) = zero

    prog : Nat -> Nat
    prog i = progAt i (natCmp i (suc N0))

    bdAt : (i : Nat) (c : NatCmp i (suc N0)) -> Lt i (suc N0) -> Lt (progAt i c) (suc M0)
    bdAt i (ltC h) _  = eqSubst (\ z -> Lt (Sg.fst (allK i h)) z) eN0
                                (And.p1 (Sg.snd (allK i h)))
    bdAt i (eqC e) lt = emptyElim (ltIrrefl (eqSubst (\ z -> Lt z (suc N0)) e lt))
    bdAt i (gtC g) lt = emptyElim (ltIrrefl (ltTrans lt g))

    bd : (i : Nat) -> Lt i (suc N0) -> Lt (prog i) (suc M0)
    bd i lt = bdAt i (natCmp i (suc N0)) lt

    ltMN : Lt M0 N0
    ltMN = eqSubst (\ z -> Lt M0 z) (eqSym eN0) (ltSelf M0)

    coll : Collide prog N0
    coll = pigeonhole prog N0 M0 bd ltMN

    i0 : Nat
    i0 = Collide.i_idx coll
    j0 : Nat
    j0 = Collide.j_idx coll

    -- run-evidence at i, with VALUE xs i and program prog i.
    descAt : (i : Nat) (c : NatCmp i (suc N0)) -> Lt i (suc N0) ->
      Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (progAt i c)) (natCode Nn))
                                 (ap1 s (natCode (xs i)))))
    descAt i (ltC h) _  = And.p2 (Sg.snd (allK i h))
    descAt i (eqC e) lt = emptyElim (ltIrrefl (eqSubst (\ z -> Lt z (suc N0)) e lt))
    descAt i (gtC g) lt = emptyElim (ltIrrefl (ltTrans lt g))

    desc : (i : Nat) -> Lt i (suc N0) ->
      Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (prog i)) (natCode Nn))
                                 (ap1 s (natCode (xs i)))))
    desc i lt = descAt i (natCmp i (suc N0)) lt

    progEq : Eq (prog i0) (prog j0)
    progEq = Collide.ix_eq coll

    di : Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (prog i0)) (natCode Nn))
                                    (ap1 s (natCode (xs i0)))))
    di = desc i0 (Collide.i_lt coll)
    dj : Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (prog j0)) (natCode Nn))
                                    (ap1 s (natCode (xs j0)))))
    dj = desc j0 (Collide.j_lt coll)

    dj_at_i : Deriv (eqF (ap2 runProgN (natCode (prog i0)) (natCode (Sg.fst dj)))
                         (ap1 s (natCode (xs j0))))
    dj_at_i = eqSubst (\ q -> Deriv (eqF (ap2 runProgN (natCode q) (natCode (Sg.fst dj)))
                                         (ap1 s (natCode (xs j0)))))
                      (eqSym progEq) (Sg.snd dj)

    -- same program describes xs i0 and xs j0  =>  xs i0 = xs j0  =>  i0 = j0 (inj).
    valsEq : Eq (xs i0) (xs j0)
    valsEq = valEq con (prog i0) (xs i0) (xs j0) (Sg.fst di) (Sg.fst dj)
                   (Sg.snd di) dj_at_i

    i0eqj0 : Eq i0 j0
    i0eqj0 = inj i0 j0 (Collide.i_lt coll) (Collide.j_lt coll) valsEq

------------------------------------------------------------------------
-- corollary: every injective block of 3^(L+1)+1 numbers has an incompressible
-- one ( negative form: they cannot all be compressible ).

blockHasIncompressible :
  Not (Deriv falseF) -> (L : Nat) (xs : Nat -> Nat) ->
  Injective xs (pow3 (suc L)) ->
  Not ((i : Nat) -> Lt i (suc (pow3 (suc L))) -> Kle L (xs i))
blockHasIncompressible con L xs inj allK =
  compressibleBounded con L xs inj allK
