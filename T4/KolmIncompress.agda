{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmIncompress -- incompressible numbers exist, and K is unbounded.
--
-- From the counting bound:  among [0, 3^(L+1)] there are 3^(L+1)+1 numbers but
-- at most 3^(L+1) of them have K <= L, so SOME number <= 3^(L+1) has K > L.
--
-- Constructively (Kle is a Sigma over an unbounded fuel, hence not decidable),
-- the statement is the negative form:
--
--   incompressible : con -> (L) -> NOT (all i <= 3^(L+1) have Kle L i)
--   kUnbounded     : con -> (L) -> NOT (all i have Kle L i)
--
-- i.e. not every number up to 3^(L+1) is L-compressible -- there is an
-- incompressible one -- and K is unbounded.  Only simple consistency is used.

module T4.KolmIncompress where

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
-- "every number up to 3^(L+1) is L-compressible".

AllCompressible : Nat -> Set
AllCompressible L = (i : Nat) -> Lt i (suc (pow3 (suc L))) -> Kle L i

------------------------------------------------------------------------
-- THE incompressibility theorem (negative form).

incompressible :
  Not (Deriv falseF) -> (L : Nat) -> Not (AllCompressible L)
incompressible con L allK = ltIrrefl collapse
  where
    N0 : Nat
    N0 = pow3 (suc L)

    posN0 : Sg Nat (\ M -> Eq N0 (suc M))
    posN0 = pos_to_suc (pow3_ge1 (suc L))
    M0 : Nat
    M0 = Sg.fst posN0
    eN0 : Eq N0 (suc M0)
    eN0 = Sg.snd posN0

    -- the program of i (junk outside the range); decided by natCmp.
    progAt : (i : Nat) -> NatCmp i (suc N0) -> Nat
    progAt i (ltC h) = Sg.fst (allK i h)
    progAt i (eqC _) = zero
    progAt i (gtC _) = zero

    prog : Nat -> Nat
    prog i = progAt i (natCmp i (suc N0))

    -- bound: prog i < suc M0 (= 3^(L+1)) for i in range.
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

    -- the run-evidence at i, extracted through the same natCmp decision so the
    -- program matches  prog i = progAt i (natCmp ...) .
    descAt : (i : Nat) (c : NatCmp i (suc N0)) -> Lt i (suc N0) ->
      Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (progAt i c)) (natCode Nn))
                                 (ap1 s (natCode i))))
    descAt i (ltC h) _  = And.p2 (Sg.snd (allK i h))
    descAt i (eqC e) lt = emptyElim (ltIrrefl (eqSubst (\ z -> Lt z (suc N0)) e lt))
    descAt i (gtC g) lt = emptyElim (ltIrrefl (ltTrans lt g))

    desc : (i : Nat) -> Lt i (suc N0) ->
      Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (prog i)) (natCode Nn))
                                 (ap1 s (natCode i))))
    desc i lt = descAt i (natCmp i (suc N0)) lt

    progEq : Eq (prog i0) (prog j0)
    progEq = Collide.ix_eq coll

    di : Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (prog i0)) (natCode Nn))
                                    (ap1 s (natCode i0))))
    di = desc i0 (Collide.i_lt coll)
    dj : Sg Nat (\ Nn -> Deriv (eqF (ap2 runProgN (natCode (prog j0)) (natCode Nn))
                                    (ap1 s (natCode j0))))
    dj = desc j0 (Collide.j_lt coll)

    -- rewrite dj's program to prog i0 (= prog j0).
    dj_at_i : Deriv (eqF (ap2 runProgN (natCode (prog i0)) (natCode (Sg.fst dj)))
                         (ap1 s (natCode j0)))
    dj_at_i = eqSubst (\ q -> Deriv (eqF (ap2 runProgN (natCode q) (natCode (Sg.fst dj)))
                                         (ap1 s (natCode j0))))
                      (eqSym progEq) (Sg.snd dj)

    -- same program describes i0 and j0  =>  i0 = j0  (determinism + consistency).
    i0eqj0 : Eq i0 j0
    i0eqj0 = valEq con (prog i0) i0 j0 (Sg.fst di) (Sg.fst dj) (Sg.snd di) dj_at_i

    -- but the collision says i0 /= j0 ; with i0 = j0 we get Lt j0 j0.
    collapse : Lt j0 j0
    collapse = emptyElim (Collide.i_neq coll i0eqj0)

------------------------------------------------------------------------
-- K is unbounded: for every L, not every number is L-compressible.

kUnbounded :
  Not (Deriv falseF) -> (L : Nat) -> Not ((i : Nat) -> Kle L i)
kUnbounded con L allK = incompressible con L (\ i _ -> allK i)
