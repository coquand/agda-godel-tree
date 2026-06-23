{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CheckState -- the DATA LAYER of the fuel-driven worklist verifier for
-- parallel-reduction proof codes (the CK-machine route that avoids the global
-- fold-unfold-at-opaque-code obligation: the trusted recursion is on FUEL via
-- BRA3.CourseOfValues.iter, and the only opaque lemma needed is the LOCAL
-- one-step decode -- T4.SizedProofDec's pTag/pL/pR equations).
--
-- A WORK ITEM is an obligation "proof code  p  proves  t => u":
--     wItem p t uu = Pair p (Pair t u)
-- A STATE is a flag plus a worklist (a CodedList of work items):
--     mkSt flag wl = Pair flag wl          flag: O = ok-so-far, s O = rejected
-- The worklist uses T4.CodedList (codeNil / codeCons).  One machine step pops
-- the head item, decodes its proof's outer constructor (pTag), checks the local
-- shape, and pushes the immediate premises as new work items (cons), updating
-- the flag; checkPar p t u = read the flag of  iter step (mkSt O [wItem p t uu])
-- (size p + 1) .  This file delivers the coding + accessors + their Deriv
-- equations (axFst / axSnd only).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CheckState where

open import T4.Base

------------------------------------------------------------------------
-- SECTION 1.  Work items:  wItem p t uu = Pair p (Pair t u) .

wItem : Term -> Term -> Term -> Term
wItem p t uu = ap2 Pair p (ap2 Pair t uu)

wProof : Term -> Term
wProof i = ap1 Fst i

wSrc : Term -> Term
wSrc i = ap1 Fst (ap1 Snd i)

wTgt : Term -> Term
wTgt i = ap1 Snd (ap1 Snd i)

wProof_eq : (p t uu : Term) -> Deriv (eqF (wProof (wItem p t uu)) p)
wProof_eq p t uu = axFst p (ap2 Pair t uu)

wSrc_eq : (p t uu : Term) -> Deriv (eqF (wSrc (wItem p t uu)) t)
wSrc_eq p t uu =
  ruleTrans (cong1 Fst (axSnd p (ap2 Pair t uu))) (axFst t uu)

wTgt_eq : (p t uu : Term) -> Deriv (eqF (wTgt (wItem p t uu)) uu)
wTgt_eq p t uu =
  ruleTrans (cong1 Snd (axSnd p (ap2 Pair t uu))) (axSnd t uu)

------------------------------------------------------------------------
-- SECTION 2.  States:  mkSt flag wl = Pair flag wl .

mkSt : Term -> Term -> Term
mkSt flag wl = ap2 Pair flag wl

stFlag : Term -> Term
stFlag st = ap1 Fst st

stWork : Term -> Term
stWork st = ap1 Snd st

stFlag_eq : (flag wl : Term) -> Deriv (eqF (stFlag (mkSt flag wl)) flag)
stFlag_eq flag wl = axFst flag wl

stWork_eq : (flag wl : Term) -> Deriv (eqF (stWork (mkSt flag wl)) wl)
stWork_eq flag wl = axSnd flag wl
