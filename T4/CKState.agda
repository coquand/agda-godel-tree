{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CKState -- the data layer of the CK STACK MACHINE verifier (Thierry's
-- choice: reuse BRA's proven iter/Reaches vehicle; assemble the trace POSTORDER
-- via explicit Build markers, no after-the-fact flat-log reassembly).
--
--   state = (worklist , outstack , flag)
--         = Pair worklist (Pair outstack flag)
--
-- worklist items are tagged:
--   Check:  chk p t u = Pair (natCode 0) (Pair p (Pair t u))   -- obligation p:t=>u
--   Build:  bld g t u = Pair (natCode 1) (Pair g (Pair t u))   -- assemble marker
--             ( g = constructor tag; arity is determined by g; t,u = boundary )
-- Both share the inner shape  Pair A (Pair B C) , so generic accessors
-- itemKind / itemA / itemB / itemC serve both (chkP = bldTag = itemA, etc.).
-- worklist and outstack are CodedLists (T4.CodedList codeNil/codeCons); the
-- outstack holds the already-built premise traces, popped by a Build marker.
--
-- One step (defined later as a Fun1, run by  iter ): pop the head item; if
-- Check, decode the proof's outer ctor, on success push its premises'
-- Check items then a Build marker (so premises are processed first, postorder);
-- if Build, pop the arity-many premise traces off outstack, assemble
-- Node(tag, D1..Dk), check boundary, push onto outstack.  Accept when worklist
-- empties with one trace on outstack and flag ok.
--
-- This file: coding + accessors + Deriv equations (axFst / axSnd only).
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CKState where

open import T4.Base

------------------------------------------------------------------------
-- SECTION 1.  Worklist items (shared inner shape  Pair A (Pair B C) ).

itemKind : Term -> Term
itemKind i = ap1 Fst i

itemA : Term -> Term
itemA i = ap1 Fst (ap1 Snd i)

itemB : Term -> Term
itemB i = ap1 Fst (ap1 Snd (ap1 Snd i))

itemC : Term -> Term
itemC i = ap1 Snd (ap1 Snd (ap1 Snd i))

chk : Term -> Term -> Term -> Term
chk p t uu = ap2 Pair (natCode 0) (ap2 Pair p (ap2 Pair t uu))

bld : Term -> Term -> Term -> Term
bld g t uu = ap2 Pair (natCode 1) (ap2 Pair g (ap2 Pair t uu))

-- Shared inner-decomposition lemma:  Snd (Snd <item with body A,B,C>) = Pair B C .
-- (used to project itemB / itemC).

private
  innerBC : (k a b c : Term) ->
    Deriv (eqF (ap1 Snd (ap1 Snd (ap2 Pair k (ap2 Pair a (ap2 Pair b c)))))
               (ap2 Pair b c))
  innerBC k a b c =
    ruleTrans (cong1 Snd (axSnd k (ap2 Pair a (ap2 Pair b c))))
              (axSnd a (ap2 Pair b c))

------------------------------------------------------------------------
-- SECTION 2.  Check-item equations.

itemKind_chk : (p t uu : Term) -> Deriv (eqF (itemKind (chk p t uu)) (natCode 0))
itemKind_chk p t uu = axFst (natCode 0) (ap2 Pair p (ap2 Pair t uu))

chkP : (p t uu : Term) -> Deriv (eqF (itemA (chk p t uu)) p)
chkP p t uu =
  ruleTrans (cong1 Fst (axSnd (natCode 0) (ap2 Pair p (ap2 Pair t uu))))
            (axFst p (ap2 Pair t uu))

chkT : (p t uu : Term) -> Deriv (eqF (itemB (chk p t uu)) t)
chkT p t uu = ruleTrans (cong1 Fst (innerBC (natCode 0) p t uu)) (axFst t uu)

chkU : (p t uu : Term) -> Deriv (eqF (itemC (chk p t uu)) uu)
chkU p t uu = ruleTrans (cong1 Snd (innerBC (natCode 0) p t uu)) (axSnd t uu)

------------------------------------------------------------------------
-- SECTION 3.  Build-item equations.

itemKind_bld : (g t uu : Term) -> Deriv (eqF (itemKind (bld g t uu)) (natCode 1))
itemKind_bld g t uu = axFst (natCode 1) (ap2 Pair g (ap2 Pair t uu))

bldTag : (g t uu : Term) -> Deriv (eqF (itemA (bld g t uu)) g)
bldTag g t uu =
  ruleTrans (cong1 Fst (axSnd (natCode 1) (ap2 Pair g (ap2 Pair t uu))))
            (axFst g (ap2 Pair t uu))

bldT : (g t uu : Term) -> Deriv (eqF (itemB (bld g t uu)) t)
bldT g t uu = ruleTrans (cong1 Fst (innerBC (natCode 1) g t uu)) (axFst t uu)

bldU : (g t uu : Term) -> Deriv (eqF (itemC (bld g t uu)) uu)
bldU g t uu = ruleTrans (cong1 Snd (innerBC (natCode 1) g t uu)) (axSnd t uu)

------------------------------------------------------------------------
-- SECTION 4.  States:  mkState wl out flag = Pair wl (Pair out flag) .

mkState : Term -> Term -> Term -> Term
mkState wl out flag = ap2 Pair wl (ap2 Pair out flag)

sWork : Term -> Term
sWork st = ap1 Fst st

sOut : Term -> Term
sOut st = ap1 Fst (ap1 Snd st)

sFlag : Term -> Term
sFlag st = ap1 Snd (ap1 Snd st)

sWork_eq : (wl out flag : Term) -> Deriv (eqF (sWork (mkState wl out flag)) wl)
sWork_eq wl out flag = axFst wl (ap2 Pair out flag)

sOut_eq : (wl out flag : Term) -> Deriv (eqF (sOut (mkState wl out flag)) out)
sOut_eq wl out flag =
  ruleTrans (cong1 Fst (axSnd wl (ap2 Pair out flag))) (axFst out flag)

sFlag_eq : (wl out flag : Term) -> Deriv (eqF (sFlag (mkState wl out flag)) flag)
sFlag_eq wl out flag =
  ruleTrans (cong1 Snd (axSnd wl (ap2 Pair out flag))) (axSnd out flag)
