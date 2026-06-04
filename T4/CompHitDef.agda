{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.CompHitDef -- the compressibility hit-indicator for the TURING-K /
-- definable predicate (the evalU analogue of T4.TestComp).
--
-- The bounded search ranges over an index  j  that codes a (program, fuel) pair
--   j = pi p n ,   p = Fst j  (the program NAME) ,  n = Snd j  (the fuel) .
-- The per-index test is the decidable  definable(p, z, n)  (T4.Definable),
-- as the AND of three 0/1 indicators (the  andInd  condFork idiom, reused from
-- T4.TestComp):
--   test_def(z, j) =  szLeq(Fst j)                                  -- |p| <= L (param)
--                  .  eqInd(evalU(parse(Fst j), Snd j), s z)         -- run p / n  outputs z
--                  .  eqInd(evalU(parse(Fst j), pred(Snd j)), O) .   -- run p / n-1  still 0
-- So  compHit z = existsHitU z B = 1  iff  some short program describes z within
-- B steps -- the COMPRESSIBILITY predicate, the program p QUANTIFIED inside the
-- bounded search (neg compHit = K(z) > L).
--
-- szLeq : Fun1 (the |.| <= L size indicator) is a MODULE PARAMETER, as in
-- T4.TestComp.Rec (it is  szLeqFun L  with  L  pinned in C.5 / dLen).  evalU /
-- parse / predecessor are CONCRETE; no enum / pairEnum (j IS the pair).
--
-- Deliverables (IndU's interface + the witness firing):
--   test_def_le_one : (z j) -> leq (test_def z j) 1
--   test_def_fires  : from definable's three facts at (Fst j, z, Snd j), test fires
--   compHit         = IndU.compHitOf constB : Fun1
--   compHit_settles : a witness (p0 = pi g_L n0) with leq p0 B -> compHit z = 1  (= h)

module T4.CompHitDef where

open import T4.Base
open import T4.EvalUEval using ( evalU )
open import T4.ProgParse using ( parse )
open import T4.Counting  using ( eqInd ; eqInd_le_one )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.TestComp   using ( andInd ; andInd_fires ; andInd_le_one
                                  ; eqInd_at_eq ; leqLeftCong )
import T4.ExistsHitU

open import BRA3.Church          using ( pi ; predecessor )
open import BRA3.ChurchLeq       using ( leq )

module Rec
  (szLeq : Fun1)                                                   -- |.| <= L indicator (C.5/dLen)
  (szLeq_le_one : (c : Term) -> Deriv (leq (ap1 szLeq c) (ap1 s O)))
  where

  ----------------------------------------------------------------------
  -- andInd as a Fun2 (copied verbatim from T4.TestComp.Rec; generic).
  andIndF : Fun2
  andIndF = Fan (Fan v (Lift1 o) pi) Const condFork

  andIndF_eq :
    (p q : Term) -> Deriv (eqF (ap2 andIndF p q) (andInd p q))
  andIndF_eq p q =
    let inner_left : Deriv (eqF (ap2 (Fan v (Lift1 o) pi) p q) (ap2 pi q O))
        inner_left = ruleTrans (axFan v (Lift1 o) pi p q)
                       (ruleTrans (congL pi (ap2 (Lift1 o) p q) (ax_v p q))
                                  (congR pi q (ruleTrans (axLift o p q) (ax_o p))))
    in ruleTrans (axFan (Fan v (Lift1 o) pi) Const condFork p q)
         (ruleTrans (congL condFork (ap2 Const p q) inner_left)
                    (congR condFork (ap2 pi q O) (axConst p q)))

  ----------------------------------------------------------------------
  -- SECTION 1.  The reads (Fun1 of the index  j ).

  -- evalU(parse(Fst j), Snd j)
  evalRead : Fun1
  evalRead = C evalU (compose1U parse Fst) Snd
  evalRead_eq :
    (j : Term) ->
    Deriv (eqF (ap1 evalRead j) (ap2 evalU (ap1 parse (ap1 Fst j)) (ap1 Snd j)))
  evalRead_eq j =
    ruleTrans (ax_C evalU (compose1U parse Fst) Snd j)
              (congL evalU (ap1 Snd j) (axComp parse Fst j))

  -- evalU(parse(Fst j), pred(Snd j))
  predRead : Fun1
  predRead = C evalU (compose1U parse Fst) (compose1U predecessor Snd)
  predRead_eq :
    (j : Term) ->
    Deriv (eqF (ap1 predRead j)
               (ap2 evalU (ap1 parse (ap1 Fst j)) (ap1 predecessor (ap1 Snd j))))
  predRead_eq j =
    ruleTrans (ax_C evalU (compose1U parse Fst) (compose1U predecessor Snd) j)
              (ruleTrans (congL evalU (ap1 (compose1U predecessor Snd) j) (axComp parse Fst j))
                         (congR evalU (ap1 parse (ap1 Fst j)) (axComp predecessor Snd j)))

  -- szLeq(Fst j)
  szF : Fun1
  szF = compose1U szLeq Fst
  szF_eq : (j : Term) -> Deriv (eqF (ap1 szF j) (ap1 szLeq (ap1 Fst j)))
  szF_eq j = axComp szLeq Fst j

  ----------------------------------------------------------------------
  -- SECTION 2.  The three factors as Fun2.

  -- szPart(z, j) = szLeq(Fst j)
  szPart : Fun2
  szPart = Lift2 szF
  szPart_eq : (z j : Term) -> Deriv (eqF (ap2 szPart z j) (ap1 szLeq (ap1 Fst j)))
  szPart_eq z j = ruleTrans (axLift2 szF z j) (szF_eq j)

  -- evalEq(z, j) = eqInd(evalRead j, s z)
  evalEqPart : Fun2
  evalEqPart = Fan (Lift2 evalRead) (Lift1 s) eqIndF
  evalEqPart_eq :
    (z j : Term) -> Deriv (eqF (ap2 evalEqPart z j) (eqInd (ap1 evalRead j) (ap1 s z)))
  evalEqPart_eq z j =
    ruleTrans (axFan (Lift2 evalRead) (Lift1 s) eqIndF z j)
      (ruleTrans (congL eqIndF (ap2 (Lift1 s) z j) (axLift2 evalRead z j))
        (ruleTrans (congR eqIndF (ap1 evalRead j) (axLift s z j))
                   (eqIndF_eq (ap1 evalRead j) (ap1 s z))))

  -- predEq(z, j) = eqInd(predRead j, O)
  predEqPart : Fun2
  predEqPart = Fan (Lift2 predRead) (Lift1 o) eqIndF
  predEqPart_eq :
    (z j : Term) -> Deriv (eqF (ap2 predEqPart z j) (eqInd (ap1 predRead j) O))
  predEqPart_eq z j =
    ruleTrans (axFan (Lift2 predRead) (Lift1 o) eqIndF z j)
      (ruleTrans (congL eqIndF (ap2 (Lift1 o) z j) (axLift2 predRead z j))
        (ruleTrans (congR eqIndF (ap1 predRead j) (axLift o z j))
          (ruleTrans (congR eqIndF (ap1 predRead j) (ax_o z))
                     (eqIndF_eq (ap1 predRead j) O))))

  ----------------------------------------------------------------------
  -- SECTION 3.  test_def = AND of the three factors.

  test_def : Fun2
  test_def = Fan (Fan szPart evalEqPart andIndF) predEqPart andIndF

  -- abbreviations for the three 0/1 indicator values.
  szI : Term -> Term
  szI j = ap1 szLeq (ap1 Fst j)
  evalI : Term -> Term -> Term
  evalI z j = eqInd (ap1 evalRead j) (ap1 s z)
  predI : Term -> Term
  predI j = eqInd (ap1 predRead j) O

  test_def_eq :
    (z j : Term) ->
    Deriv (eqF (ap2 test_def z j)
               (andInd (andInd (szI j) (evalI z j)) (predI j)))
  test_def_eq z j =
    let lhsAnd : Deriv (eqF (ap2 (Fan szPart evalEqPart andIndF) z j)
                            (andInd (szI j) (evalI z j)))
        lhsAnd =
          ruleTrans (axFan szPart evalEqPart andIndF z j)
            (ruleTrans (congL andIndF (ap2 evalEqPart z j) (szPart_eq z j))
              (ruleTrans (congR andIndF (szI j) (evalEqPart_eq z j))
                         (andIndF_eq (szI j) (evalI z j))))
    in ruleTrans (axFan (Fan szPart evalEqPart andIndF) predEqPart andIndF z j)
         (ruleTrans (congL andIndF (ap2 predEqPart z j) lhsAnd)
           (ruleTrans (congR andIndF (andInd (szI j) (evalI z j)) (predEqPart_eq z j))
                      (andIndF_eq (andInd (szI j) (evalI z j)) (predI j))))

  ----------------------------------------------------------------------
  -- SECTION 4.  test_def is 0/1, and it fires at a definability witness.

  test_def_le_one :
    (z j : Term) -> Deriv (leq (ap2 test_def z j) (ap1 s O))
  test_def_le_one z j =
    leqLeftCong (ap2 test_def z j)
      (andInd (andInd (szI j) (evalI z j)) (predI j)) (ap1 s O)
      (test_def_eq z j)
      (andInd_le_one (andInd (szI j) (evalI z j)) (predI j)
        (andInd_le_one (szI j) (evalI z j)
          (szLeq_le_one (ap1 Fst j))
          (eqInd_le_one (ap1 evalRead j) (ap1 s z)))
        (eqInd_le_one (ap1 predRead j) O))

  -- the witness firing: at an index  j  whose program (Fst j) is short and whose
  -- run outputs  z  at fuel (Snd j) and  0  at fuel (Snd j)-1, the test fires.
  test_def_fires :
    (z j : Term) ->
    Deriv (eqF (ap1 szLeq (ap1 Fst j)) (ap1 s O)) ->                                   -- |Fst j| <= L
    Deriv (eqF (ap2 evalU (ap1 parse (ap1 Fst j)) (ap1 Snd j)) (ap1 s z)) ->           -- outputs z at n
    Deriv (eqF (ap2 evalU (ap1 parse (ap1 Fst j)) (ap1 predecessor (ap1 Snd j))) O) -> -- 0 at n-1
    Deriv (eqF (ap2 test_def z j) (ap1 s O))
  test_def_fires z j szFires evalFires predFires =
    let szI_fires : Deriv (eqF (szI j) (ap1 s O))
        szI_fires = szFires
        -- evalRead j = s z  ;  then  eqInd(s z, s z) = 1  (via the eqIndF Fun2).
        e_eval : Deriv (eqF (ap1 evalRead j) (ap1 s z))
        e_eval = ruleTrans (evalRead_eq j) evalFires
        evalI_fires : Deriv (eqF (evalI z j) (ap1 s O))
        evalI_fires =
          ruleTrans (ruleSym (eqIndF_eq (ap1 evalRead j) (ap1 s z)))
            (ruleTrans (congL eqIndF (ap1 s z) e_eval)
              (ruleTrans (eqIndF_eq (ap1 s z) (ap1 s z))
                         (eqInd_at_eq (ap1 s z))))
        e_pred : Deriv (eqF (ap1 predRead j) O)
        e_pred = ruleTrans (predRead_eq j) predFires
        predI_fires : Deriv (eqF (predI j) (ap1 s O))
        predI_fires =
          ruleTrans (ruleSym (eqIndF_eq (ap1 predRead j) O))
            (ruleTrans (congL eqIndF O e_pred)
              (ruleTrans (eqIndF_eq O O)
                         (eqInd_at_eq O)))
    in ruleTrans (test_def_eq z j)
         (andInd_fires (andInd (szI j) (evalI z j)) (predI j)
           (andInd_fires (szI j) (evalI z j) szI_fires evalI_fires)
           predI_fires)

  ----------------------------------------------------------------------
  -- SECTION 5.  Instantiate the bounded-exists machine at  test_def .

  open T4.ExistsHitU.IndU test_def test_def_le_one public
    using ( existsHitU ; existsHitU_settles ; compHitOf ; compHitOf_eq )
