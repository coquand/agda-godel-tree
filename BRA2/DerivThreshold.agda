{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.DerivThreshold -- BRA2.DerivT re-exported as the BRA2.Deriv API.
--
-- The threshold derivation type DerivT (BRA2.DerivT) restricts tree
-- induction to atomic-equation predicates.  This module re-exports
-- DerivT under the name Deriv, providing the same surface API as
-- BRA2.Deriv but with the threshold restriction:
--
--   open import BRA2.DerivThreshold
--   -- Now `Deriv P` denotes a DerivT proof of P, which is also a
--   -- threshold-system proof (no compound-IND).
--
-- Files in the GoedelIIFull closure are migrated to this module by
-- replacing  open import BRA2.Deriv  with
--  open import BRA2.DerivThreshold .  Constructor names match
-- (axI, axFst, etc.), so the bulk of proof scripts requires no
-- changes.  The atomic-IND derived rules ruleIndBTAtomic /
-- ruleIndBT2Atomic become aliases for indBT / indBT2 (which are
-- DerivT's primitive atomic-IND constructors).
--
-- Goal of this migration:
--
--   godelII : Deriv Con -> Deriv bot
--           = godelII_T : DerivT Con -> DerivT bot
--
-- i.e., the threshold system itself proves Goedel II end-to-end.
--
-- Files outside the closure (BRA2.DecodeAt, BRA2.Thm12.* legacy)
-- keep using BRA2.Deriv (the full system); the two modules coexist.

module BRA2.DerivThreshold where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula

------------------------------------------------------------------------
-- Re-export DerivT under the surface name Deriv.

open import BRA2.DerivT public
  renaming
    ( DerivT to Deriv
    ; indBT  to ruleIndBTAtomic
    ; indBT2 to ruleIndBT2Atomic
    )

------------------------------------------------------------------------
-- Convenience abbreviation:  eqF t u  =  atomic (eqn t u) .

eqF : Term -> Term -> Formula
eqF t u = atomic (eqn t u)

------------------------------------------------------------------------
-- Derived axKT (IsValue-indexed): ported from BRA2.Deriv.

axKT : (v : Term) -> IsValue v -> (x : Term) ->
       Deriv (atomic (eqn (ap1 (KT v) x) v))
axKT .O                valO                 x = axZ x
axKT (ap2 Pair a b)   (valNd .a .b va vb)   x =
  let s1 : Deriv (atomic (eqn (ap1 (Comp2 Pair (KT a) (KT b)) x)
                              (ap2 Pair (ap1 (KT a) x) (ap1 (KT b) x))))
      s1 = axComp2 Pair (KT a) (KT b) x
      ihA = axKT a va x
      ihB = axKT b vb x
      s2 = congL Pair (ap1 (KT b) x) ihA
      s3 = congR Pair a ihB
  in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Derived axRecPLf / axRecPNd.

axRecPLf : (s : Fun2) (p : Term) ->
           Deriv (atomic (eqn (ap2 (RecP s) p O) O))
axRecPLf s p = ruleTrans (axTreeRecLf Z s p) (axZ p)

axRecPNd : (s : Fun2) (p a b : Term) ->
           Deriv (atomic (eqn (ap2 (RecP s) p (ap2 Pair a b))
                               (ap2 s (ap2 Pair p (ap2 Pair a b))
                                      (ap2 Pair (ap2 (RecP s) p a)
                                                (ap2 (RecP s) p b)))))
axRecPNd s p a b = axTreeRecNd Z s p a b

------------------------------------------------------------------------
-- Derived axRecLf / axRecNd via treeRec bridges.

recRedTo_treeRec : (s : Fun2) (x : Term) ->
                   Deriv (atomic (eqn (ap1 (Rec s) x)
                                      (ap2 (treeRec Z s) O x)))
recRedTo_treeRec s x =
  let e1 : Deriv (atomic (eqn (ap1 (Rec s) x)
                              (ap2 (treeRec Z s) (ap1 Z x) (ap1 I x))))
      e1 = axComp2 (treeRec Z s) Z I x
      e2 : Deriv (atomic (eqn (ap2 (treeRec Z s) (ap1 Z x) (ap1 I x))
                              (ap2 (treeRec Z s) O (ap1 I x))))
      e2 = congL (treeRec Z s) (ap1 I x) (axZ x)
      e3 : Deriv (atomic (eqn (ap2 (treeRec Z s) O (ap1 I x))
                              (ap2 (treeRec Z s) O x)))
      e3 = congR (treeRec Z s) O (axI x)
  in ruleTrans e1 (ruleTrans e2 e3)

treeRecOTo_rec : (s : Fun2) (x : Term) ->
                 Deriv (atomic (eqn (ap2 (treeRec Z s) O x)
                                    (ap1 (Rec s) x)))
treeRecOTo_rec s x = ruleSym (recRedTo_treeRec s x)

axRecLf : (s : Fun2) ->
          Deriv (atomic (eqn (ap1 (Rec s) O) O))
axRecLf s =
  let e1 : Deriv (atomic (eqn (ap1 (Rec s) O) (ap2 (treeRec Z s) O O)))
      e1 = recRedTo_treeRec s O
      e2 : Deriv (atomic (eqn (ap2 (treeRec Z s) O O) (ap1 Z O)))
      e2 = axTreeRecLf Z s O
      e3 : Deriv (atomic (eqn (ap1 Z O) O))
      e3 = axZ O
  in ruleTrans e1 (ruleTrans e2 e3)

axRecNd : (s : Fun2) (a b : Term) ->
          Deriv (atomic (eqn (ap1 (Rec s) (ap2 Pair a b))
                              (ap2 s (ap2 Pair O (ap2 Pair a b))
                                     (ap2 Pair (ap1 (Rec s) a)
                                               (ap1 (Rec s) b)))))
axRecNd s a b =
  let pab : Term
      pab = ap2 Pair a b
      e1 : Deriv (atomic (eqn (ap1 (Rec s) pab) (ap2 (treeRec Z s) O pab)))
      e1 = recRedTo_treeRec s pab
      e2 : Deriv (atomic (eqn (ap2 (treeRec Z s) O pab)
                              (ap2 s (ap2 Pair O pab)
                                     (ap2 Pair (ap2 (treeRec Z s) O a)
                                               (ap2 (treeRec Z s) O b)))))
      e2 = axTreeRecNd Z s O a b
      bridgeA : Deriv (atomic (eqn (ap2 (treeRec Z s) O a) (ap1 (Rec s) a)))
      bridgeA = treeRecOTo_rec s a
      bridgeB : Deriv (atomic (eqn (ap2 (treeRec Z s) O b) (ap1 (Rec s) b)))
      bridgeB = treeRecOTo_rec s b
      e3a : Deriv (atomic (eqn (ap2 Pair (ap2 (treeRec Z s) O a)
                                         (ap2 (treeRec Z s) O b))
                               (ap2 Pair (ap1 (Rec s) a)
                                         (ap2 (treeRec Z s) O b))))
      e3a = congL Pair (ap2 (treeRec Z s) O b) bridgeA
      e3b : Deriv (atomic (eqn (ap2 Pair (ap1 (Rec s) a)
                                         (ap2 (treeRec Z s) O b))
                               (ap2 Pair (ap1 (Rec s) a)
                                         (ap1 (Rec s) b))))
      e3b = congR Pair (ap1 (Rec s) a) bridgeB
      e3 : Deriv (atomic (eqn (ap2 Pair (ap2 (treeRec Z s) O a)
                                         (ap2 (treeRec Z s) O b))
                               (ap2 Pair (ap1 (Rec s) a)
                                         (ap1 (Rec s) b))))
      e3 = ruleTrans e3a e3b
      e4 : Deriv (atomic (eqn (ap2 s (ap2 Pair O pab)
                                     (ap2 Pair (ap2 (treeRec Z s) O a)
                                               (ap2 (treeRec Z s) O b)))
                              (ap2 s (ap2 Pair O pab)
                                     (ap2 Pair (ap1 (Rec s) a)
                                               (ap1 (Rec s) b)))))
      e4 = congR s (ap2 Pair O pab) e3
  in ruleTrans e1 (ruleTrans e2 e4)

------------------------------------------------------------------------
-- Derived classical lemmas.  Lukasiewicz form.

private
  identP : (P : Formula) -> Deriv (P imp P)
  identP P =
    mp (mp (axS P (P imp P) P) (axK P (P imp P))) (axK P P)

  liftP : (R : Formula) {Q : Formula} -> Deriv Q -> Deriv (R imp Q)
  liftP R D = mp (axK _ R) D

  bComb : {P Q R : Formula} ->
          Deriv (P imp (Q imp R)) ->
          Deriv (P imp Q) ->
          Deriv (P imp R)
  bComb {P} {Q} {R} D1 D2 = mp (mp (axS P Q R) D1) D2

  bCombTwo : {P1 P2 Q R : Formula} ->
             Deriv (P1 imp (P2 imp (Q imp R))) ->
             Deriv (P1 imp (P2 imp Q)) ->
             Deriv (P1 imp (P2 imp R))
  bCombTwo {P1} {P2} {Q} {R} D1 D2 =
    bComb (bComb (liftP P1 (axS P2 Q R)) D1) D2

  compI : {X Y W : Formula} ->
          Deriv (X imp Y) -> Deriv (Y imp W) -> Deriv (X imp W)
  compI {X} {Y} {W} h1 h2 = bComb (liftP X h2) h1

------------------------------------------------------------------------
-- DNE :  ~~A -> A .

DNE : (A : Formula) -> Deriv ((not (not A)) imp A)
DNE A =
  let
    H : Formula
    H = not (not A)

    U : Formula
    U = not A

    V : Formula
    V = not (not (not A))

    W : Formula
    W = not (not (not (not A)))

    s1  : Deriv ((W imp H) imp (U imp V))
    s1  = axNeg V U

    s2  : Deriv (((W imp H) imp (U imp V)) imp (H imp ((W imp H) imp (U imp V))))
    s2  = axK ((W imp H) imp (U imp V)) H

    s3  : Deriv (H imp ((W imp H) imp (U imp V)))
    s3  = mp s2 s1

    s4  : Deriv ((H imp ((W imp H) imp (U imp V)))
                   imp ((H imp (W imp H)) imp (H imp (U imp V))))
    s4  = axS H (W imp H) (U imp V)

    s5  : Deriv ((H imp (W imp H)) imp (H imp (U imp V)))
    s5  = mp s4 s3

    s6  : Deriv (H imp (W imp H))
    s6  = axK H W

    s7  : Deriv (H imp (U imp V))
    s7  = mp s5 s6

    s8  : Deriv ((U imp V) imp (H imp A))
    s8  = axNeg A H

    s9  : Deriv (((U imp V) imp (H imp A)) imp (H imp ((U imp V) imp (H imp A))))
    s9  = axK ((U imp V) imp (H imp A)) H

    s10 : Deriv (H imp ((U imp V) imp (H imp A)))
    s10 = mp s9 s8

    s11 : Deriv ((H imp ((U imp V) imp (H imp A)))
                  imp ((H imp (U imp V)) imp (H imp (H imp A))))
    s11 = axS H (U imp V) (H imp A)

    s12 : Deriv ((H imp (U imp V)) imp (H imp (H imp A)))
    s12 = mp s11 s10

    s13 : Deriv (H imp (H imp A))
    s13 = mp s12 s7

    s14 : Deriv (H imp ((H imp H) imp H))
    s14 = axK H (H imp H)

    s15 : Deriv (H imp (H imp H))
    s15 = axK H H

    s16 : Deriv ((H imp ((H imp H) imp H)) imp ((H imp (H imp H)) imp (H imp H)))
    s16 = axS H (H imp H) H

    s17 : Deriv ((H imp (H imp H)) imp (H imp H))
    s17 = mp s16 s14

    s18 : Deriv (H imp H)
    s18 = mp s17 s15

    s19 : Deriv ((H imp (H imp A)) imp ((H imp H) imp (H imp A)))
    s19 = axS H H A

    s20 : Deriv ((H imp H) imp (H imp A))
    s20 = mp s19 s13
  in mp s20 s18

------------------------------------------------------------------------
-- Q_to_dNeg, dNeg_lift, axContrapos, axExFalso.

private
  Q_to_dNeg : (Q : Formula) -> Deriv (Q imp (not (not Q)))
  Q_to_dNeg Q = mp (axNeg (not (not Q)) Q) (DNE (not Q))

  dNeg_lift : (P Q : Formula) ->
              Deriv ((P imp Q) imp ((not (not P)) imp (not (not Q))))
  dNeg_lift P Q =
    let
      H   : Formula
      H   = P imp Q
      NNP : Formula
      NNP = not (not P)
      NNQ : Formula
      NNQ = not (not Q)

      D1 : Deriv (H imp (NNP imp (NNP imp P)))
      D1 = liftP H (liftP NNP (DNE P))

      D2 : Deriv (H imp (NNP imp NNP))
      D2 = liftP H (identP NNP)

      P_avail : Deriv (H imp (NNP imp P))
      P_avail = bCombTwo D1 D2

      H_avail : Deriv (H imp (NNP imp (P imp Q)))
      H_avail = axK H NNP

      Q_avail : Deriv (H imp (NNP imp Q))
      Q_avail = bCombTwo H_avail P_avail

      QtoNNQ_avail : Deriv (H imp (NNP imp (Q imp NNQ)))
      QtoNNQ_avail = liftP H (liftP NNP (Q_to_dNeg Q))
    in bCombTwo QtoNNQ_avail Q_avail

axContrapos : (P Q : Formula) ->
              Deriv ((P imp Q) imp ((not Q) imp (not P)))
axContrapos P Q =
  compI (dNeg_lift P Q) (axNeg (not P) (not Q))

axExFalso : (P Q : Formula) -> Deriv (P imp ((not P) imp Q))
axExFalso P Q =
  let
    nq_to_np : Deriv (P imp ((not P) imp ((not Q) imp (not P))))
    nq_to_np = liftP P (axK (not P) (not Q))

    axNegLifted : Deriv (P imp ((not P) imp (((not Q) imp (not P)) imp (P imp Q))))
    axNegLifted = liftP P (liftP (not P) (axNeg Q P))

    pq_avail : Deriv (P imp ((not P) imp (P imp Q)))
    pq_avail = bCombTwo axNegLifted nq_to_np

    hypP : Deriv (P imp ((not P) imp P))
    hypP = axK P (not P)
  in bCombTwo pq_avail hypP

------------------------------------------------------------------------
-- Consistency (hyp-less form).

trueT : Term
trueT = O

falseT : Term
falseT = ap2 Pair O O

Consistent : Set
Consistent = Deriv (atomic (eqn trueT falseT)) -> Empty
