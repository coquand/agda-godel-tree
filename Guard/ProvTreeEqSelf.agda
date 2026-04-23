{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.ProvTreeEqSelf -- Prov-form of tree self-equality.
--
--   provTreeEqSelfReify : (t : Tree) ->
--     Prov (atomic (eqn (ap2 TreeEq (reify t) (reify t)) O))
--
-- Parallels  Guard.TreeEqSelfUnify.treeEqSelfReify , lifted to Prov
-- via three axiom-primitives  provAxTreeEqLL , provAxTreeEqNN ,
--  provAxIfLfL  that mirror the corresponding encAx*Corr lemmas.
--
-- Needed by Guard.GodelI to close the self-application diagonal
--  TreeEq (reify cGSCR) (reify cGSCR) = O .
--
-- Induction step: at  t = nd a b ,
--
--   TreeEq (Pair ra rb) (Pair ra rb)
--     = IfLf (TreeEq ra ra) (Pair (TreeEq rb rb) falseT)   [provAxTreeEqNN]
--     = IfLf O              (Pair (TreeEq rb rb) falseT)   [provCongL IfLf + IH_a]
--     = TreeEq rb rb                                         [provAxIfLfL]
--     = O                                                    [IH_b]

module Guard.ProvTreeEqSelf where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForHF using (thmT)
open import Guard.Prov using
  ( Prov ; mkProv ; prov1 ; prov2 ; provCorr ; provPass
  ; provTrans ; provCongL
  )
open import Guard.ProofEncUnify using
  ( encAxTreeEqLL ; encAxTreeEqLLCorr ; encAxTreeEqLLPass
  ; encAxTreeEqNN ; encAxTreeEqNNCorr ; encAxTreeEqNNPass
  ; encAxIfLfL    ; encAxIfLfLCorr    ; encAxIfLfLPass
  )

------------------------------------------------------------------------
-- Tag-number aliases.

private
  n11 : Nat
  n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  n13 : Nat ; n13 = suc (suc n11)
  n16 : Nat ; n16 = suc (suc (suc n13))

------------------------------------------------------------------------
-- provAxTreeEqLL: the closed fact  TreeEq O O = O .

provAxTreeEqLL : Prov (atomic (eqn (ap2 TreeEq O O) O))
provAxTreeEqLL = mkProv
    (reify (natCode n13))
    O
    encAxTreeEqLLCorr
    (\ x rcs -> encAxTreeEqLLPass x rcs)

------------------------------------------------------------------------
-- provAxTreeEqNN: the  TreeEq (Pair a1 a2) (Pair b1 b2)  expansion.

provAxTreeEqNN : (a1 a2 b1 b2 : Term) ->
  Prov (atomic (eqn
    (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
    (ap2 IfLf (ap2 TreeEq a1 b1)
              (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O)))))
provAxTreeEqNN a1 a2 b1 b2 =
  let a1C : Term ; a1C = reify (code a1)
      a2C : Term ; a2C = reify (code a2)
      b1C : Term ; b1C = reify (code b1)
      b2C : Term ; b2C = reify (code b2)
  in mkProv
       (reify (natCode n16))
       (ap2 Pair a1C (ap2 Pair a2C (ap2 Pair b1C b2C)))
       (encAxTreeEqNNCorr a1C a2C b1C b2C)
       (\ x rcs -> encAxTreeEqNNPass a1 a2 b1 b2 x rcs)

------------------------------------------------------------------------
-- provAxIfLfL: the  IfLf O (Pair a b) = a  axiom.

provAxIfLfL : (a b : Term) ->
  Prov (atomic (eqn (ap2 IfLf O (ap2 Pair a b)) a))
provAxIfLfL a b =
  let aC : Term ; aC = reify (code a)
      bC : Term ; bC = reify (code b)
  in mkProv
       (reify (natCode n11))
       (ap2 Pair aC bC)
       (encAxIfLfLCorr aC bC)
       (\ x rcs -> encAxIfLfLPass a b x rcs)

------------------------------------------------------------------------
-- provTreeEqSelfReify: main result.

provTreeEqSelfReify : (t : Tree) ->
  Prov (atomic (eqn (ap2 TreeEq (reify t) (reify t)) O))
provTreeEqSelfReify lf       = provAxTreeEqLL
provTreeEqSelfReify (nd a b) =
  let ra : Term ; ra = reify a
      rb : Term ; rb = reify b
      teAA : Term ; teAA = ap2 TreeEq ra ra
      teBB : Term ; teBB = ap2 TreeEq rb rb
      poo  : Term ; poo  = ap2 Pair O O
      rest : Term ; rest = ap2 Pair teBB poo
      ihA : Prov (atomic (eqn teAA O))
      ihA = provTreeEqSelfReify a
      ihB : Prov (atomic (eqn teBB O))
      ihB = provTreeEqSelfReify b
      step1 : Prov (atomic (eqn (ap2 TreeEq (ap2 Pair ra rb) (ap2 Pair ra rb))
                                (ap2 IfLf teAA rest)))
      step1 = provAxTreeEqNN ra rb ra rb
      step2 : Prov (atomic (eqn (ap2 IfLf teAA rest) (ap2 IfLf O rest)))
      step2 = provCongL IfLf rest {teAA} {O} ihA
      step3 : Prov (atomic (eqn (ap2 IfLf O rest) teBB))
      step3 = provAxIfLfL teBB poo
  in provTrans (ap2 TreeEq (ap2 Pair ra rb) (ap2 Pair ra rb))
               (ap2 IfLf teAA rest) O
               step1
               (provTrans (ap2 IfLf teAA rest) (ap2 IfLf O rest) O
                  step2
                  (provTrans (ap2 IfLf O rest) teBB O step3 ihB))
