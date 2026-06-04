{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CoverBridgeAlph -- re-types  T4.CoverBridge.coverBridge  at the
-- K-formula  T4.KdefAlph.KdefAlph , verifying ( by  refl ) that the open
-- Pi_1 consequent  coverBridge  produces IS exactly the  checkAlphN -guarded
-- K-formula whose Chaitin diagonal is built in  T4.CgFalseImpAlph .   This
-- is the front-end -> Chaitin-core junction of the surprise-GII assembly.

open import T4.Base

module T4.CoverBridgeAlph (Lstar_meta : Nat) where

open import T4.KdefAlph Lstar_meta using ( KdefAlph )
open import T4.CoverBridge Lstar_meta using ( coverBridge )
open import T4.KdefBigConjFuelBridge using ( KdefBigConjF )
open import T4.EnumProg Lstar_meta using ( enum ; Bnat )

-- coverBridge :  ⋀_{k<=M} ¬def_{enum k}(r)  =>  KdefAlph(natCode r) ,
-- the open  Pi_1  K-formula over the free program  var 0 .
coverBridgeKdefAlph :
  (M r : Nat) (bnatEq : Eq Bnat (suc M)) ->
  Deriv (imp (KdefBigConjF enum (var (suc zero)) M (natCode r))
             (KdefAlph (natCode r)))
coverBridgeKdefAlph M r bnatEq = coverBridge M r bnatEq
