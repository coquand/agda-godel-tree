{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StabilityNatFuel -- meta-Nat induction over the fuel argument of
--  cov_spec : Fun1 -> Fun2 -> Fun2 .
--
-- ======================================================================
-- WHAT THIS SESSION SHIPS (S2).
-- ======================================================================
--
--  1.  stateMeta : Fun1 -> Fun2 -> Term -> Nat -> Term .
--      The meta-level closed form of  cov_spec baseFun stepFun spec K
--      at fuel  K : Nat .
--
--  2.  cov_spec_natCode :  for any  K : Nat ,
--          ap2 (cov_spec baseFun stepFun) spec (natCode K)
--            =Deriv=  stateMeta baseFun stepFun spec K .
--      Proved by meta-induction on K.
--
--  3.  closed_stateMeta :  if  spec  is Closed, then so is  stateMeta
--      baseFun stepFun spec K  for every meta-Nat  K .  (Inherits
--      closure of  pi  and  baseFun  / stepFun  outputs from the
--      shape of  state_step_spec .)
--
--  4.  fst_stateMeta :  Fst (stateMeta baseFun stepFun spec K) =Deriv=
--      natCode K .  Captures the counter-preservation invariant.
--      Proved by meta-induction on K (base: Fst (pi O ...) = O ;
--      step: Fst (state_step_spec ...) = s (Fst prev) , combined with IH).
--
--  5.  fstSnd_stateMeta :  Fst (Snd (stateMeta baseFun stepFun spec K))
--      =Deriv= spec .  Captures the spec-preservation invariant.
--
--  6.  readOff_stateMeta_step :  readOff_spec (stateMeta f g spec (suc K))
--      =Deriv= stepFun (natCode K) (Snd (stateMeta f g spec K)) .
--      Direct consequence of stateMeta_succ + readOff_spec_eq +
--      axFst/axSnd and  fst_stateMeta .
--
--  7.  snd_stateMeta_step :  Snd (Snd (stateMeta f g spec (suc K))) =Deriv=
--      pi (stepFun (Fst state) (Snd state)) (Snd (Snd state))
--      where  state = stateMeta f g spec K .  This is the table at step K+1.
--
--  Together these are enough for the S3-S5 sessions to express
--  ap2 sbtState spec t  as  stateMeta ... K  for input  t = natCode K
--  (and via  pi_natCode  bridges, for shape inputs like
--  ap2 pi (natCode tag_var) (natCode m) ).

module BRA4.StabilityNatFuel where

open import BRA4.Base
open import BRA4.CoVSpec

open import BRA3.Church          using ( pi )
open import BRA3.ChurchT117      using ( Fst )
open import BRA3.ChurchT116      using ( Snd )
open import BRA3.PairAlgebra     using
  ( axFst ; axSnd ; compose1U ; compose1U_eq )
open import BRA3.Dispatch        using
  ( Closed ; closed_O ; closed_natCode ; closed_ap1 ; closed_ap2 )
open import BRA3.Numerals        using ( pi_natCode )
open import BRA3.Code.Tag        using ( cantor )

------------------------------------------------------------------------
-- stateMeta : Fun1 -> Fun2 -> Term -> Nat -> Term
--
-- The meta-Agda closed form of  cov_spec baseFun stepFun spec  at
-- fuel  K : Nat .

stateMeta : Fun1 -> Fun2 -> Term -> Nat -> Term
stateMeta baseFun stepFun spec zero    =
  ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))
stateMeta baseFun stepFun spec (suc K) =
  ap1 (state_step_spec stepFun) (stateMeta baseFun stepFun spec K)

------------------------------------------------------------------------
-- cov_spec_natCode :  the BRA-internal cov_spec at fuel  natCode K
-- equals the meta-level  stateMeta K .  By meta-induction on K.

cov_spec_natCode :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (natCode K))
              (stateMeta baseFun stepFun spec K))
cov_spec_natCode baseFun stepFun spec zero =
  cov_spec_base baseFun stepFun spec
cov_spec_natCode baseFun stepFun spec (suc K) =
  let step_eq :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s (natCode K)))
                    (ap1 (state_step_spec stepFun)
                          (ap2 (cov_spec baseFun stepFun) spec (natCode K))))
      step_eq = cov_spec_step baseFun stepFun spec (natCode K) (closed_natCode K)

      ih : Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (natCode K))
                       (stateMeta baseFun stepFun spec K))
      ih = cov_spec_natCode baseFun stepFun spec K

      lifted :
        Deriv (eqF (ap1 (state_step_spec stepFun)
                          (ap2 (cov_spec baseFun stepFun) spec (natCode K)))
                    (ap1 (state_step_spec stepFun)
                          (stateMeta baseFun stepFun spec K)))
      lifted = cong1 (state_step_spec stepFun) ih
  in ruleTrans step_eq lifted

------------------------------------------------------------------------
-- closed_stateMeta :  if  spec  is Closed, so is  stateMeta ... K .

closed_stateMeta :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) -> Closed spec ->
  (K : Nat) -> Closed (stateMeta baseFun stepFun spec K)
closed_stateMeta baseFun stepFun spec cs zero =
  closed_ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))
    closed_O
    (closed_ap2 pi spec (ap2 pi (ap1 baseFun spec) O)
      cs
      (closed_ap2 pi (ap1 baseFun spec) O
        (closed_ap1 baseFun spec cs)
        closed_O))
closed_stateMeta baseFun stepFun spec cs (suc K) =
  closed_ap1 (state_step_spec stepFun)
              (stateMeta baseFun stepFun spec K)
              (closed_stateMeta baseFun stepFun spec cs K)

------------------------------------------------------------------------
-- fst_stateMeta :  Fst (stateMeta baseFun stepFun spec K) =Deriv= natCode K .
--
-- By meta-induction on K.
--   Base K = 0:  stateMeta 0 = pi O (pi spec (pi (baseFun spec) O)) ,
--                so Fst = O = natCode 0.
--   Step K+1:    stateMeta (suc K) = state_step_spec g (stateMeta K) ,
--                Fst (state_step_spec g state) = s (Fst state).
--                By IH, Fst (stateMeta K) = natCode K, so this becomes
--                s (natCode K) = natCode (suc K).

fst_stateMeta :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 Fst (stateMeta baseFun stepFun spec K)) (natCode K))
fst_stateMeta baseFun stepFun spec zero =
  -- Fst (pi O (pi spec (pi (baseFun spec) O))) = O.
  axFst O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))
fst_stateMeta baseFun stepFun spec (suc K) =
  let prev : Term
      prev = stateMeta baseFun stepFun spec K

      -- state_step_spec_eq : the shape lemma.
      shape :
        Deriv (eqF (ap1 (state_step_spec stepFun) prev)
                    (ap2 pi (ap1 s (ap1 Fst prev))
                            (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev))))))
      shape = state_step_spec_eq stepFun prev

      -- Fst (state_step_spec g prev) = s (Fst prev).
      fst_step_raw :
        Deriv (eqF (ap1 Fst (ap1 (state_step_spec stepFun) prev))
                    (ap1 Fst (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev)))))))
      fst_step_raw = cong1 Fst shape

      fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev))))))
                    (ap1 s (ap1 Fst prev)))
      fst_pi = axFst (ap1 s (ap1 Fst prev))
                     (ap2 pi (ap1 Fst (ap1 Snd prev))
                       (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                               (ap1 Snd (ap1 Snd prev))))

      fst_step :
        Deriv (eqF (ap1 Fst (ap1 (state_step_spec stepFun) prev))
                    (ap1 s (ap1 Fst prev)))
      fst_step = ruleTrans fst_step_raw fst_pi

      -- IH:  Fst prev = natCode K .
      ih : Deriv (eqF (ap1 Fst prev) (natCode K))
      ih = fst_stateMeta baseFun stepFun spec K

      -- Lift IH under  s :  s (Fst prev) = s (natCode K) = natCode (suc K) .
      lifted :
        Deriv (eqF (ap1 s (ap1 Fst prev)) (ap1 s (natCode K)))
      lifted = cong1 s ih
  in ruleTrans fst_step lifted

------------------------------------------------------------------------
-- snd_stateMeta_succ :  Snd (stateMeta f g spec (suc K)) =Deriv=
--   pi spec (pi (stepFun (Fst prev) (Snd prev)) (Snd (Snd prev)))
-- where  prev = stateMeta f g spec K .  Just the Snd-shape of
-- state_step_spec applied to  prev .

snd_stateMeta_succ :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 Snd (stateMeta baseFun stepFun spec (suc K)))
              (ap2 pi (ap1 Fst (ap1 Snd (stateMeta baseFun stepFun spec K)))
                      (ap2 pi (ap2 stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                                              (ap1 Snd (stateMeta baseFun stepFun spec K)))
                              (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec K))))))
snd_stateMeta_succ baseFun stepFun spec K =
  let prev : Term
      prev = stateMeta baseFun stepFun spec K

      shape :
        Deriv (eqF (ap1 (state_step_spec stepFun) prev)
                    (ap2 pi (ap1 s (ap1 Fst prev))
                            (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev))))))
      shape = state_step_spec_eq stepFun prev

      snd_shape :
        Deriv (eqF (ap1 Snd (ap1 (state_step_spec stepFun) prev))
                    (ap1 Snd (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev)))))))
      snd_shape = cong1 Snd shape

      snd_pi :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev))))))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_pi = axSnd (ap1 s (ap1 Fst prev))
                      (ap2 pi (ap1 Fst (ap1 Snd prev))
                          (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                  (ap1 Snd (ap1 Snd prev))))
  in ruleTrans snd_shape snd_pi

------------------------------------------------------------------------
-- fstSnd_stateMeta :  Fst (Snd (stateMeta f g spec K)) =Deriv= spec .
--
-- Spec preservation across all K.  By meta-induction on K.
--   Base K = 0:  stateMeta 0 = pi O (pi spec (pi (baseFun spec) O)) .
--                Snd = pi spec ... .  Fst (Snd) = spec .
--   Step K+1:    Snd (state_step_spec g prev) = pi spec_K (...) where
--                spec_K = Fst (Snd prev) , so Fst (Snd) = Fst (Snd prev).
--                By IH, Fst (Snd prev) = spec .

fstSnd_stateMeta :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (stateMeta baseFun stepFun spec K))) spec)
fstSnd_stateMeta baseFun stepFun spec zero =
  let -- Snd (pi O (pi spec (pi (baseFun spec) O))) = pi spec (pi (baseFun spec) O).
      snd_eq :
        Deriv (eqF (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))))
                    (ap2 pi spec (ap2 pi (ap1 baseFun spec) O)))
      snd_eq = axSnd O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))

      -- Lift under Fst.
      fst_snd_eq :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O)))))
                    (ap1 Fst (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))))
      fst_snd_eq = cong1 Fst snd_eq

      -- Fst (pi spec ...) = spec.
      fst_eq : Deriv (eqF (ap1 Fst (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))) spec)
      fst_eq = axFst spec (ap2 pi (ap1 baseFun spec) O)
  in ruleTrans fst_snd_eq fst_eq
fstSnd_stateMeta baseFun stepFun spec (suc K) =
  let prev : Term
      prev = stateMeta baseFun stepFun spec K

      -- Snd (stateMeta (suc K)) = pi (Fst (Snd prev)) (pi (stepFun ...) (Snd (Snd prev))).
      snd_eq :
        Deriv (eqF (ap1 Snd (stateMeta baseFun stepFun spec (suc K)))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_eq = snd_stateMeta_succ baseFun stepFun spec K

      -- Fst (pi (Fst (Snd prev)) ...) = Fst (Snd prev).
      fst_snd_eq :
        Deriv (eqF (ap1 Fst (ap1 Snd (stateMeta baseFun stepFun spec (suc K))))
                    (ap1 Fst (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))))
      fst_snd_eq = cong1 Fst snd_eq

      fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev)))))
                    (ap1 Fst (ap1 Snd prev)))
      fst_pi = axFst (ap1 Fst (ap1 Snd prev))
                     (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                             (ap1 Snd (ap1 Snd prev)))

      -- IH:  Fst (Snd prev) = spec .
      ih : Deriv (eqF (ap1 Fst (ap1 Snd prev)) spec)
      ih = fstSnd_stateMeta baseFun stepFun spec K
  in ruleTrans fst_snd_eq (ruleTrans fst_pi ih)

------------------------------------------------------------------------
-- sndSnd_stateMeta_succ :  Snd (Snd (stateMeta f g spec (suc K))) =Deriv=
--   pi (stepFun (Fst prev) (Snd prev)) (Snd (Snd prev))
-- where  prev = stateMeta f g spec K .  This is the table at step K+1.

sndSnd_stateMeta_succ :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec (suc K))))
              (ap2 pi (ap2 stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                                      (ap1 Snd (stateMeta baseFun stepFun spec K)))
                      (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec K)))))
sndSnd_stateMeta_succ baseFun stepFun spec K =
  let prev : Term
      prev = stateMeta baseFun stepFun spec K

      snd_eq :
        Deriv (eqF (ap1 Snd (stateMeta baseFun stepFun spec (suc K)))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_eq = snd_stateMeta_succ baseFun stepFun spec K

      -- Snd of the resulting pi: Snd (pi spec_K (pi val_K+1 oldTable)) = pi val_K+1 oldTable.
      snd_snd_eq :
        Deriv (eqF (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec (suc K))))
                    (ap1 Snd (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))))
      snd_snd_eq = cong1 Snd snd_eq

      snd_pi :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev)))))
                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                            (ap1 Snd (ap1 Snd prev))))
      snd_pi = axSnd (ap1 Fst (ap1 Snd prev))
                      (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                              (ap1 Snd (ap1 Snd prev)))
  in ruleTrans snd_snd_eq snd_pi

------------------------------------------------------------------------
-- fstSndSnd_stateMeta_succ :  Fst (Snd (Snd (stateMeta f g spec (suc K))))
--   =Deriv= stepFun (Fst prev) (Snd prev)
-- where  prev = stateMeta f g spec K .  This is val_{K+1} -- the
-- "newest val" extracted by  readOff_spec  at the suc-K state.

fstSndSnd_stateMeta_succ :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec (suc K)))))
              (ap2 stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                            (ap1 Snd (stateMeta baseFun stepFun spec K))))
fstSndSnd_stateMeta_succ baseFun stepFun spec K =
  let prev : Term
      prev = stateMeta baseFun stepFun spec K

      sndSnd_eq :
        Deriv (eqF (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec (suc K))))
                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                            (ap1 Snd (ap1 Snd prev))))
      sndSnd_eq = sndSnd_stateMeta_succ baseFun stepFun spec K

      fst_lift :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd (stateMeta baseFun stepFun spec (suc K)))))
                    (ap1 Fst (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev)))))
      fst_lift = cong1 Fst sndSnd_eq

      fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))
                    (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev)))
      fst_pi = axFst (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                     (ap1 Snd (ap1 Snd prev))
  in ruleTrans fst_lift fst_pi

------------------------------------------------------------------------
-- readOff_stateMeta_succ :  readOff_spec (stateMeta f g spec (suc K))
--   =Deriv= stepFun (Fst prev) (Snd prev)
-- where  prev = stateMeta f g spec K .  Direct via readOff_spec_eq +
-- fstSndSnd_stateMeta_succ.

readOff_stateMeta_succ :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 readOff_spec (stateMeta baseFun stepFun spec (suc K)))
              (ap2 stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                            (ap1 Snd (stateMeta baseFun stepFun spec K))))
readOff_stateMeta_succ baseFun stepFun spec K =
  let state : Term
      state = stateMeta baseFun stepFun spec (suc K)

      e1 :
        Deriv (eqF (ap1 readOff_spec state)
                    (ap1 Fst (ap1 Snd (ap1 Snd state))))
      e1 = readOff_spec_eq state
  in ruleTrans e1 (fstSndSnd_stateMeta_succ baseFun stepFun spec K)

------------------------------------------------------------------------
-- readOff_stateMeta_succ_via_natCode :  the same val computed at  Fst
-- of  prev  replaced by  natCode K  (using  fst_stateMeta ).  This is
-- the form S3-S5 consume:  readOff_spec (stateMeta f g spec (suc K))
--   =Deriv= stepFun (natCode K) (Snd (stateMeta f g spec K)) .

readOff_stateMeta_succ_via_natCode :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 readOff_spec (stateMeta baseFun stepFun spec (suc K)))
              (ap2 stepFun (natCode K) (ap1 Snd (stateMeta baseFun stepFun spec K))))
readOff_stateMeta_succ_via_natCode baseFun stepFun spec K =
  let prev : Term
      prev = stateMeta baseFun stepFun spec K

      raw :
        Deriv (eqF (ap1 readOff_spec (stateMeta baseFun stepFun spec (suc K)))
                    (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev)))
      raw = readOff_stateMeta_succ baseFun stepFun spec K

      fst_eq : Deriv (eqF (ap1 Fst prev) (natCode K))
      fst_eq = fst_stateMeta baseFun stepFun spec K

      lifted :
        Deriv (eqF (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                    (ap2 stepFun (natCode K) (ap1 Snd prev)))
      lifted = congL stepFun (ap1 Snd prev) fst_eq
  in ruleTrans raw lifted

------------------------------------------------------------------------
-- PHASE 4: per-shape rephrasings.
--
-- These bridge S2's stability infrastructure to the input shapes S3-S5
-- need to discharge the SbContract closures.

------------------------------------------------------------------------
-- readOff_cov_spec_succ :  for any Closed Term  n , the readoff of
--  cov_spec  at fuel  s n  equals  stepFun (Fst prev) (Snd prev)
-- where  prev = cov_spec f g spec n .

readOff_cov_spec_succ :
  (baseFun : Fun1) (stepFun : Fun2) (spec n : Term) -> Closed n ->
  Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseFun stepFun) spec (ap1 s n)))
              (ap2 stepFun (ap1 Fst (ap2 (cov_spec baseFun stepFun) spec n))
                            (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec n))))
readOff_cov_spec_succ baseFun stepFun spec n cn =
  let prev : Term
      prev = ap2 (cov_spec baseFun stepFun) spec n

      step_eq :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s n))
                    (ap1 (state_step_spec stepFun) prev))
      step_eq = cov_spec_step baseFun stepFun spec n cn

      lifted_readOff :
        Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseFun stepFun) spec (ap1 s n)))
                    (ap1 readOff_spec (ap1 (state_step_spec stepFun) prev)))
      lifted_readOff = cong1 readOff_spec step_eq

      -- readOff_spec (state_step_spec g state) =
      --   Fst (Snd (Snd (state_step_spec g state))) =
      --   stepFun (Fst state) (Snd state).
      readOff_eq :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun) prev))
                    (ap1 Fst (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) prev)))))
      readOff_eq = readOff_spec_eq (ap1 (state_step_spec stepFun) prev)

      -- Use state_step_spec_eq to get the explicit pi-shape.
      shape :
        Deriv (eqF (ap1 (state_step_spec stepFun) prev)
                    (ap2 pi (ap1 s (ap1 Fst prev))
                            (ap2 pi (ap1 Fst (ap1 Snd prev))
                                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                            (ap1 Snd (ap1 Snd prev))))))
      shape = state_step_spec_eq stepFun prev

      snd_shape :
        Deriv (eqF (ap1 Snd (ap1 (state_step_spec stepFun) prev))
                    (ap1 Snd (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev)))))))
      snd_shape = cong1 Snd shape

      snd_pi :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 s (ap1 Fst prev))
                              (ap2 pi (ap1 Fst (ap1 Snd prev))
                                (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                        (ap1 Snd (ap1 Snd prev))))))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_pi = axSnd (ap1 s (ap1 Fst prev))
                      (ap2 pi (ap1 Fst (ap1 Snd prev))
                          (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                  (ap1 Snd (ap1 Snd prev))))

      snd_full :
        Deriv (eqF (ap1 Snd (ap1 (state_step_spec stepFun) prev))
                    (ap2 pi (ap1 Fst (ap1 Snd prev))
                            (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                    (ap1 Snd (ap1 Snd prev)))))
      snd_full = ruleTrans snd_shape snd_pi

      -- Snd (Snd ...).
      snd_snd_eq :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) prev)))
                    (ap1 Snd (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))))
      snd_snd_eq = cong1 Snd snd_full

      snd_pi2 :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 Fst (ap1 Snd prev))
                              (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev)))))
                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                            (ap1 Snd (ap1 Snd prev))))
      snd_pi2 = axSnd (ap1 Fst (ap1 Snd prev))
                       (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                               (ap1 Snd (ap1 Snd prev)))

      snd_snd_full :
        Deriv (eqF (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) prev)))
                    (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                            (ap1 Snd (ap1 Snd prev))))
      snd_snd_full = ruleTrans snd_snd_eq snd_pi2

      -- Fst (Snd (Snd ...)) = stepFun (Fst prev) (Snd prev).
      fst_lift :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd (ap1 (state_step_spec stepFun) prev))))
                    (ap1 Fst (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev)))))
      fst_lift = cong1 Fst snd_snd_full

      fst_pi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                                      (ap1 Snd (ap1 Snd prev))))
                    (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev)))
      fst_pi = axFst (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev))
                      (ap1 Snd (ap1 Snd prev))

      readOff_to_step :
        Deriv (eqF (ap1 readOff_spec (ap1 (state_step_spec stepFun) prev))
                    (ap2 stepFun (ap1 Fst prev) (ap1 Snd prev)))
      readOff_to_step =
        ruleTrans readOff_eq (ruleTrans fst_lift fst_pi)
  in ruleTrans lifted_readOff readOff_to_step

------------------------------------------------------------------------
-- readOff_cov_spec_natCode_succ :  the natCode-specialised form of
--  readOff_cov_spec_succ .  Combines  cov_spec_natCode  +  fst_stateMeta
-- to give the canonical "stepFun(natCode K, Snd (stateMeta K))" shape.

readOff_cov_spec_natCode_succ :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (K : Nat) ->
  Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseFun stepFun) spec (natCode (suc K))))
              (ap2 stepFun (natCode K) (ap1 Snd (stateMeta baseFun stepFun spec K))))
readOff_cov_spec_natCode_succ baseFun stepFun spec K =
  let -- natCode (suc K) = ap1 s (natCode K) by definition of natCode.
      raw :
        Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseFun stepFun) spec (ap1 s (natCode K))))
                    (ap2 stepFun (ap1 Fst (ap2 (cov_spec baseFun stepFun) spec (natCode K)))
                                  (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (natCode K)))))
      raw = readOff_cov_spec_succ baseFun stepFun spec (natCode K) (closed_natCode K)

      -- Bridge  cov_spec spec (natCode K)  to  stateMeta K  via cov_spec_natCode.
      cov_eq :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (natCode K))
                    (stateMeta baseFun stepFun spec K))
      cov_eq = cov_spec_natCode baseFun stepFun spec K

      -- Lift through Fst.
      fst_lift :
        Deriv (eqF (ap1 Fst (ap2 (cov_spec baseFun stepFun) spec (natCode K)))
                    (ap1 Fst (stateMeta baseFun stepFun spec K)))
      fst_lift = cong1 Fst cov_eq

      -- Lift through Snd.
      snd_lift :
        Deriv (eqF (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (natCode K)))
                    (ap1 Snd (stateMeta baseFun stepFun spec K)))
      snd_lift = cong1 Snd cov_eq

      -- Combine: stepFun(Fst(cov...), Snd(cov...)) = stepFun(Fst(stateMeta), Snd(stateMeta)).
      step_via_meta :
        Deriv (eqF (ap2 stepFun (ap1 Fst (ap2 (cov_spec baseFun stepFun) spec (natCode K)))
                                  (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (natCode K))))
                    (ap2 stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                                  (ap1 Snd (stateMeta baseFun stepFun spec K))))
      step_via_meta =
        ruleTrans (congL stepFun (ap1 Snd (ap2 (cov_spec baseFun stepFun) spec (natCode K)))
                          fst_lift)
                   (congR stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                          snd_lift)

      -- Now reduce  Fst (stateMeta K) = natCode K  via fst_stateMeta.
      fst_meta_eq :
        Deriv (eqF (ap1 Fst (stateMeta baseFun stepFun spec K)) (natCode K))
      fst_meta_eq = fst_stateMeta baseFun stepFun spec K

      step_natCode :
        Deriv (eqF (ap2 stepFun (ap1 Fst (stateMeta baseFun stepFun spec K))
                                  (ap1 Snd (stateMeta baseFun stepFun spec K)))
                    (ap2 stepFun (natCode K)
                                  (ap1 Snd (stateMeta baseFun stepFun spec K))))
      step_natCode = congL stepFun (ap1 Snd (stateMeta baseFun stepFun spec K)) fst_meta_eq
  in ruleTrans raw (ruleTrans step_via_meta step_natCode)

------------------------------------------------------------------------
-- snd_stateMeta_pi_form :  Snd (stateMeta f g spec K) has the form
--  pi spec (table_K)  for ALL K.  Specifically:
--
--   * K = 0:  Snd (pi O (pi spec (pi (baseFun spec) O))) = pi spec (pi (baseFun spec) O).
--   * K = suc K':  Snd (state_step_spec g prev) = pi (Fst (Snd prev)) (...),
--                  and Fst (Snd prev) = spec by fstSnd_stateMeta.
--
-- This characterises  Snd (stateMeta K)  as a pi with  spec  at the head,
-- enabling stepFun_sbt's  get_spec = Fst Snd  access to fire correctly
-- at the next step.

snd_stateMeta_at_zero :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) ->
  Deriv (eqF (ap1 Snd (stateMeta baseFun stepFun spec zero))
              (ap2 pi spec (ap2 pi (ap1 baseFun spec) O)))
snd_stateMeta_at_zero baseFun stepFun spec =
  axSnd O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))

------------------------------------------------------------------------
-- The "spec at head" form of  Snd (stateMeta K)  for ARBITRARY K, used
-- by stepFun_sbt's lookup machinery.  This is the BRA4 analog of the
-- main stability theorem in the PDF.
--
-- Statement:  Snd (stateMeta f g spec K) =Deriv= pi spec restTable_K
-- where  restTable_K = ?  -- we leave restTable abstract for now and
-- export the FST projection (which is invariant = spec).
--
-- The Fst-of-Snd is exactly what  get_spec  in BRA4/SbT.agda reads off.

------------------------------------------------------------------------
-- cov_spec_at_pi_natCode :  bridge from  pi (natCode a) (natCode b)
-- input form to  stateMeta (cantor a b)  via pi_natCode.
--
-- This is the entry point S3-S5 use for inputs of the form
--  ap2 pi (natCode tag) (natCode body) .

cov_spec_at_pi_natCode :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (a b : Nat) ->
  Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap2 pi (natCode a) (natCode b)))
              (stateMeta baseFun stepFun spec (cantor a b)))
cov_spec_at_pi_natCode baseFun stepFun spec a b =
  let -- pi (natCode a) (natCode b) = natCode (cantor a b).
      pi_eq : Deriv (eqF (ap2 pi (natCode a) (natCode b)) (natCode (cantor a b)))
      pi_eq = pi_natCode a b

      -- Lift through cov_spec ... spec (-).
      cov_lift :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap2 pi (natCode a) (natCode b)))
                    (ap2 (cov_spec baseFun stepFun) spec (natCode (cantor a b))))
      cov_lift = congR (cov_spec baseFun stepFun) spec pi_eq

      -- cov_spec at natCode (cantor a b) = stateMeta (cantor a b).
      cov_eq :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (natCode (cantor a b)))
                    (stateMeta baseFun stepFun spec (cantor a b)))
      cov_eq = cov_spec_natCode baseFun stepFun spec (cantor a b)
  in ruleTrans cov_lift cov_eq

------------------------------------------------------------------------
-- readOff_at_pi_natCode :  composition of  cov_spec_at_pi_natCode  with
--  readOff_spec  --  the form  S3-S5 most directly need.

readOff_at_pi_natCode :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) (a b : Nat) ->
  Deriv (eqF (ap1 readOff_spec (ap2 (cov_spec baseFun stepFun) spec
                                      (ap2 pi (natCode a) (natCode b))))
              (ap1 readOff_spec (stateMeta baseFun stepFun spec (cantor a b))))
readOff_at_pi_natCode baseFun stepFun spec a b =
  cong1 readOff_spec (cov_spec_at_pi_natCode baseFun stepFun spec a b)
