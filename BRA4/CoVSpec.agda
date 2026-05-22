{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CoVSpec -- spec-carrying course-of-values recursion.
--
-- ======================================================================
-- DESIGN.
-- ======================================================================
--
-- Build  cov_spec : Fun1 -> Fun2 -> Fun2  such that, applied to (spec, K):
--
--   ap2 (cov_spec baseFun stepFun) spec K  =Deriv=  state_K
--
-- where the state at step K is:
--
--   state_K = ap2 pi (natCode K) (ap2 pi spec table_K)
--
-- and  table_K  is the cons-list  [val_K, val_{K-1}, ..., val_0]  encoded
-- as  ap2 pi val_K (ap2 pi val_{K-1} ... (ap2 pi val_0 O)) .
--
-- Compared with  BRA3.CourseOfValuesRec.courseOfValues  (which has state
-- shape  pi (natCode K) table_K ), the spec-carrying version inserts
-- one extra layer  pi spec ...  inside  Snd state .  This is how the
-- step function gets access to  spec  without it being an explicit BRA
-- argument:  spec  is recoverable as  Fst (Snd state)  at every step.
--
-- The values are computed by:
--   val_0     =  ap1 baseFun spec
--   val_{K+1} =  ap2 stepFun (Fst state_K) (Snd state_K)
--   stepFun receives the prior counter  natCode K  and the prior  pi spec table_K
--   bundle.  Inside stepFun, spec and table_K are accessible via Fst / Snd .
--
-- The PDF  treerec.pdf  (Tree Recursion with Binary Trees) confirms this
-- pattern is "the actual primitive-recursive object" underlying tree
-- recursion, with  H = lookup compose courseOfValues .
--
-- ======================================================================
-- INTERFACE.
-- ======================================================================
--
-- Three closures are shipped:
--
--   cov_spec_base :  cov_spec baseFun stepFun spec O  =Deriv=
--                     pi O (pi spec (pi (baseFun spec) O))
--
--   cov_spec_step :  Closed n ->
--                     cov_spec baseFun stepFun spec (s n)  =Deriv=
--                     state_step_spec stepFun (cov_spec baseFun stepFun spec n)
--
--   state_step_spec_shape :  Universal shape lemma --
--     state_step_spec stepFun state  =Deriv=
--     pi (s (Fst state)) (pi (Fst (Snd state))
--                          (pi (stepFun (Fst state) (Snd state)) (Snd (Snd state)))) .
--
-- Plus per-projection preservation lemmas downstream sessions consume.

module BRA4.CoVSpec where

open import BRA4.Base
open import BRA3.Church       using ( pi )
open import BRA3.ChurchT116   using ( Snd )
open import BRA3.ChurchT117   using ( Fst )
open import BRA3.PairAlgebra  using
  ( axFst ; axSnd ; compose1U ; compose1U_eq )
open import BRA3.CourseOfValues using
  ( iter_step_fun ; iter_step_fun_eq )

------------------------------------------------------------------------
-- The initial-state Fun1.
--
-- initialState_spec baseFun spec
--   = pi O (pi spec (pi (baseFun spec) O))

initialState_spec : Fun1 -> Fun1
initialState_spec baseFun = C pi o (C pi u (C pi baseFun o))

initialState_spec_eq :
  (baseFun : Fun1) (spec : Term) ->
  Deriv (eqF (ap1 (initialState_spec baseFun) spec)
              (ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))))
initialState_spec_eq baseFun spec =
  let -- (C pi o (C pi u (C pi baseFun o))) spec
      --   = pi (o spec) ((C pi u (C pi baseFun o)) spec).
      step1 :
        Deriv (eqF (ap1 (initialState_spec baseFun) spec)
                    (ap2 pi (ap1 o spec)
                            (ap1 (C pi u (C pi baseFun o)) spec)))
      step1 = ax_C pi o (C pi u (C pi baseFun o)) spec

      o_eq : Deriv (eqF (ap1 o spec) O)
      o_eq = ax_o spec

      step2 :
        Deriv (eqF (ap2 pi (ap1 o spec)
                            (ap1 (C pi u (C pi baseFun o)) spec))
                    (ap2 pi O
                            (ap1 (C pi u (C pi baseFun o)) spec)))
      step2 = congL pi (ap1 (C pi u (C pi baseFun o)) spec) o_eq

      -- (C pi u (C pi baseFun o)) spec
      --   = pi (u spec) ((C pi baseFun o) spec)
      --   = pi spec     ((C pi baseFun o) spec).
      inner1 :
        Deriv (eqF (ap1 (C pi u (C pi baseFun o)) spec)
                    (ap2 pi (ap1 u spec)
                            (ap1 (C pi baseFun o) spec)))
      inner1 = ax_C pi u (C pi baseFun o) spec

      u_eq : Deriv (eqF (ap1 u spec) spec)
      u_eq = ax_u spec

      inner2 :
        Deriv (eqF (ap2 pi (ap1 u spec)
                            (ap1 (C pi baseFun o) spec))
                    (ap2 pi spec
                            (ap1 (C pi baseFun o) spec)))
      inner2 = congL pi (ap1 (C pi baseFun o) spec) u_eq

      -- (C pi baseFun o) spec = pi (baseFun spec) (o spec) = pi (baseFun spec) O.
      bf1 :
        Deriv (eqF (ap1 (C pi baseFun o) spec)
                    (ap2 pi (ap1 baseFun spec) (ap1 o spec)))
      bf1 = ax_C pi baseFun o spec

      bf2 :
        Deriv (eqF (ap2 pi (ap1 baseFun spec) (ap1 o spec))
                    (ap2 pi (ap1 baseFun spec) O))
      bf2 = congR pi (ap1 baseFun spec) o_eq

      bf_full :
        Deriv (eqF (ap1 (C pi baseFun o) spec)
                    (ap2 pi (ap1 baseFun spec) O))
      bf_full = ruleTrans bf1 bf2

      inner3 :
        Deriv (eqF (ap2 pi spec (ap1 (C pi baseFun o) spec))
                    (ap2 pi spec (ap2 pi (ap1 baseFun spec) O)))
      inner3 = congR pi spec bf_full

      inner_full :
        Deriv (eqF (ap1 (C pi u (C pi baseFun o)) spec)
                    (ap2 pi spec (ap2 pi (ap1 baseFun spec) O)))
      inner_full = ruleTrans inner1 (ruleTrans inner2 inner3)

      step3 :
        Deriv (eqF (ap2 pi O (ap1 (C pi u (C pi baseFun o)) spec))
                    (ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))))
      step3 = congR pi O inner_full
  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- The state-step Fun1.
--
-- state_step_spec stepFun state
--   = pi (s (Fst state))
--        (pi (Fst (Snd state))
--             (pi (stepFun (Fst state) (Snd state)) (Snd (Snd state))))
--
-- I.e., increment counter, preserve spec (= Fst (Snd state)), prepend new
-- val (= stepFun(Fst state, Snd state)) to old table (= Snd (Snd state)).

state_step_spec : Fun2 -> Fun1
state_step_spec stepFun =
  C pi (compose1U s Fst)                                          -- s K
       (C pi (compose1U Fst Snd)                                  -- spec
             (C pi (C stepFun Fst Snd)                            -- new val
                   (compose1U Snd Snd)))                          -- old table

state_step_spec_eq :
  (stepFun : Fun2) (state : Term) ->
  Deriv (eqF (ap1 (state_step_spec stepFun) state)
              (ap2 pi (ap1 s (ap1 Fst state))
                      (ap2 pi (ap1 Fst (ap1 Snd state))
                              (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                      (ap1 Snd (ap1 Snd state))))))
state_step_spec_eq stepFun state =
  let -- Outer C pi (compose1U s Fst) ... applied:
      e_outer :
        Deriv (eqF (ap1 (state_step_spec stepFun) state)
                    (ap2 pi (ap1 (compose1U s Fst) state)
                            (ap1 (C pi (compose1U Fst Snd)
                                   (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                                  state)))
      e_outer = ax_C pi (compose1U s Fst)
                       (C pi (compose1U Fst Snd)
                          (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                       state

      -- compose1U s Fst state = s (Fst state).
      e_sFst :
        Deriv (eqF (ap1 (compose1U s Fst) state) (ap1 s (ap1 Fst state)))
      e_sFst = compose1U_eq s Fst state

      e_outer_L :
        Deriv (eqF (ap2 pi (ap1 (compose1U s Fst) state)
                            (ap1 (C pi (compose1U Fst Snd)
                                   (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                                  state))
                    (ap2 pi (ap1 s (ap1 Fst state))
                            (ap1 (C pi (compose1U Fst Snd)
                                   (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                                  state)))
      e_outer_L = congL pi
                    (ap1 (C pi (compose1U Fst Snd)
                            (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                          state)
                    e_sFst

      -- Middle: (C pi (compose1U Fst Snd) (C pi (C stepFun Fst Snd) (compose1U Snd Snd))) state.
      e_mid :
        Deriv (eqF (ap1 (C pi (compose1U Fst Snd)
                          (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                         state)
                    (ap2 pi (ap1 (compose1U Fst Snd) state)
                            (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd))
                                  state)))
      e_mid = ax_C pi (compose1U Fst Snd)
                     (C pi (C stepFun Fst Snd) (compose1U Snd Snd))
                     state

      -- compose1U Fst Snd state = Fst (Snd state).
      e_FstSnd :
        Deriv (eqF (ap1 (compose1U Fst Snd) state) (ap1 Fst (ap1 Snd state)))
      e_FstSnd = compose1U_eq Fst Snd state

      e_mid_L :
        Deriv (eqF (ap2 pi (ap1 (compose1U Fst Snd) state)
                            (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd))
                                  state))
                    (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd))
                                  state)))
      e_mid_L = congL pi
                  (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd)) state)
                  e_FstSnd

      -- Inner: (C pi (C stepFun Fst Snd) (compose1U Snd Snd)) state.
      e_inner :
        Deriv (eqF (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd)) state)
                    (ap2 pi (ap1 (C stepFun Fst Snd) state)
                            (ap1 (compose1U Snd Snd) state)))
      e_inner = ax_C pi (C stepFun Fst Snd) (compose1U Snd Snd) state

      -- (C stepFun Fst Snd) state = stepFun(Fst state, Snd state).
      e_stepFun :
        Deriv (eqF (ap1 (C stepFun Fst Snd) state)
                    (ap2 stepFun (ap1 Fst state) (ap1 Snd state)))
      e_stepFun = ax_C stepFun Fst Snd state

      -- compose1U Snd Snd state = Snd (Snd state).
      e_SndSnd :
        Deriv (eqF (ap1 (compose1U Snd Snd) state) (ap1 Snd (ap1 Snd state)))
      e_SndSnd = compose1U_eq Snd Snd state

      e_inner_L :
        Deriv (eqF (ap2 pi (ap1 (C stepFun Fst Snd) state)
                            (ap1 (compose1U Snd Snd) state))
                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                            (ap1 (compose1U Snd Snd) state)))
      e_inner_L = congL pi
                    (ap1 (compose1U Snd Snd) state)
                    e_stepFun

      e_inner_R :
        Deriv (eqF (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                            (ap1 (compose1U Snd Snd) state))
                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                            (ap1 Snd (ap1 Snd state))))
      e_inner_R = congR pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state)) e_SndSnd

      e_inner_full :
        Deriv (eqF (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd)) state)
                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                            (ap1 Snd (ap1 Snd state))))
      e_inner_full = ruleTrans e_inner (ruleTrans e_inner_L e_inner_R)

      -- Now stitch up to the middle.
      e_mid_R :
        Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap1 (C pi (C stepFun Fst Snd) (compose1U Snd Snd))
                                  state))
                    (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                    (ap1 Snd (ap1 Snd state)))))
      e_mid_R = congR pi (ap1 Fst (ap1 Snd state)) e_inner_full

      e_mid_full :
        Deriv (eqF (ap1 (C pi (compose1U Fst Snd)
                          (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                         state)
                    (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                    (ap1 Snd (ap1 Snd state)))))
      e_mid_full = ruleTrans e_mid (ruleTrans e_mid_L e_mid_R)

      -- Outer R.
      e_outer_R :
        Deriv (eqF (ap2 pi (ap1 s (ap1 Fst state))
                            (ap1 (C pi (compose1U Fst Snd)
                                   (C pi (C stepFun Fst Snd) (compose1U Snd Snd)))
                                  state))
                    (ap2 pi (ap1 s (ap1 Fst state))
                            (ap2 pi (ap1 Fst (ap1 Snd state))
                                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                            (ap1 Snd (ap1 Snd state))))))
      e_outer_R = congR pi (ap1 s (ap1 Fst state)) e_mid_full
  in ruleTrans e_outer (ruleTrans e_outer_L e_outer_R)

------------------------------------------------------------------------
-- cov_spec : Fun1 -> Fun2 -> Fun2 -- the spec-carrying course of values.

cov_spec : Fun1 -> Fun2 -> Fun2
cov_spec baseFun stepFun =
  R (initialState_spec baseFun)
    (iter_step_fun (state_step_spec stepFun))
    v

------------------------------------------------------------------------
-- cov_spec_base : at fuel = O, the state is the initial state.

cov_spec_base_raw :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) ->
  Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec O)
              (ap1 (initialState_spec baseFun) spec))
cov_spec_base_raw baseFun stepFun spec =
  ax_R_base (initialState_spec baseFun)
            (iter_step_fun (state_step_spec stepFun))
            v spec

cov_spec_base :
  (baseFun : Fun1) (stepFun : Fun2) (spec : Term) ->
  Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec O)
              (ap2 pi O (ap2 pi spec (ap2 pi (ap1 baseFun spec) O))))
cov_spec_base baseFun stepFun spec =
  ruleTrans (cov_spec_base_raw baseFun stepFun spec)
            (initialState_spec_eq baseFun spec)

------------------------------------------------------------------------
-- cov_spec_step : at fuel = suc n , state extends via state_step_spec.

cov_spec_step :
  (baseFun : Fun1) (stepFun : Fun2) (spec n : Term) -> Closed n ->
  Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s n))
              (ap1 (state_step_spec stepFun)
                    (ap2 (cov_spec baseFun stepFun) spec n)))
cov_spec_step baseFun stepFun spec n cn =
  let prev : Term
      prev = ap2 (cov_spec baseFun stepFun) spec n

      s1 :
        Deriv (eqF (ap2 (cov_spec baseFun stepFun) spec (ap1 s n))
                    (ap2 (iter_step_fun (state_step_spec stepFun))
                          (ap2 v spec n) prev))
      s1 = ax_R_step (initialState_spec baseFun)
                      (iter_step_fun (state_step_spec stepFun))
                      v spec n

      s2 :
        Deriv (eqF (ap2 (iter_step_fun (state_step_spec stepFun))
                          (ap2 v spec n) prev)
                    (ap2 (iter_step_fun (state_step_spec stepFun))
                          n prev))
      s2 = congL (iter_step_fun (state_step_spec stepFun)) prev (ax_v spec n)

      s3 :
        Deriv (eqF (ap2 (iter_step_fun (state_step_spec stepFun))
                          n prev)
                    (ap1 (state_step_spec stepFun) prev))
      s3 = iter_step_fun_eq (state_step_spec stepFun) n prev cn
  in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Convenience: the readOff Fun1 for spec-carrying states.
--
-- readOff_spec : Fun1 -- extracts val_K (the newest table value).
--   ap1 readOff_spec state = Fst (Snd (Snd state))
--
-- Closure equation: readOff_spec_eq .

readOff_spec : Fun1
readOff_spec = compose1U Fst (compose1U Snd Snd)

readOff_spec_eq :
  (state : Term) ->
  Deriv (eqF (ap1 readOff_spec state)
              (ap1 Fst (ap1 Snd (ap1 Snd state))))
readOff_spec_eq state =
  let e1 :
        Deriv (eqF (ap1 readOff_spec state)
                    (ap1 Fst (ap1 (compose1U Snd Snd) state)))
      e1 = compose1U_eq Fst (compose1U Snd Snd) state

      e2 :
        Deriv (eqF (ap1 (compose1U Snd Snd) state) (ap1 Snd (ap1 Snd state)))
      e2 = compose1U_eq Snd Snd state

      e3 :
        Deriv (eqF (ap1 Fst (ap1 (compose1U Snd Snd) state))
                    (ap1 Fst (ap1 Snd (ap1 Snd state))))
      e3 = cong1 Fst e2
  in ruleTrans e1 e3

------------------------------------------------------------------------
-- "spec-preservation" lemma: at every state produced by state_step_spec,
-- the second projection's first component is the prior spec.
--
-- This is the BRA4 analog of the PDF's Snd_state_step_preserve, adapted
-- to the spec-carrying state shape.  Stays unconditional (no Closed
-- conditions) because axFst / axSnd are universal.

state_step_spec_specPreserve :
  (stepFun : Fun2) (state : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (ap1 (state_step_spec stepFun) state)))
              (ap1 Fst (ap1 Snd state)))
state_step_spec_specPreserve stepFun state =
  let -- state_step_spec stepFun state =
      --   pi (s K) (pi spec (pi new_val table)).
      shape :
        Deriv (eqF (ap1 (state_step_spec stepFun) state)
                    (ap2 pi (ap1 s (ap1 Fst state))
                            (ap2 pi (ap1 Fst (ap1 Snd state))
                                    (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                            (ap1 Snd (ap1 Snd state))))))
      shape = state_step_spec_eq stepFun state

      -- Snd (state_step_spec stepFun state) =Deriv= ...
      sndShape :
        Deriv (eqF (ap1 Snd (ap1 (state_step_spec stepFun) state))
                    (ap1 Snd (ap2 pi (ap1 s (ap1 Fst state))
                              (ap2 pi (ap1 Fst (ap1 Snd state))
                                (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                        (ap1 Snd (ap1 Snd state)))))))
      sndShape = cong1 Snd shape

      -- Snd (pi a b) = b , so Snd of the RHS = pi spec (pi new_val table).
      sndPi :
        Deriv (eqF (ap1 Snd (ap2 pi (ap1 s (ap1 Fst state))
                              (ap2 pi (ap1 Fst (ap1 Snd state))
                                (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                        (ap1 Snd (ap1 Snd state))))))
                    (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                    (ap1 Snd (ap1 Snd state)))))
      sndPi = axSnd (ap1 s (ap1 Fst state))
                      (ap2 pi (ap1 Fst (ap1 Snd state))
                          (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                  (ap1 Snd (ap1 Snd state))))

      sndFull :
        Deriv (eqF (ap1 Snd (ap1 (state_step_spec stepFun) state))
                    (ap2 pi (ap1 Fst (ap1 Snd state))
                            (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                    (ap1 Snd (ap1 Snd state)))))
      sndFull = ruleTrans sndShape sndPi

      -- Fst (Snd (...)) =Deriv= Fst (pi spec (...)) = spec.
      fstSnd :
        Deriv (eqF (ap1 Fst (ap1 Snd (ap1 (state_step_spec stepFun) state)))
                    (ap1 Fst (ap2 pi (ap1 Fst (ap1 Snd state))
                              (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                      (ap1 Snd (ap1 Snd state))))))
      fstSnd = cong1 Fst sndFull

      fstPi :
        Deriv (eqF (ap1 Fst (ap2 pi (ap1 Fst (ap1 Snd state))
                              (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                                      (ap1 Snd (ap1 Snd state)))))
                    (ap1 Fst (ap1 Snd state)))
      fstPi = axFst (ap1 Fst (ap1 Snd state))
                      (ap2 pi (ap2 stepFun (ap1 Fst state) (ap1 Snd state))
                              (ap1 Snd (ap1 Snd state)))
  in ruleTrans fstSnd fstPi
