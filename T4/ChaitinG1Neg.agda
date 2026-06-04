{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.ChaitinG1Neg -- C.4 of the corrected (num-headed) Goedel-Chaitin G1
-- barrier: the incompressibility-search RECOGNISER, and its (trivial) bridge to
-- the  dNeg  leg of  T4.ChaitinG1Hit.chaitin_G1_hit /
-- T4.ChaitinG1Witness.chaitin_G1_barrier.
--
-- The corrected atom is the SINGLE num-headed equation  P = codeFXeqY1 compHit
-- z0 (s O) = <| compHit(num z0) = num 1 |> , and its negation (the
-- incompressibility code) is the CLOSED, decidable
--   N = cNeg P = <| not (compHit(num z0) = num 1) |> .
-- Because  N  is a closed num-headed equation-negation (NOT an open formula),
-- the recogniser's soundness bridge is just NUMERIC REFLECTION  eqInd_sound  --
-- there is NO open->closed  thmT_at_sb  step (that residual existed only for the
-- old open/codeFormula atom; the bounded-indicator atom eliminated it, see
-- CHAITIN-G1-RHO-VS-EVAL-DECISION.md).  So C.4 is:
--
--   (1) negCompCodeF compHit : Fun1 -- the num-headed code-builder
--         ap1 (negCompCodeF compHit) x = cNeg (codeFXeqY1 compHit x (s O)) ,
--       built as a fixed 5-level  C Pair  tree with the  num x  hole (the
--       codeFXeqY1 tree branches at the equation node -- the RHS  num(s O)  is a
--       constant leaf -- so this is NOT a wrapAll right-spine; it is a direct
--       C-Pair tree with two left-const nodes, one right-const node, two more);
--   (2) hitNeg compHit out : Fun1 -- the recogniser indicator
--         ap1 (hitNeg compHit out) w = eqInd (thmT w) (negCompCodeF compHit (out w)) ,
--       reading thmT(w) and matching it (numerically, codes are Nats) against
--       the incompressibility template at hole  out w ;  hitNeg_le_one is the
--       shipped  eqInd_le_one ;
--   (3) dNeg_from_hitNeg -- a firing match  hitNeg compHit out w0 = 1  yields
--         thmT w0 = cNeg (codeFXeqY1 compHit (out w0) (s O)) ,
--       i.e.  dNeg  with the subject read off as  z0 := out w0 .  This is
--       eqInd_sound  composed with  negCompCodeF_eval  -- the whole bridge.
--
-- The search itself (enum, the lastPos settling that PRODUCES a firing w0, and
-- the concrete  out  projector that reads the hole back to z0) is C.5; this
-- module is parametric in  out  and consumes the firing as a hypothesis.

module T4.ChaitinG1Neg where

open import T4.Base
open import T4.Tags            using ( tag_neg ; tag_eq ; tag_ap1 )
open import T4.ThmT            using ( thmT )
open import T4.Num             using ( num )
open import T4.Code            using ( codeFun1 )
open import T4.DefWit          using ( cNeg )
open import T4.Thm12.Thm13     using ( codeFXeqY1 )
open import T4.Thm12.ConstTermFun1
  using ( NoVar ; constTermFun1 ; constTermFun1_eq ; NoVar_natCode )
open import T4.DoubleCodeNum   using ( NoVar_codeFun1L )
open import T4.CountingObj     using ( eqIndF ; eqIndF_eq )
open import T4.Counting        using ( eqInd ; eqInd_le_one )
open import T4.Bridge          using ( eqInd_sound )

open import BRA3.Church          using ( sub )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.Logic           using ( prependEqLeft )

------------------------------------------------------------------------
-- SECTION 0.  Two Pair-node combinators (const left / const right child) and
-- their object evaluations.

-- left-const node:  ap1 (LP c inner) x = Pair c (ap1 inner x)  (for NoVar c).
LP : Term -> Fun1 -> Fun1
LP c inner = C Pair (constTermFun1 c) inner

LP_eval :
  (c : Term) (inner : Fun1) (x : Term) -> NoVar c ->
  Deriv (eqF (ap1 (LP c inner) x) (ap2 Pair c (ap1 inner x)))
LP_eval c inner x nv =
  ruleTrans (ax_C Pair (constTermFun1 c) inner x)
            (congL Pair (ap1 inner x) (constTermFun1_eq c nv x))

-- right-const node:  ap1 (RP inner c) x = Pair (ap1 inner x) c  (for NoVar c).
RP : Fun1 -> Term -> Fun1
RP inner c = C Pair inner (constTermFun1 c)

RP_eval :
  (inner : Fun1) (c : Term) (x : Term) -> NoVar c ->
  Deriv (eqF (ap1 (RP inner c) x) (ap2 Pair (ap1 inner x) c))
RP_eval inner c x nv =
  ruleTrans (ax_C Pair inner (constTermFun1 c) x)
            (congR Pair (ap1 inner x) (constTermFun1_eq c nv x))

------------------------------------------------------------------------
-- SECTION 1.  negCompCodeF -- the num-headed incompressibility code-builder.
--
--   ap1 (negCompCodeF compHit) x
--     = cNeg (codeFXeqY1 compHit x (s O))
--     = Pair tag_neg (Pair tag_eq (Pair (Pair tag_ap1 (Pair (codeFun1 compHit)
--                                                            (num x)))
--                                       (num (s O)))) .

negCompCodeF : Fun1 -> Fun1
negCompCodeF compHit =
  LP (natCode tag_neg)
   (LP (natCode tag_eq)
     (RP (LP (natCode tag_ap1)
            (LP (codeFun1 compHit) num))
         (ap1 num (ap1 s O))))

negCompCodeF_eval :
  (compHit : Fun1) (x : Term) ->
  Deriv (eqF (ap1 (negCompCodeF compHit) x)
             (cNeg (codeFXeqY1 compHit x (ap1 s O))))
negCompCodeF_eval compHit x =
  let -- E = Pair (codeFun1 compHit) (num x)
      E : Fun1
      E = LP (codeFun1 compHit) num
      eE : Deriv (eqF (ap1 E x) (ap2 Pair (codeFun1 compHit) (ap1 num x)))
      eE = LP_eval (codeFun1 compHit) num x (NoVar_codeFun1L compHit)

      -- Csub = Pair tag_ap1 (Pair (codeFun1 compHit) (num x))
      Csub : Fun1
      Csub = LP (natCode tag_ap1) E
      eC : Deriv (eqF (ap1 Csub x)
                      (ap2 Pair (natCode tag_ap1)
                         (ap2 Pair (codeFun1 compHit) (ap1 num x))))
      eC = ruleTrans (LP_eval (natCode tag_ap1) E x (NoVar_natCode tag_ap1))
                     (congR Pair (natCode tag_ap1) eE)

      -- B = Pair Csub (num (s O))
      B : Fun1
      B = RP Csub (ap1 num (ap1 s O))
      eB : Deriv (eqF (ap1 B x)
                      (ap2 Pair (ap2 Pair (natCode tag_ap1)
                                    (ap2 Pair (codeFun1 compHit) (ap1 num x)))
                                (ap1 num (ap1 s O))))
      eB = ruleTrans (RP_eval Csub (ap1 num (ap1 s O)) x tt)
                     (congL Pair (ap1 num (ap1 s O)) eC)

      -- A = Pair tag_eq B
      A : Fun1
      A = LP (natCode tag_eq) B
      eA : Deriv (eqF (ap1 A x)
                      (ap2 Pair (natCode tag_eq)
                         (ap2 Pair (ap2 Pair (natCode tag_ap1)
                                       (ap2 Pair (codeFun1 compHit) (ap1 num x)))
                                   (ap1 num (ap1 s O)))))
      eA = ruleTrans (LP_eval (natCode tag_eq) B x (NoVar_natCode tag_eq))
                     (congR Pair (natCode tag_eq) eB)
  in ruleTrans (LP_eval (natCode tag_neg) A x (NoVar_natCode tag_neg))
               (congR Pair (natCode tag_neg) eA)

------------------------------------------------------------------------
-- SECTION 2.  hitNeg -- the recogniser indicator, parametric in the hole
-- projector  out : Fun1 .
--
--   ap1 (hitNeg compHit out) w
--     = eqInd (thmT w) (ap1 (negCompCodeF compHit) (out w)) .

hitNeg : Fun1 -> Fun1 -> Fun1
hitNeg compHit out = C eqIndF thmT (compose1U (negCompCodeF compHit) out)

hitNeg_eval :
  (compHit out : Fun1) (w : Term) ->
  Deriv (eqF (ap1 (hitNeg compHit out) w)
             (eqInd (ap1 thmT w) (ap1 (negCompCodeF compHit) (ap1 out w))))
hitNeg_eval compHit out w =
  ruleTrans (ax_C eqIndF thmT (compose1U (negCompCodeF compHit) out) w)
    (ruleTrans (congR eqIndF (ap1 thmT w) (axComp (negCompCodeF compHit) out w))
               (eqIndF_eq (ap1 thmT w) (ap1 (negCompCodeF compHit) (ap1 out w))))

-- the recogniser is 0/1-valued (shipped eqInd_le_one, re-keyed via hitNeg_eval).
hitNeg_le_one :
  (compHit out : Fun1) (w : Term) ->
  Deriv (leq (ap1 (hitNeg compHit out) w) (ap1 s O))
hitNeg_le_one compHit out w =
  let c0 : Term
      c0 = ap1 (hitNeg compHit out) w
      c1 : Term
      c1 = eqInd (ap1 thmT w) (ap1 (negCompCodeF compHit) (ap1 out w))
      rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
      rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
             (congL sub (ap1 s O) (hitNeg_eval compHit out w))
  in mp rw (eqInd_le_one (ap1 thmT w) (ap1 (negCompCodeF compHit) (ap1 out w)))

------------------------------------------------------------------------
-- SECTION 3.  The bridge:  a firing match  ==>  dNeg .
--
-- A firing recogniser at  w0  (the search settles here, hitNeg = 1) yields the
-- num-headed  dNeg  with the subject read off as  z0 := ap1 out w0 :
--   thmT w0 = cNeg (codeFXeqY1 compHit (out w0) (s O)) .
-- This is exactly the  dNeg  leg consumed by  ChaitinG1Hit.chaitin_G1_hit  /
-- ChaitinG1Witness.chaitin_G1_barrier  (there z0 = out w0).  The bridge is the
-- shipped numeric reflection  eqInd_sound  (codes are Nats; a numeric match
-- reflects to code identity) composed with  negCompCodeF_eval  -- no
-- thmT_at_sb, no codeFormula, no open->closed step.

dNeg_from_hitNeg :
  (compHit out : Fun1) (w0 : Term) ->
  Deriv (eqF (ap1 (hitNeg compHit out) w0) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT w0)
             (cNeg (codeFXeqY1 compHit (ap1 out w0) (ap1 s O))))
dNeg_from_hitNeg compHit out w0 h =
  let match : Deriv (eqF (eqInd (ap1 thmT w0)
                                (ap1 (negCompCodeF compHit) (ap1 out w0)))
                         (ap1 s O))
      match = ruleTrans (ruleSym (hitNeg_eval compHit out w0)) h
      sound : Deriv (eqF (ap1 thmT w0)
                         (ap1 (negCompCodeF compHit) (ap1 out w0)))
      sound = eqInd_sound (ap1 thmT w0)
                          (ap1 (negCompCodeF compHit) (ap1 out w0)) match
  in ruleTrans sound (negCompCodeF_eval compHit (ap1 out w0))
