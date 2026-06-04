{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefRecogN -- the number-code re-pointing of T4.KdefRecog : the recogniser
-- hitKdefN , subject projector  outKdefN , and firing bridges, over the honest
-- p<N / runProgN K-formula  T4.KdefN  ( instead of the szLeqApp / runProg
-- T4.Kdef ).  Verbatim mirror : KdefRecog is GENERIC in the K-formula's
-- constants ( kdefConsts / Kcode / Kcode_eval / kdefSkel ), so only the  T4.Kdef
-- -> T4.KdefN  swap is needed; the  L  threshold argument is absorbed into the
-- module parameter  predN .

open import T4.Base

module T4.KdefRecogN (predN : Term) where

open import T4.ThmT        using ( thmT )
open import T4.Num         using ( num )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.KdefN predN using ( KdefN ; KcodeN ; KcodeN_eval ; kdefConstsN ; kdefSkelN )
open import T4.KOut        using ( sndProj ; skelOf_proj )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_le_one )
open import T4.Bridge      using ( eqInd_sound )
open import T4.KFire       using ( eqInd_at_eq )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

------------------------------------------------------------------------
-- SECTION 1.  The subject projector  outKdefN .

projKdefN : Fun1
projKdefN = sndProj kdefConstsN

outKdefN : Fun1
outKdefN = compose1U decode (compose1U projKdefN thmT)

-- num-raw correctness:  thmT w = ap1 KcodeN x'  ==>  outKdefN w = x' .
outKdefN_correct :
  (w x' : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeN x')) ->
  Deriv (eqF (ap1 outKdefN w) x')
outKdefN_correct w x' matched =
  let e1 : Deriv (eqF (ap1 outKdefN w)
                      (ap1 decode (ap1 (compose1U projKdefN thmT) w)))
      e1 = compose1U_eq decode (compose1U projKdefN thmT) w

      e2 : Deriv (eqF (ap1 (compose1U projKdefN thmT) w)
                      (ap1 projKdefN (ap1 thmT w)))
      e2 = compose1U_eq projKdefN thmT w

      e3 : Deriv (eqF (ap1 projKdefN (ap1 thmT w)) (ap1 num x'))
      e3 = ruleTrans (cong1 projKdefN (ruleTrans matched (KcodeN_eval x')))
                     (skelOf_proj kdefConstsN (ap1 num x'))

      e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
      e4 = decode_num_id_at x'
  in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

------------------------------------------------------------------------
-- SECTION 2.  The recogniser indicator, parametric in the projector  out .

hitKdefN : Fun1 -> Fun1
hitKdefN out = C eqIndF thmT (compose1U KcodeN out)

hitKdefN_eval :
  (out : Fun1) (w : Term) ->
  Deriv (eqF (ap1 (hitKdefN out) w)
             (eqInd (ap1 thmT w) (ap1 KcodeN (ap1 out w))))
hitKdefN_eval out w =
  ruleTrans (ax_C eqIndF thmT (compose1U KcodeN out) w)
    (ruleTrans (congR eqIndF (ap1 thmT w) (axComp KcodeN out w))
               (eqIndF_eq (ap1 thmT w) (ap1 KcodeN (ap1 out w))))

hitKdefN_le_one :
  (out : Fun1) (w : Term) ->
  Deriv (leq (ap1 (hitKdefN out) w) (ap1 s O))
hitKdefN_le_one out w =
  let c0 : Term
      c0 = ap1 (hitKdefN out) w
      c1 : Term
      c1 = eqInd (ap1 thmT w) (ap1 KcodeN (ap1 out w))
      rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
      rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
             (congL sub (ap1 s O) (hitKdefN_eval out w))
  in mp rw (eqInd_le_one (ap1 thmT w) (ap1 KcodeN (ap1 out w)))

------------------------------------------------------------------------
-- SECTION 3.  Firing  ==>  dNeg .  Subject  x' := ap1 out w0 .

dNeg_from_hitKdefN :
  (out : Fun1) (w0 : Term) ->
  Deriv (eqF (ap1 (hitKdefN out) w0) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT w0) (ap1 KcodeN (ap1 out w0)))
dNeg_from_hitKdefN out w0 h =
  let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 KcodeN (ap1 out w0)))
                         (ap1 s O))
      match = ruleTrans (ruleSym (hitKdefN_eval out w0)) h
  in eqInd_sound (ap1 thmT w0) (ap1 KcodeN (ap1 out w0)) match

------------------------------------------------------------------------
-- SECTION 4.  Provability hypothesis  ==>  the recogniser FIRES at w .

hitKdefN_fires :
  (w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeN x)) ->
  Deriv (eqF (ap1 (hitKdefN outKdefN) w) (ap1 s O))
hitKdefN_fires w x hyp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 KcodeN (ap1 outKdefN w)
      bIsKx : Deriv (eqF B (ap1 KcodeN x))
      bIsKx = cong1 KcodeN (outKdefN_correct w x hyp)
  in ruleTrans (hitKdefN_eval outKdefN w)
       (ruleTrans (ruleSym (eqIndF_eq A B))
         (ruleTrans (congL eqIndF B hyp)
           (ruleTrans (congR eqIndF (ap1 KcodeN x) bIsKx)
             (ruleTrans (eqIndF_eq (ap1 KcodeN x) (ap1 KcodeN x))
               (eqInd_at_eq (ap1 KcodeN x))))))
