{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefRecogAlph -- the  checkAlphN -guard analog of  T4.KdefRecog .
-- outKdefAlph / hitKdefAlph / dNeg_from_hitKdefAlph / hitKdefAlph_fires ,
-- re-pointed from  Kcode / outKdef  to  KcodeAlph / outKdefAlph .  The bodies
-- are GENERIC in  Kcode / kdefConsts ; only the imports change.

open import T4.Base

module T4.KdefRecogAlph (Lstar_meta : Nat) where

open import T4.ThmT        using ( thmT )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.Num         using ( num )
open import T4.KdefAlph Lstar_meta
  using ( KdefAlph ; KcodeAlph ; KcodeAlph_eval ; kdefAlphConsts ; kdefAlphSkel )
open import T4.KOut        using ( sndProj ; skelOf_proj )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_le_one )
open import T4.Bridge      using ( eqInd_sound )
open import T4.KFire       using ( eqInd_at_eq )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchT116  using ( Snd )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

------------------------------------------------------------------------
-- SECTION 1.  The subject projector  outKdefAlph .

projKdefAlph : Fun1
projKdefAlph = sndProj kdefAlphConsts

outKdefAlph : Fun1
outKdefAlph = compose1U decode (compose1U projKdefAlph thmT)

outKdefAlph_correct :
  (w x' : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeAlph x')) ->
  Deriv (eqF (ap1 outKdefAlph w) x')
outKdefAlph_correct w x' matched =
  let e1 : Deriv (eqF (ap1 outKdefAlph w)
                      (ap1 decode (ap1 (compose1U projKdefAlph thmT) w)))
      e1 = compose1U_eq decode (compose1U projKdefAlph thmT) w

      e2 : Deriv (eqF (ap1 (compose1U projKdefAlph thmT) w)
                      (ap1 projKdefAlph (ap1 thmT w)))
      e2 = compose1U_eq projKdefAlph thmT w

      e3 : Deriv (eqF (ap1 projKdefAlph (ap1 thmT w)) (ap1 num x'))
      e3 = ruleTrans (cong1 projKdefAlph (ruleTrans matched (KcodeAlph_eval x')))
                     (skelOf_proj kdefAlphConsts (ap1 num x'))

      e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
      e4 = decode_num_id_at x'
  in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

------------------------------------------------------------------------
-- SECTION 2.  The recogniser indicator, parametric in the projector  out .

hitKdefAlph : Fun1 -> Fun1
hitKdefAlph out = C eqIndF thmT (compose1U KcodeAlph out)

hitKdefAlph_eval :
  (out : Fun1) (w : Term) ->
  Deriv (eqF (ap1 (hitKdefAlph out) w)
             (eqInd (ap1 thmT w) (ap1 KcodeAlph (ap1 out w))))
hitKdefAlph_eval out w =
  ruleTrans (ax_C eqIndF thmT (compose1U KcodeAlph out) w)
    (ruleTrans (congR eqIndF (ap1 thmT w) (axComp KcodeAlph out w))
               (eqIndF_eq (ap1 thmT w) (ap1 KcodeAlph (ap1 out w))))

hitKdefAlph_le_one :
  (out : Fun1) (w : Term) ->
  Deriv (leq (ap1 (hitKdefAlph out) w) (ap1 s O))
hitKdefAlph_le_one out w =
  let c0 : Term
      c0 = ap1 (hitKdefAlph out) w
      c1 : Term
      c1 = eqInd (ap1 thmT w) (ap1 KcodeAlph (ap1 out w))
      rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
      rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
             (congL sub (ap1 s O) (hitKdefAlph_eval out w))
  in mp rw (eqInd_le_one (ap1 thmT w) (ap1 KcodeAlph (ap1 out w)))

------------------------------------------------------------------------
-- SECTION 3.  Firing  ==>  dNeg .  Subject  x' := ap1 out w0 .

dNeg_from_hitKdefAlph :
  (out : Fun1) (w0 : Term) ->
  Deriv (eqF (ap1 (hitKdefAlph out) w0) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT w0) (ap1 KcodeAlph (ap1 out w0)))
dNeg_from_hitKdefAlph out w0 h =
  let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 KcodeAlph (ap1 out w0)))
                         (ap1 s O))
      match = ruleTrans (ruleSym (hitKdefAlph_eval out w0)) h
  in eqInd_sound (ap1 thmT w0) (ap1 KcodeAlph (ap1 out w0)) match

------------------------------------------------------------------------
-- SECTION 4.  Provability hypothesis  thmT w = ap1 KcodeAlph x  makes the
-- recogniser FIRE at w.

hitKdefAlph_fires :
  (w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 KcodeAlph x)) ->
  Deriv (eqF (ap1 (hitKdefAlph outKdefAlph) w) (ap1 s O))
hitKdefAlph_fires w x hyp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 KcodeAlph (ap1 outKdefAlph w)
      bIsKx : Deriv (eqF B (ap1 KcodeAlph x))
      bIsKx = cong1 KcodeAlph (outKdefAlph_correct w x hyp)
  in ruleTrans (hitKdefAlph_eval outKdefAlph w)
       (ruleTrans (ruleSym (eqIndF_eq A B))
         (ruleTrans (congL eqIndF B hyp)
           (ruleTrans (congR eqIndF (ap1 KcodeAlph x) bIsKx)
             (ruleTrans (eqIndF_eq (ap1 KcodeAlph x) (ap1 KcodeAlph x))
               (eqInd_at_eq (ap1 KcodeAlph x))))))
