{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.KdefRecogConj -- the recogniser  hitKdefConj , subject
-- projector  outKdefConj , and the firing bridge  dNeg_from_hitKdefConj
-- at the NEW conjunction-shape K-formula  KcodeConj M enum  (per
-- T4/NEXT-SESSION-CGICONJ-BODY.md).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   outKdefConj M enum   = compose1U decode (compose1U (projKdefConj M enum) thmT)
--     outKdefConj_correct : thmT w = ap1 (KcodeConj M enum) x  ==>  outKdefConj M enum w = x
--
--   hitKdefConj M enum out w  = eqInd (thmT w) (KcodeConj M enum (out w))   -- 0/1
--     dNeg_from_hitKdefConj  :  hitKdefConj M enum out w = 1
--                                ==>  thmT w = KcodeConj M enum (out w)
--     hitKdefConj_fires      :  thmT w = KcodeConj M enum x
--                                ==>  hitKdefConj M enum (outKdefConj M enum) w = 1
--
-- Mechanical parallel of  T4.KdefRecog  with the search-and-replace
--   Kcode Lstar       ->  KcodeConj M enum
--   kdefConsts Lstar  ->  kdefConjConsts M enum
--   Kcode_eval Lstar  ->  KcodeConj_eval M enum
--
-- The proof skeletons are IDENTICAL ; the only divergence is the
-- code-builder argument .

module T4.SurpriseG2.KdefRecogConj where

open import T4.Base
open import T4.ThmT        using ( thmT )
open import T4.Decode      using ( decode ; decode_num_id_at )
open import T4.Num         using ( num )
open import T4.KOut        using ( sndProj ; skelOf_proj )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_le_one )
open import T4.Bridge      using ( eqInd_sound )
open import T4.KFire       using ( eqInd_at_eq )
open import T4.SurpriseG2.KcodeConj
  using ( KcodeConj ; kdefConjConsts ; kdefConjSkel ; KcodeConj_eval )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

------------------------------------------------------------------------
-- SECTION 1.  The subject projector  outKdefConj .

projKdefConj : Nat -> Fun1 -> Fun1
projKdefConj M enum = sndProj (kdefConjConsts M enum)

outKdefConj : Nat -> Fun1 -> Fun1
outKdefConj M enum = compose1U decode (compose1U (projKdefConj M enum) thmT)

-- num-raw correctness:  thmT w = ap1 (KcodeConj M enum) x'  ==>  outKdefConj M enum w = x' .
outKdefConj_correct :
  (M : Nat) (enum : Fun1) (w x' : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (KcodeConj M enum) x')) ->
  Deriv (eqF (ap1 (outKdefConj M enum) w) x')
outKdefConj_correct M enum w x' matched =
  let e1 : Deriv (eqF (ap1 (outKdefConj M enum) w)
                      (ap1 decode (ap1 (compose1U (projKdefConj M enum) thmT) w)))
      e1 = compose1U_eq decode (compose1U (projKdefConj M enum) thmT) w

      e2 : Deriv (eqF (ap1 (compose1U (projKdefConj M enum) thmT) w)
                      (ap1 (projKdefConj M enum) (ap1 thmT w)))
      e2 = compose1U_eq (projKdefConj M enum) thmT w

      -- thmT w = ap1 (KcodeConj M enum) x' = kdefConjSkel M enum (num x') = skelOf (kdefConjConsts M enum) (num x').
      e3 : Deriv (eqF (ap1 (projKdefConj M enum) (ap1 thmT w)) (ap1 num x'))
      e3 = ruleTrans (cong1 (projKdefConj M enum)
                              (ruleTrans matched (KcodeConj_eval M enum x')))
                     (skelOf_proj (kdefConjConsts M enum) (ap1 num x'))

      -- decode (num x') = x'  (no isNat).
      e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
      e4 = decode_num_id_at x'
  in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

------------------------------------------------------------------------
-- SECTION 2.  The recogniser indicator, parametric in the projector  out .

hitKdefConj : Nat -> Fun1 -> Fun1 -> Fun1
hitKdefConj M enum out = C eqIndF thmT (compose1U (KcodeConj M enum) out)

hitKdefConj_eval :
  (M : Nat) (enum : Fun1) (out : Fun1) (w : Term) ->
  Deriv (eqF (ap1 (hitKdefConj M enum out) w)
             (eqInd (ap1 thmT w) (ap1 (KcodeConj M enum) (ap1 out w))))
hitKdefConj_eval M enum out w =
  ruleTrans (ax_C eqIndF thmT (compose1U (KcodeConj M enum) out) w)
    (ruleTrans (congR eqIndF (ap1 thmT w) (axComp (KcodeConj M enum) out w))
               (eqIndF_eq (ap1 thmT w) (ap1 (KcodeConj M enum) (ap1 out w))))

hitKdefConj_le_one :
  (M : Nat) (enum : Fun1) (out : Fun1) (w : Term) ->
  Deriv (leq (ap1 (hitKdefConj M enum out) w) (ap1 s O))
hitKdefConj_le_one M enum out w =
  let c0 : Term
      c0 = ap1 (hitKdefConj M enum out) w
      c1 : Term
      c1 = eqInd (ap1 thmT w) (ap1 (KcodeConj M enum) (ap1 out w))
      rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
      rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
             (congL sub (ap1 s O) (hitKdefConj_eval M enum out w))
  in mp rw (eqInd_le_one (ap1 thmT w) (ap1 (KcodeConj M enum) (ap1 out w)))

------------------------------------------------------------------------
-- SECTION 3.  Firing  ==>  dNeg .  Subject  x' := ap1 out w0 .

dNeg_from_hitKdefConj :
  (M : Nat) (enum : Fun1) (out : Fun1) (w0 : Term) ->
  Deriv (eqF (ap1 (hitKdefConj M enum out) w0) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT w0) (ap1 (KcodeConj M enum) (ap1 out w0)))
dNeg_from_hitKdefConj M enum out w0 h =
  let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 (KcodeConj M enum) (ap1 out w0)))
                          (ap1 s O))
      match = ruleTrans (ruleSym (hitKdefConj_eval M enum out w0)) h
  in eqInd_sound (ap1 thmT w0) (ap1 (KcodeConj M enum) (ap1 out w0)) match

------------------------------------------------------------------------
-- SECTION 4.  Reverse: a provability hypothesis  thmT w = ap1 (KcodeConj
-- M enum) x  makes the recogniser FIRE at  w .   Mirrors
-- T4.KdefRecog.hitKdef_fires .

hitKdefConj_fires :
  (M : Nat) (enum : Fun1) (w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (KcodeConj M enum) x)) ->
  Deriv (eqF (ap1 (hitKdefConj M enum (outKdefConj M enum)) w) (ap1 s O))
hitKdefConj_fires M enum w x hyp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 (KcodeConj M enum) (ap1 (outKdefConj M enum) w)
      bIsKx : Deriv (eqF B (ap1 (KcodeConj M enum) x))
      bIsKx = cong1 (KcodeConj M enum) (outKdefConj_correct M enum w x hyp)
  in ruleTrans (hitKdefConj_eval M enum (outKdefConj M enum) w)
       (ruleTrans (ruleSym (eqIndF_eq A B))
         (ruleTrans (congL eqIndF B hyp)
           (ruleTrans (congR eqIndF (ap1 (KcodeConj M enum) x) bIsKx)
             (ruleTrans (eqIndF_eq (ap1 (KcodeConj M enum) x) (ap1 (KcodeConj M enum) x))
               (eqInd_at_eq (ap1 (KcodeConj M enum) x))))))
