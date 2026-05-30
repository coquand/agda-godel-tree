{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KdefRecog -- CGI num-raw step (b): the recogniser  hitKdef , the subject
-- projector  outKdef , and the firing bridge  dNeg_from_hitKdef .  The num-raw
-- analogs of BRA4.KRecog / BRA4.KOut, re-pointed from  negKgtCodeOf / Kgt  to
-- the open  Kcode / Kdef  (BRA4.Kdef).
--
--   outKdef L = decode . sndProj (kdefConsts L) . thmT
--     outKdef_correct : thmT w = ap1 (Kcode L) x'  ==>  outKdef L w = x'
--       -- num-raw, NO isNat: the subject slot is  num x' , and  decode (num x') = x'
--       -- directly (BRA4.Decode.decode_num_id_at).  Cleaner than KOut.out_L_correct.
--
--   hitKdef L out w = eqInd (thmT w) (ap1 (Kcode L) (ap1 out w))      -- 0/1
--     dNeg_from_hitKdef : a firing  hitKdef L out w0 = 1  yields
--       thmT w0 = ap1 (Kcode L) (ap1 out w0)    -- the open dNeg cgiClash consumes.

module BRA4.KdefRecog where

open import BRA4.Base
open import BRA4.ThmT        using ( thmT )
open import BRA4.Decode      using ( decode ; decode_num_id_at )
open import BRA4.Num         using ( num )
open import BRA4.Kdef        using ( Kdef ; Kcode ; Kcode_eval ; kdefConsts ; kdefSkel )
open import BRA4.KOut        using ( sndProj ; skelOf_proj )
open import BRA4.CountingObj using ( eqIndF ; eqIndF_eq )
open import BRA4.Counting    using ( eqInd ; eqInd_le_one )
open import BRA4.Bridge      using ( eqInd_sound )
open import BRA4.KFire       using ( eqInd_at_eq )

open import BRA3.Church      using ( sub )
open import BRA3.ChurchT116  using ( Snd )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

------------------------------------------------------------------------
-- SECTION 1.  The subject projector  outKdef .

projKdef : Term -> Fun1
projKdef L = sndProj (kdefConsts L)

outKdef : Term -> Fun1
outKdef L = compose1U decode (compose1U (projKdef L) thmT)

-- num-raw correctness:  thmT w = ap1 (Kcode L) x'  ==>  outKdef L w = x' .
outKdef_correct :
  (L w x' : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (Kcode L) x')) ->
  Deriv (eqF (ap1 (outKdef L) w) x')
outKdef_correct L w x' matched =
  let e1 : Deriv (eqF (ap1 (outKdef L) w)
                      (ap1 decode (ap1 (compose1U (projKdef L) thmT) w)))
      e1 = compose1U_eq decode (compose1U (projKdef L) thmT) w

      e2 : Deriv (eqF (ap1 (compose1U (projKdef L) thmT) w)
                      (ap1 (projKdef L) (ap1 thmT w)))
      e2 = compose1U_eq (projKdef L) thmT w

      -- thmT w = ap1 (Kcode L) x' = kdefSkel L (num x') = skelOf (kdefConsts L) (num x').
      e3 : Deriv (eqF (ap1 (projKdef L) (ap1 thmT w)) (ap1 num x'))
      e3 = ruleTrans (cong1 (projKdef L) (ruleTrans matched (Kcode_eval L x')))
                     (skelOf_proj (kdefConsts L) (ap1 num x'))

      -- decode (num x') = x'  (no isNat).
      e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
      e4 = decode_num_id_at x'
  in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

------------------------------------------------------------------------
-- SECTION 2.  The recogniser indicator, parametric in the projector  out .

hitKdef : Term -> Fun1 -> Fun1
hitKdef L out = C eqIndF thmT (compose1U (Kcode L) out)

hitKdef_eval :
  (L : Term) (out : Fun1) (w : Term) ->
  Deriv (eqF (ap1 (hitKdef L out) w)
             (eqInd (ap1 thmT w) (ap1 (Kcode L) (ap1 out w))))
hitKdef_eval L out w =
  ruleTrans (ax_C eqIndF thmT (compose1U (Kcode L) out) w)
    (ruleTrans (congR eqIndF (ap1 thmT w) (axComp (Kcode L) out w))
               (eqIndF_eq (ap1 thmT w) (ap1 (Kcode L) (ap1 out w))))

hitKdef_le_one :
  (L : Term) (out : Fun1) (w : Term) ->
  Deriv (leq (ap1 (hitKdef L out) w) (ap1 s O))
hitKdef_le_one L out w =
  let c0 : Term
      c0 = ap1 (hitKdef L out) w
      c1 : Term
      c1 = eqInd (ap1 thmT w) (ap1 (Kcode L) (ap1 out w))
      rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
      rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
             (congL sub (ap1 s O) (hitKdef_eval L out w))
  in mp rw (eqInd_le_one (ap1 thmT w) (ap1 (Kcode L) (ap1 out w)))

------------------------------------------------------------------------
-- SECTION 3.  Firing  ==>  dNeg .  Subject  x' := ap1 out w0 .

dNeg_from_hitKdef :
  (L : Term) (out : Fun1) (w0 : Term) ->
  Deriv (eqF (ap1 (hitKdef L out) w0) (ap1 s O)) ->
  Deriv (eqF (ap1 thmT w0) (ap1 (Kcode L) (ap1 out w0)))
dNeg_from_hitKdef L out w0 h =
  let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 (Kcode L) (ap1 out w0)))
                         (ap1 s O))
      match = ruleTrans (ruleSym (hitKdef_eval L out w0)) h
  in eqInd_sound (ap1 thmT w0) (ap1 (Kcode L) (ap1 out w0)) match

------------------------------------------------------------------------
-- SECTION 4.  The OTHER direction: a provability hypothesis  thmT w = ap1
-- (Kcode L) x  makes the recogniser FIRE at w (the search-exists content).
-- Mirrors  BRA4.KFire.fireAtProof , but sourced from the provability fact
-- (no proof  d , no thmT_complete_rec): outKdef reads  x  back, the two codes
-- coincide, and  eqInd  fires by reflexivity (eqInd_at_eq).

hitKdef_fires :
  (L w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (Kcode L) x)) ->
  Deriv (eqF (ap1 (hitKdef L (outKdef L)) w) (ap1 s O))
hitKdef_fires L w x hyp =
  let A : Term
      A = ap1 thmT w
      B : Term
      B = ap1 (Kcode L) (ap1 (outKdef L) w)
      bIsKx : Deriv (eqF B (ap1 (Kcode L) x))
      bIsKx = cong1 (Kcode L) (outKdef_correct L w x hyp)
  in ruleTrans (hitKdef_eval L (outKdef L) w)
       (ruleTrans (ruleSym (eqIndF_eq A B))
         (ruleTrans (congL eqIndF B hyp)
           (ruleTrans (congR eqIndF (ap1 (Kcode L) x) bIsKx)
             (ruleTrans (eqIndF_eq (ap1 (Kcode L) x) (ap1 (Kcode L) x))
               (eqInd_at_eq (ap1 (Kcode L) x))))))
