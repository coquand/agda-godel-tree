{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.KFire -- THE FIRING, derived from thmT-completeness.
--
-- If T proves  K(z) > L  (a derivation  d : Deriv (Kgt L (natCode z)) ), then:
--   * the recogniser  hitK L (out_L L)  FIRES (= 1) at the proof-code  encode d ;
--   * the projector  out_L L  reads the subject  z  back off  encode d .
--
-- This is exactly the search-exists content that is genuinely a consequence of
-- the proof  d  + the checker's completeness:
--   thmT_complete_rec d : thmT (encode d) = codeFormula (Kgt L (natCode z))
-- so  thmT(encode d)  and  negKgtCodeOf L (out_L L (encode d))  are BOTH the code
-- of  Kgt L (natCode z) , whence the equality-indicator eqInd fires.  No search
-- ORDER is involved here (that is the separate minimisation); this is just
-- "the proof's own code is a hit, with subject z".
--
-- NOTE (codes are numbers).  encode d is a pi-pairing term; since  Pair = pi  is
-- the numeric pairing, it is a Gödel number -- so this object firing is exactly
-- a firing at the natural number coding the proof, i.e. a hit the number-search
-- can reach.  The firing position is the object term  encode d  (a number).

module BRA4.KFire where

open import BRA4.Base
open import BRA4.Code            using ( codeFormula )
open import BRA4.ThmT            using ( thmT )
open import BRA4.ThmTCompleteRec using ( thmT_complete_rec )
open import BRA4.Encode          using ( encode )
open import BRA4.KFormula        using ( Kgt ; negKgtCodeOf ; negKgtCodeOf_correct
                                       ; negKgtCodeOf_correct_T )
open import BRA4.KRecog          using ( hitK ; hitK_eval )
open import BRA4.KOut            using ( out_L ; out_L_correct ; out_L_correct_T )
open import BRA4.IsNat           using ( isNat )
open import BRA4.Counting        using ( eqInd )
open import BRA4.CountingObj     using ( eqIndF ; eqIndF_eq )
open import BRA4.PHP             using ( indLt )

open import BRA3.Church            using ( sub )
open import BRA3.ChurchSubSucc     using ( T_sub_O )
open import BRA3.RecBRA3AtPairUniv using ( sub_self ; sub_succ_self )

------------------------------------------------------------------------
-- eqInd at equal arguments fires:  eqInd a a = 1  (self-contained; the
-- arithmetic shadow  sub (s O) O = s O  after sub_self / sub_succ_self).

eqInd_at_eq : (a : Term) -> Deriv (eqF (eqInd a a) (ap1 s O))
eqInd_at_eq a =
  let e_hi : Deriv (eqF (indLt a (ap1 s a)) (ap1 s O))
      e_hi = ruleTrans (congR sub (ap1 s O) (sub_self (ap1 s a))) (T_sub_O (ap1 s O))
      e_lo : Deriv (eqF (indLt a a) O)
      e_lo = ruleTrans (congR sub (ap1 s O) (sub_succ_self a)) (sub_self (ap1 s O))
  in ruleTrans (congL sub (indLt a a) e_hi)
       (ruleTrans (congR sub (ap1 s O) e_lo) (T_sub_O (ap1 s O)))

------------------------------------------------------------------------
-- The subject readout and the firing, at the proof-code  encode d .

module _ (L : Term) (z : Nat) (d : Deriv (Kgt L (natCode z))) where

  private
    cKgt : Term
    cKgt = codeFormula (Kgt L (natCode z))

    tc : Deriv (eqF (ap1 thmT (encode d)) cKgt)
    tc = thmT_complete_rec d

  -- out_L reads off the subject z at the proof-code.
  subjAtProof : Deriv (eqF (ap1 (out_L L) (encode d)) (natCode z))
  subjAtProof = out_L_correct L (encode d) z tc

  -- the recogniser FIRES at the proof-code:  hitK L (out_L L) (encode d) = 1 .
  fireAtProof : Deriv (eqF (ap1 (hitK L (out_L L)) (encode d)) (ap1 s O))
  fireAtProof =
    let A : Term
        A = ap1 thmT (encode d)
        B : Term
        B = ap1 (negKgtCodeOf L) (ap1 (out_L L) (encode d))
        bIsC : Deriv (eqF B cKgt)
        bIsC = ruleTrans (cong1 (negKgtCodeOf L) subjAtProof)
                         (negKgtCodeOf_correct L z)
    in ruleTrans (hitK_eval L (out_L L) (encode d))
         (ruleTrans (ruleSym (eqIndF_eq A B))
           (ruleTrans (congL eqIndF B tc)
             (ruleTrans (congR eqIndF cKgt bIsC)
               (ruleTrans (eqIndF_eq cKgt cKgt) (eqInd_at_eq cKgt)))))

------------------------------------------------------------------------
-- The TERM-subject firing.  Same as above but the subject is a Term  x  that
-- is a numeral (isNat x), NOT a meta  Nat  -- so the assumed proof  d  is of
-- Kgt L x  for an object term  x  ("for some integer  x , a proof of K(x)>L").

module _ (L : Term) (x : Term) (nx : isNat x) (d : Deriv (Kgt L x)) where

  private
    cKgtT : Term
    cKgtT = codeFormula (Kgt L x)

    tcT : Deriv (eqF (ap1 thmT (encode d)) cKgtT)
    tcT = thmT_complete_rec d

  -- out_L reads off the subject  x  at the proof-code.
  subjAtProof_T : Deriv (eqF (ap1 (out_L L) (encode d)) x)
  subjAtProof_T = out_L_correct_T L (encode d) x nx tcT

  -- the recogniser FIRES at the proof-code:  hitK L (out_L L) (encode d) = 1 .
  fireAtProof_T : Deriv (eqF (ap1 (hitK L (out_L L)) (encode d)) (ap1 s O))
  fireAtProof_T =
    let A : Term
        A = ap1 thmT (encode d)
        B : Term
        B = ap1 (negKgtCodeOf L) (ap1 (out_L L) (encode d))
        bIsC : Deriv (eqF B cKgtT)
        bIsC = ruleTrans (cong1 (negKgtCodeOf L) subjAtProof_T)
                         (negKgtCodeOf_correct_T L x nx)
    in ruleTrans (hitK_eval L (out_L L) (encode d))
         (ruleTrans (ruleSym (eqIndF_eq A B))
           (ruleTrans (congL eqIndF B tcT)
             (ruleTrans (congR eqIndF cKgtT bIsC)
               (ruleTrans (eqIndF_eq cKgtT cKgtT) (eqInd_at_eq cKgtT)))))
