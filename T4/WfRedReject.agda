{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.WfRedReject -- the JUNK-TAG rejection equation for wfRedSized:
--
--   p != O ,  dtag p  is none of dgZe..dgRS   =>   wfRedSized p = s O
--
-- (so its validity  wfRedSized p = O  is then refutable).  This is the
-- exhaustiveness witness behind the object course-of-values tag dispatch:
-- in the all-skip branch the wfStep cascade falls through to rejectCell =
-- constN 1 = s O.  Built from the wfStep opaque harness (opUnfold) + the
-- neg-form cascade skips (T4.TagSkipNeg).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.WfRedReject where

open import T4.Base

open import T4.DerCodeS using ( dtag )
open import T4.DerCode  using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfStep ; wfRestSu ; wfRestAd ; wfRestRO ; wfRestRS
        ; unaryCell ; binaryCell ; rejectCell )
open import T4.WfRedExtract using ( opkg ; opUnfold ; op_nIdx )
open import T4.DerSrc       using ( testEq ; fork_false_to_snd )
open import T4.TagSkipNeg   using ( testEq_skip_neg )
open import T4.BinTree      using ( nIdx )

open import BRA3.Logic     using ( prependEqLeft )
open import BRA3.Classical using ( axContrapos )

------------------------------------------------------------------------
-- transport a  neg (b = c)  across a subject equality  a = b  to  neg (a = c) .

private
  negTransport : (a b c : Term) -> Deriv (eqF a b) ->
    Deriv (neg (eqF b c)) -> Deriv (neg (eqF a c))
  negTransport a b c ab nbc =
    mp (mp (axContrapos (eqF a c) (eqF b c))
           (prependEqLeft b a c (ruleSym ab))) nbc

------------------------------------------------------------------------

wfRedSized_reject : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (neg (eqF (dtag p) dgZe)) -> Deriv (neg (eqF (dtag p) dgSu)) ->
  Deriv (neg (eqF (dtag p) dgAd)) -> Deriv (neg (eqF (dtag p) dgRO)) ->
  Deriv (neg (eqF (dtag p) dgRS)) ->
  Deriv (eqF (ap1 wfRedSized p) (ap1 s O))
wfRedSized_reject p ne n0 n1 n2 n3 n4 =
  let opk : Term
      opk = opkg p
      oni : Deriv (eqF (ap1 nIdx opk) (dtag p))
      oni = op_nIdx p ne
      k0 : Deriv (neg (eqF (ap1 nIdx opk) (natCode 0)))
      k0 = negTransport (ap1 nIdx opk) (dtag p) (natCode 0) oni n0
      k1 : Deriv (neg (eqF (ap1 nIdx opk) (natCode 1)))
      k1 = negTransport (ap1 nIdx opk) (dtag p) (natCode 1) oni n1
      k2 : Deriv (neg (eqF (ap1 nIdx opk) (natCode 2)))
      k2 = negTransport (ap1 nIdx opk) (dtag p) (natCode 2) oni n2
      k3 : Deriv (neg (eqF (ap1 nIdx opk) (natCode 3)))
      k3 = negTransport (ap1 nIdx opk) (dtag p) (natCode 3) oni n3
      k4 : Deriv (neg (eqF (ap1 nIdx opk) (natCode 4)))
      k4 = negTransport (ap1 nIdx opk) (dtag p) (natCode 4) oni n4
      s0 : Deriv (eqF (ap1 wfStep opk) (ap1 wfRestSu opk))
      s0 = fork_false_to_snd Z wfRestSu (testEq 0) opk (testEq_skip_neg 0 opk k0)
      s1 : Deriv (eqF (ap1 wfRestSu opk) (ap1 wfRestAd opk))
      s1 = fork_false_to_snd unaryCell wfRestAd (testEq 1) opk (testEq_skip_neg 1 opk k1)
      s2 : Deriv (eqF (ap1 wfRestAd opk) (ap1 wfRestRO opk))
      s2 = fork_false_to_snd binaryCell wfRestRO (testEq 2) opk (testEq_skip_neg 2 opk k2)
      s3 : Deriv (eqF (ap1 wfRestRO opk) (ap1 wfRestRS opk))
      s3 = fork_false_to_snd unaryCell wfRestRS (testEq 3) opk (testEq_skip_neg 3 opk k3)
      s4 : Deriv (eqF (ap1 wfRestRS opk) (ap1 rejectCell opk))
      s4 = fork_false_to_snd binaryCell rejectCell (testEq 4) opk (testEq_skip_neg 4 opk k4)
      rej : Deriv (eqF (ap1 rejectCell opk) (natCode 1))
      rej = constN_eq 1 opk
  in ruleTrans (opUnfold p ne)
       (ruleTrans s0 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
         (ruleTrans s4 rej)))))
