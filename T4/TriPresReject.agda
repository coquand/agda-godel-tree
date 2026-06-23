{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriPresReject -- the REJECT leaf of the object tag dispatch.  Under the
-- five tag-negations (dtag p is none of dgZe..dgRS) AND the combined antecedent
-- PA = (sigma Xbig (wfRedSized p) = O), the verifier's reject cascade gives
-- wfRedSized p = s O , contradicting wfRedSized p = O (from PA), so anything --
-- in particular  wfRedSized (triFSized p) = O .
--
-- Carried in the depth-6 context [nRS, nRO, nAd, nSu, nZe, PA] matching the
-- innermost else-branch of the nested caseElim.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.TriPresReject where

open import T4.Base

open import T4.DerCodeS using ( dtag )
open import T4.DerCode  using ( dgZe ; dgSu ; dgAd ; dgRO ; dgRS )
open import T4.WfRedSized
  using ( wfRedSized ; wfStep ; unaryCell ; binaryCell ; rejectCell
        ; wfRestSu ; wfRestAd ; wfRestRO ; wfRestRS )
open import T4.WfRedExtract using ( opkg ; opUnfold ; op_nIdx )
open import T4.DerTriS using ( triFSized )
open import T4.DerSrc using ( testEq )
open import T4.BinTree using ( nIdx )

open import T4.ForkImp using ( natEqSkipNeg_imp ; fork_false_to_snd_imp )
open import T4.CtxKit
  using ( lift6 ; get6a ; get6b ; get6c ; get6d ; get6e ; get6f ; ap6c ; trans6c )

open import BRA3.Church      using ( sigma ; pi )
open import T4.SigmaZeroN    using ( sigmaZeroR )
open import BRA3.Logic       using ( eqSymImp ; prependEqLeft )
open import BRA3.Classical   using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; identP )
open import BRA3.Dispatch    using ( constN_eq )
open import BRA3.ChurchT80   using ( succEqO_to_anything )

------------------------------------------------------------------------

private
  -- negK_imp p ne k : neg(dtag p = natCode k) => neg(nIdx (opkg p) = natCode k).
  negK_imp : (p : Term) -> Deriv (neg (eqF p O)) -> (k : Nat) ->
    Deriv (imp (neg (eqF (dtag p) (natCode k)))
               (neg (eqF (ap1 nIdx (opkg p)) (natCode k))))
  negK_imp p ne k =
    mp (axContrapos (eqF (ap1 nIdx (opkg p)) (natCode k)) (eqF (dtag p) (natCode k)))
       (prependEqLeft (dtag p) (ap1 nIdx (opkg p)) (natCode k) (ruleSym (op_nIdx p ne)))

  -- a single cascade step over the neg antecedent (dtag p /= natCode k).
  cascStep : (p : Term) -> Deriv (neg (eqF p O)) ->
    (k : Nat) (A Bcell : Fun1) ->
    Deriv (imp (neg (eqF (dtag p) (natCode k)))
               (eqF (ap1 (C condFork (C pi A Bcell) (testEq k)) (opkg p))
                    (ap1 Bcell (opkg p))))
  cascStep p ne k A Bcell =
    let Hk : Formula
        Hk = neg (eqF (dtag p) (natCode k))
    in fork_false_to_snd_imp Hk A Bcell (testEq k) (opkg p)
         (natEqSkipNeg_imp Hk nIdx k (opkg p)
           (compI (identP Hk) (negK_imp p ne k)))

rejectLeaf : (p Xbig : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (imp (neg (eqF (dtag p) dgRS))
        (imp (neg (eqF (dtag p) dgRO))
        (imp (neg (eqF (dtag p) dgAd))
        (imp (neg (eqF (dtag p) dgSu))
        (imp (neg (eqF (dtag p) dgZe))
        (imp (eqF (ap2 sigma Xbig (ap1 wfRedSized p)) O)
             (eqF (ap1 wfRedSized (ap1 triFSized p)) O)))))))
rejectLeaf p Xbig ne =
  let opk : Term
      opk = opkg p
      B : Formula
      B = eqF (ap1 wfRedSized (ap1 triFSized p)) O
      PA : Formula
      PA = eqF (ap2 sigma Xbig (ap1 wfRedSized p)) O
      Ga : Formula
      Ga = neg (eqF (dtag p) dgRS)
      Gb : Formula
      Gb = neg (eqF (dtag p) dgRO)
      Gc : Formula
      Gc = neg (eqF (dtag p) dgAd)
      Gd : Formula
      Gd = neg (eqF (dtag p) dgSu)
      Ge : Formula
      Ge = neg (eqF (dtag p) dgZe)
      -- the five steps, lifted into the depth-6 context.
      s0 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                  (eqF (ap1 wfStep opk) (ap1 wfRestSu opk))))))))
      s0 = ap6c (lift6 Ga Gb Gc Gd Ge PA (cascStep p ne 0 Z wfRestSu))
                (get6e Ga Gb Gc Gd Ge PA)
      s1 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                  (eqF (ap1 wfRestSu opk) (ap1 wfRestAd opk))))))))
      s1 = ap6c (lift6 Ga Gb Gc Gd Ge PA (cascStep p ne 1 unaryCell wfRestAd))
                (get6d Ga Gb Gc Gd Ge PA)
      s2 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                  (eqF (ap1 wfRestAd opk) (ap1 wfRestRO opk))))))))
      s2 = ap6c (lift6 Ga Gb Gc Gd Ge PA (cascStep p ne 2 binaryCell wfRestRO))
                (get6c Ga Gb Gc Gd Ge PA)
      s3 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                  (eqF (ap1 wfRestRO opk) (ap1 wfRestRS opk))))))))
      s3 = ap6c (lift6 Ga Gb Gc Gd Ge PA (cascStep p ne 3 unaryCell wfRestRS))
                (get6b Ga Gb Gc Gd Ge PA)
      s4 : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                  (eqF (ap1 wfRestRS opk) (ap1 rejectCell opk))))))))
      s4 = ap6c (lift6 Ga Gb Gc Gd Ge PA (cascStep p ne 4 binaryCell rejectCell))
                (get6a Ga Gb Gc Gd Ge PA)
      cascade : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                  (eqF (ap1 wfStep opk) (ap1 rejectCell opk))))))))
      cascade =
        trans6c (ap1 wfStep opk) (ap1 wfRestSu opk) (ap1 rejectCell opk) s0
          (trans6c (ap1 wfRestSu opk) (ap1 wfRestAd opk) (ap1 rejectCell opk) s1
            (trans6c (ap1 wfRestAd opk) (ap1 wfRestRO opk) (ap1 rejectCell opk) s2
              (trans6c (ap1 wfRestRO opk) (ap1 wfRestRS opk) (ap1 rejectCell opk) s3 s4)))
      -- wfRedSized p = wfStep opk = rejectCell opk = s O .
      wfRedO_sO : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                    (eqF (ap1 wfRedSized p) (ap1 s O))))))))
      wfRedO_sO =
        trans6c (ap1 wfRedSized p) (ap1 wfStep opk) (ap1 s O)
          (lift6 Ga Gb Gc Gd Ge PA (opUnfold p ne))
          (trans6c (ap1 wfStep opk) (ap1 rejectCell opk) (ap1 s O)
            cascade
            (lift6 Ga Gb Gc Gd Ge PA (constN_eq 1 opk)))
      -- PA gives wfRedSized p = O .
      wfRedO : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                 (eqF (ap1 wfRedSized p) O)))))))
      wfRedO = ap6c (lift6 Ga Gb Gc Gd Ge PA
                      (sigmaZeroR Xbig (ap1 wfRedSized p)))
                    (get6f Ga Gb Gc Gd Ge PA)
      -- hence s O = O .
      sOeqO : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp PA
                (eqF (ap1 s O) O)))))))
      sOeqO =
        trans6c (ap1 s O) (ap1 wfRedSized p) O
          (ap6c (lift6 Ga Gb Gc Gd Ge PA (eqSymImp (ap1 wfRedSized p) (ap1 s O)))
                wfRedO_sO)
          wfRedO
  in ap6c (lift6 Ga Gb Gc Gd Ge PA (succEqO_to_anything O B)) sOeqO
