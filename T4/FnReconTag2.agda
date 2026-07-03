{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnReconTag2 -- reconstruction of a tag-2 (binary) node under validity: for
-- ANY term x, if  neg (Fst x = natCode 1)  and  wfMarkedF x = O  (validity), then
-- Fst x = natCode 2.  The tag-2 analog of T4.FnReconMb.reconTag0 (which handled
-- tag 0); together they let the ap2 Rcong shape-dispatch enumerate the two
-- possible marked-child shapes (head 1 = ap1, head 2 = ap2) from the single
-- validity + neg (head = 1) fact.
--
-- Argument: classically decide (Fst x = natCode 2).  If so, done.  Otherwise the
-- wfMarkedF reject cascade fires (get_tag skips BOTH the tag-1 fork -- via
-- neg (Fst x = 1) -- and the tag-2 fork -- via neg (Fst x = 2) -- landing on
-- rejectCell = s O), contradicting validity (s O = O) -> anything.  The skips are
-- threaded IMP-FORM over the two negations.
--
--   reconTag2 : imp (neg (Fst x = natCode 1)) (imp (wfMarkedF x = O) (Fst x = natCode 2))
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnReconTag2 where

open import T4.Base

open import T4.OpaqueHarnessImp using ( module HimpBase )
open import T4.ParsObj using ( stepOf )
open import T4.ProgParse using ( get_tag )
open import T4.FoldRec using ( get_newK )
open import T4.FnWfMarked2
  using ( wfMarkedF ; wfAp1CellF ; wfRestCellF ; wfBinCellF ; rejectCell ; testTag )

open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.Dispatch using ( constN_eq )
open import BRA3.ChurchT80 using ( succEqO_to_anything )
open import BRA3.ChurchCM using ( caseElim )
open import BRA3.Logic using ( eqSymImp ; prependEqLeft )
open import BRA3.Classical using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; identP )
open import T4.ForkImp using ( natEqSkipNeg_imp ; fork_false_to_snd_imp )
open import T4.Thm12.ImpHelpers using ( impLift ; impEqTrans ; impCong1 )
open import T4.CtxKit
  using ( lift2 ; get2a ; get2b ; ap2c ; trans2c
        ; lift3 ; get3a ; get3b ; get3c ; ap3c ; trans3c )

open HimpBase Z (stepOf wfAp1CellF wfRestCellF)

------------------------------------------------------------------------

reconTag2 : (x : Term) -> Deriv (neg (eqF x O)) ->
  Deriv (imp (neg (eqF (ap1 Fst x) (natCode 1)))
             (imp (eqF (ap1 wfMarkedF x) O) (eqF (ap1 Fst x) (natCode 2))))
reconTag2 x ne =
  let X2 : Formula                                     -- decided proposition
      X2 = eqF (ap1 Fst x) (natCode 2)
      Ga : Formula                                     -- neg (Fst x = 1)
      Ga = neg (eqF (ap1 Fst x) (natCode 1))
      Gb : Formula                                     -- validity
      Gb = eqF (ap1 wfMarkedF x) O
      Rf : Formula
      Rf = imp Ga (imp Gb X2)
      -- Fst x = 2 branch: conclude regardless of Ga, Gb.
      branchEq : Deriv (imp X2 Rf)
      branchEq = compI (axK X2 Gb) (axK (imp Gb X2) Ga)
      -- neg (Fst x = 2) branch.
      branchNeq : Deriv (imp (neg X2) Rf)
      branchNeq =
        let Gn : Formula                               -- neg (Fst x = 2)
            Gn = neg X2
            stepF : Term
            stepF = ap1 (stepOf wfAp1CellF wfRestCellF) (opkg x)
            wfRest : Term
            wfRest = ap1 wfRestCellF (opkg x)
            rej : Term
            rej = ap1 rejectCell (opkg x)
            -- get_tag (opkg x) = Fst x  (opaque), bare (discharged via ne).
            tagBridge : Deriv (eqF (ap1 get_tag (opkg x)) (ap1 Fst x))
            tagBridge =
              ruleTrans (compose1U_eq Fst get_newK (opkg x))
                (cong1 Fst (mp (op_newK_imp x) ne))
            -- neg (Fst x = k)  =>  neg (get_tag (opkg x) = k) , under H.
            negTag : (H : Formula) (k : Nat) ->
              Deriv (imp H (neg (eqF (ap1 Fst x) (natCode k)))) ->
              Deriv (imp H (neg (eqF (ap1 get_tag (opkg x)) (natCode k))))
            negTag H k nk =
              compI nk
                (mp (axContrapos (eqF (ap1 get_tag (opkg x)) (natCode k))
                                 (eqF (ap1 Fst x) (natCode k)))
                    (prependEqLeft (ap1 Fst x) (ap1 get_tag (opkg x)) (natCode k)
                       (ruleSym tagBridge)))
            ----------------------------------------------------------------
            -- reject value in the 3-context [Gn, Ga, Gb].
            unfoldI : Deriv (imp Gn (eqF (ap1 wfMarkedF x) stepF))
            unfoldI = impLift {Gn} (mp (opUnfold_imp x) ne)
            skip1 : Deriv (imp Ga (eqF stepF wfRest))
            skip1 = fork_false_to_snd_imp Ga wfAp1CellF wfRestCellF (testTag 1) (opkg x)
                      (natEqSkipNeg_imp Ga get_tag 1 (opkg x) (negTag Ga 1 (identP Ga)))
            skip2 : Deriv (imp Gn (eqF wfRest rej))
            skip2 = fork_false_to_snd_imp Gn wfBinCellF rejectCell (testTag 2) (opkg x)
                      (natEqSkipNeg_imp Gn get_tag 2 (opkg x) (negTag Gn 2 (identP Gn)))
            rej3 : Deriv (imp Gn (imp Ga (imp Gb (eqF (ap1 wfMarkedF x) (ap1 s O)))))
            rej3 =
              trans3c (ap1 wfMarkedF x) stepF (ap1 s O)
                (ap3c (lift3 Gn Ga Gb unfoldI) (get3a Gn Ga Gb))
                (trans3c stepF wfRest (ap1 s O)
                   (ap3c (lift3 Gn Ga Gb skip1) (get3b Gn Ga Gb))
                   (trans3c wfRest rej (ap1 s O)
                      (ap3c (lift3 Gn Ga Gb skip2) (get3a Gn Ga Gb))
                      (lift3 Gn Ga Gb (constN_eq 1 (opkg x)))))
            wfMk_O : Deriv (imp Gn (imp Ga (imp Gb (eqF (ap1 wfMarkedF x) O))))
            wfMk_O = get3c Gn Ga Gb
            sOeqO : Deriv (imp Gn (imp Ga (imp Gb (eqF (ap1 s O) O))))
            sOeqO =
              trans3c (ap1 s O) (ap1 wfMarkedF x) O
                (ap3c (lift3 Gn Ga Gb (eqSymImp (ap1 wfMarkedF x) (ap1 s O))) rej3)
                wfMk_O
        in ap3c (lift3 Gn Ga Gb (succEqO_to_anything O X2)) sOeqO
  in caseElim {X = X2} {Y = neg X2} {Rf = Rf}
       (identP (neg X2)) branchEq branchNeq
