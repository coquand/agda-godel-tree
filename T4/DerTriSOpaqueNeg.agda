{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DerTriSOpaqueNeg -- the NEG-FORM Ad-else opaque triFSized equation:
--
--   p != O , dtag p = dgAd , dtag (pL p) != dgZe , dtag (pL p) != dgSu
--     =>  triFSized p = szDerAd (triFSized (pL p)) (triFSized (pR p))
--
-- The shipped  triFSized_op_Ad_else (T4.DerTriSOpaque) is keyed on a LITERAL
-- left-tag  m  with NatNeqWitnesses; this variant takes the symbolic
-- inequalities directly, as the object tag dispatch supplies them (the left
-- tag is only known to be != 0 and != 1).  Same opaque harness + cells; the Ad
-- node cascade skips are the neg-form ones (T4.TagSkipNeg).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.DerTriSOpaqueNeg where

open import T4.Base

open import T4.DerCodeS
  using ( szDerAd ; dtag ; pL ; pR )
open import T4.DerCodeSFun using ( szDerAdF ; szDerAdF_eq )
open import T4.DerCode using ( dgZe ; dgSu ; dgAd )
open import T4.DerTriS
  using ( triStep ; triFSized
        ; cellTriZe ; cellTriSu ; cellTriAdZe ; cellTriAdSu ; cellTriAdElse
        ; triRestSu ; triRestAd ; triRestRO ; adCellTriS ; restAdNodeS
        ; testAdZeS ; testAdSuS ; adLeftTag ; adLeftTagFrom )
open import T4.WfRedSized using ( w20 )
open import T4.WfRedExtract using ( pLValueBound ; pRValueBound )
open import T4.OpaqueLookup using ( lookup_op )
open import T4.FoldRec using ( lookupAt )
open import T4.BinTree using ( nIdx ; lIdx ; rIdx )
open import T4.TagSkipNeg using ( testAdZeS_skip_neg ; testAdSuS_skip_neg )

open import T4.DerSrc
  using ( testEq ; fork_true_to_fst ; fork_false_to_snd ; testEq_fire ; testEq_skip
        ; w21 )

open import BRA3.Church      using ( predecessor )
open import BRA3.PairAlgebra using ( compose1U_eq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.Classical   using ( axContrapos )

import T4.OpaqueHarness
open T4.OpaqueHarness.H triStep

------------------------------------------------------------------------

private
  negTransport : (a b c : Term) -> Deriv (eqF a b) ->
    Deriv (neg (eqF b c)) -> Deriv (neg (eqF a c))
  negTransport a b c ab nbc =
    mp (mp (axContrapos (eqF a c) (eqF b c))
           (prependEqLeft b a c (ruleSym ab))) nbc

triFSized_op_Ad_else_neg : (p : Term) -> Deriv (neg (eqF p O)) ->
  Deriv (eqF (dtag p) dgAd) ->
  Deriv (neg (eqF (dtag (pL p)) dgZe)) ->
  Deriv (neg (eqF (dtag (pL p)) dgSu)) ->
  Deriv (eqF (ap1 triFSized p)
             (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
triFSized_op_Ad_else_neg p ne htag nL0 nL1 =
  let opk : Term
      opk = opkg p
      nieq : Deriv (eqF (ap1 nIdx opk) dgAd)
      nieq = ruleTrans (op_nIdx p ne) htag
      cell_to_ad : Deriv (eqF (ap1 triStep opk) (ap1 adCellTriS opk))
      cell_to_ad =
        ruleTrans (fork_false_to_snd cellTriZe triRestSu (testEq 0) opk
                     (testEq_skip 2 0 opk w20 nieq))
          (ruleTrans (fork_false_to_snd cellTriSu triRestAd (testEq 1) opk
                        (testEq_skip 2 1 opk w21 nieq))
                     (fork_true_to_fst adCellTriS triRestRO (testEq 2) opk
                        (testEq_fire 2 opk nieq)))
      adLeft : Deriv (eqF (ap1 adLeftTag opk) (dtag (pL p)))
      adLeft = adLeftTagFrom opk (pL p) (op_pL p ne)
      negAdZe : Deriv (neg (eqF (ap1 adLeftTag opk) (natCode 0)))
      negAdZe = negTransport (ap1 adLeftTag opk) (dtag (pL p)) (natCode 0) adLeft nL0
      negAdSu : Deriv (neg (eqF (ap1 adLeftTag opk) (natCode 1)))
      negAdSu = negTransport (ap1 adLeftTag opk) (dtag (pL p)) (natCode 1) adLeft nL1
      ad_fires : Deriv (eqF (ap1 adCellTriS opk) (ap1 cellTriAdElse opk))
      ad_fires =
        ruleTrans (fork_false_to_snd cellTriAdZe restAdNodeS testAdZeS opk
                     (testAdZeS_skip_neg opk negAdZe))
                  (fork_false_to_snd cellTriAdSu cellTriAdElse testAdSuS opk
                     (testAdSuS_skip_neg opk negAdSu))
      recL : Deriv (eqF (ap1 (lookupAt lIdx) opk) (ap1 triFSized (pL p)))
      recL = lookup_op Z triStep lIdx (ap1 predecessor p) (pL p)
               (op_pL p ne) (pLValueBound p ne)
      recR : Deriv (eqF (ap1 (lookupAt rIdx) opk) (ap1 triFSized (pR p)))
      recR = lookup_op Z triStep rIdx (ap1 predecessor p) (pR p)
               (op_pR p ne) (pRValueBound p ne)
      cell_val : Deriv (eqF (ap1 cellTriAdElse opk)
                            (szDerAd (ap1 triFSized (pL p)) (ap1 triFSized (pR p))))
      cell_val =
        ruleTrans (ax_C szDerAdF (lookupAt lIdx) (lookupAt rIdx) opk)
          (ruleTrans (congL szDerAdF (ap1 (lookupAt rIdx) opk) recL)
            (ruleTrans (congR szDerAdF (ap1 triFSized (pL p)) recR)
                       (szDerAdF_eq (ap1 triFSized (pL p)) (ap1 triFSized (pR p)))))
  in ruleTrans (opUnfold p ne)
       (ruleTrans cell_to_ad (ruleTrans ad_fires cell_val))
