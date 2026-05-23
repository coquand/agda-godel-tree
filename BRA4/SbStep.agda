{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbStep -- generic single-substitution "one-pass" step combinators
-- plus the  InertU  hypothesis type and a structural  NumCode  predicate
-- discharging it.
--
-- These are the building blocks for ELIMINATING the simultaneous
-- substitution functors  sbt2 / sbt3 / sbf2 / sbf3  (see
--  BRA4/NEXT-SESSION-ELIMINATE-SBT2-SBT3.md ).  An  sb2 / sb3  code-wrap
-- is replaced by a NESTED single- sb  wrap; thmT decodes it with
--  thmT_at_sb  applied twice / thrice, producing  sbf spec0 (sbf spec1 ...) .
-- Each nested  sbf / sbt  pass walks the SAME formula skeleton with its
-- var-leaves substituted; the combinators here perform one node of such a
-- pass, given the results on the sub-positions.
--
--   sbf_step_imp     : sbf over an  imp  node.
--   sbf_step_atomic  : sbf over an  eq (atomic) node.
--   sbf_step_neg     : sbf over a   neg  node.
--   sbt_step_ap1     : sbt over an  ap1  node (functor opaque).
--   sbt_step_ap2     : sbt over an  ap2  node (functor opaque).
--
-- The OUTER passes re-scan substituents planted by INNER passes.  When a
-- planted substituent is  num-based  (the Thm 12 situation) it is INERT
-- under every single-variable substitution -- that property is  InertU ,
-- discharged structurally by  sbt_inert_NumCode  from a  NumCode  witness.

module BRA4.SbStep where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code     using ( codeFun1 ; codeFun2 )
open import BRA4.Num      using ( num )
open import BRA4.SbT      using ( sbt ; sbt_at_O )
open import BRA4.SbtAtAp  using ( sbt_at_ap1 ; sbt_at_ap2 )
open import BRA4.SbF      using ( sbf )
open import BRA4.SbfAtClosures using ( sbf_at_atomic ; sbf_at_neg ; sbf_at_imp )
open import BRA4.NumInert  using ( sbt_num_inert )
open import BRA4.NumInertCode using ( sbt_inert_ap1 ; sbt_inert_ap2 )

------------------------------------------------------------------------
-- Generic single-pass step combinators.
--
-- Throughout,  spec = ap2 Pair (natCode k) S  is the single-variable
-- substitution code  (var k := S) .

-- sbf over an  imp  node :  sbf spec (imp ca cb) = imp (sbf spec ca) (sbf spec cb) .
sbf_step_imp :
  (k : Nat) (S ca cb ca' cb' : Term) ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) ca) ca') ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) cb) cb') ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_imp) (ap2 Pair ca cb)))
              (ap2 Pair (natCode tag_imp) (ap2 Pair ca' cb')))
sbf_step_imp k S ca cb ca' cb' ea eb =
  let spec : Term
      spec = ap2 Pair (natCode k) S
  in ruleTrans (sbf_at_imp k S ca cb)
       (congR Pair (natCode tag_imp)
         (ruleTrans (congL Pair (ap2 sbf spec cb) ea)
                    (congR Pair ca' eb)))

-- sbf over an  eq (atomic) node :  sub-positions use  sbt .
sbf_step_atomic :
  (k : Nat) (S ca cb ca' cb' : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ca) ca') ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) cb) cb') ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_eq) (ap2 Pair ca cb)))
              (ap2 Pair (natCode tag_eq) (ap2 Pair ca' cb')))
sbf_step_atomic k S ca cb ca' cb' ea eb =
  let spec : Term
      spec = ap2 Pair (natCode k) S
  in ruleTrans (sbf_at_atomic k S ca cb)
       (congR Pair (natCode tag_eq)
         (ruleTrans (congL Pair (ap2 sbt spec cb) ea)
                    (congR Pair ca' eb)))

-- sbf over a  neg  node.
sbf_step_neg :
  (k : Nat) (S cP cP' : Term) ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) cP) cP') ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_neg) cP))
              (ap2 Pair (natCode tag_neg) cP'))
sbf_step_neg k S cP cP' e =
  ruleTrans (sbf_at_neg k S cP)
    (congR Pair (natCode tag_neg) e)

-- sbt over an  ap1  node :  functor code  codeFun1 f  stays opaque.
sbt_step_ap1 :
  (k : Nat) (S : Term) (f : Fun1) (ct ct' : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ct) ct') ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
              (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct')))
sbt_step_ap1 k S f ct ct' e =
  ruleTrans (sbt_at_ap1 k S f ct)
    (congR Pair (natCode tag_ap1) (congR Pair (codeFun1 f) e))

-- sbt over an  ap2  node :  functor code  codeFun2 g  stays opaque.
sbt_step_ap2 :
  (k : Nat) (S : Term) (g : Fun2) (ca cb ca' cb' : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) ca) ca') ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) cb) cb') ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
               (ap2 Pair (natCode tag_ap2)
                 (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
              (ap2 Pair (natCode tag_ap2)
                (ap2 Pair (codeFun2 g) (ap2 Pair ca' cb'))))
sbt_step_ap2 k S g ca cb ca' cb' ea eb =
  let spec : Term
      spec = ap2 Pair (natCode k) S
  in ruleTrans (sbt_at_ap2 k S g ca cb)
       (congR Pair (natCode tag_ap2)
         (congR Pair (codeFun2 g)
           (ruleTrans (congL Pair (ap2 sbt spec cb) ea)
                      (congR Pair ca' eb))))

------------------------------------------------------------------------
-- InertU :  T  is INERT under EVERY single-variable substitution.
--
-- This is exactly the hypothesis the encoded-axiom lemmas need on each
-- substituent that an outer  sbf / sbt  pass re-scans.

InertU : Term -> Set
InertU T = (k : Nat) (S : Term) ->
           Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) T) T)

------------------------------------------------------------------------
-- NumCode :  the grammar of  num-based composite codes.  Every closed
-- numeral leaf  (ap1 num x , for ARBITRARY object  x )  is inert
-- (sbt_num_inert), and the  ap1 / ap2  wrappers preserve inertness, so
-- any  NumCode  is  InertU .

data NumCode : Term -> Set where
  ncO   : NumCode O
  ncNum : (x : Term) -> NumCode (ap1 num x)
  ncAp1 : (f : Fun1) (ct : Term) ->
          NumCode ct ->
          NumCode (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct))
  ncAp2 : (g : Fun2) (ca cb : Term) ->
          NumCode ca -> NumCode cb ->
          NumCode (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g) (ap2 Pair ca cb)))

-- A  NumCode  is  InertU .
sbt_inert_NumCode : (T : Term) -> NumCode T -> InertU T
sbt_inert_NumCode .O ncO k S = sbt_at_O (ap2 Pair (natCode k) S)
sbt_inert_NumCode .(ap1 num x) (ncNum x) k S = sbt_num_inert k S x
sbt_inert_NumCode _ (ncAp1 f ct p) k S =
  sbt_inert_ap1 k S f ct (sbt_inert_NumCode ct p k S)
sbt_inert_NumCode _ (ncAp2 g ca cb pa pb) k S =
  sbt_inert_ap2 k S g ca cb
    (sbt_inert_NumCode ca pa k S)
    (sbt_inert_NumCode cb pb k S)
