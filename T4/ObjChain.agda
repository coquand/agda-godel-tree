{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ObjChain -- object reduction traces (chains of object cert CODES) and the
-- ze-leg head-stability, finishing toward  objJoinClash .
--
-- A trace  a =>* w  is a chain of non-reflexive object cert steps (each  d  a
-- Term with  d != O ,  src d = a' ,  tgt d = m ); endpoints carried as Deriv
-- side-conditions (the object src/tgt are fold applications, not Agda-equal to
-- the codes).  Reflexive steps are omitted WLOG.
--
-- ze-leg head-stability is then immediate: ze# is normal, so a non-reflexive
-- step from a ze-headed term is EX FALSO (T4.CertHeadZeObj.certHeadZe_step),
-- which short-circuits the whole tail to the goal -- no recursion needed.
--
--   chainHeadZe_obj : ObjChainM a w -> hd a = tagZe -> hd w = tagZe
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ObjChain where

open import T4.Base

open import T4.ParEnds     using ( src ; tgt )
open import T4.CertHeadZeObj using ( certHeadZe_step )
open import T4.CertHeadSuObj using ( certHeadSu_step )
open import T4.TrsCodeObj  using ( tagZe ; tagSu ; ze# ; su# ; hd_ze ; hd_su )

open import BRA3.ChurchT80 using ( succEqO_to_anything )

------------------------------------------------------------------------
-- Object reduction traces (non-reflexive cert-code steps).

data ObjChainM : Term -> Term -> Set where
  ocnil  : {a : Term} -> ObjChainM a a
  occons : {a m w : Term} (d : Term) ->
           Deriv (neg (eqF d O)) ->
           Deriv (eqF (ap1 src d) a) ->
           Deriv (eqF (ap1 tgt d) m) ->
           ObjChainM m w ->
           ObjChainM a w

------------------------------------------------------------------------
-- ze-leg head-stability (ze# normal: any real step from ze-head is ex falso).

chainHeadZe_obj : {a w : Term} -> ObjChainM a w ->
                  Deriv (eqF (ap1 Fst a) tagZe) -> Deriv (eqF (ap1 Fst w) tagZe)
chainHeadZe_obj ocnil hyp = hyp
chainHeadZe_obj {a} {w} (occons d ne srcEq tgtEq rest) hyp =
  certHeadZe_step d (eqF (ap1 Fst w) tagZe) ne
    (ruleTrans (cong1 Fst srcEq) hyp)

------------------------------------------------------------------------
-- su-leg head-stability (su# CAN step, so this RECURSES via certHeadSu_step).

chainHeadSu_obj : {a w : Term} -> ObjChainM a w ->
                  Deriv (eqF (ap1 Fst a) tagSu) -> Deriv (eqF (ap1 Fst w) tagSu)
chainHeadSu_obj ocnil hyp = hyp
chainHeadSu_obj (occons d ne srcEq tgtEq rest) hyp =
  let tgtHead : Deriv (eqF (ap1 Fst (ap1 tgt d)) tagSu)
      tgtHead = certHeadSu_step d ne (ruleTrans (cong1 Fst srcEq) hyp)
      mHead : Deriv (eqF (ap1 Fst _) tagSu)
      mHead = ruleTrans (ruleSym (cong1 Fst tgtEq)) tgtHead
  in chainHeadSu_obj rest mHead

------------------------------------------------------------------------
-- THE CLASH:  0 and s0 have no common reduct (object Con(T0) core, arrow 3c).

objJoinClash : (w : Term) (Q : Formula) ->
  ObjChainM ze# w -> ObjChainM (su# ze#) w -> Deriv Q
objJoinClash w Q leg0 legS =
  let fwZe : Deriv (eqF (ap1 Fst w) tagZe)
      fwZe = chainHeadZe_obj leg0 hd_ze
      fwSu : Deriv (eqF (ap1 Fst w) tagSu)
      fwSu = chainHeadSu_obj legS (hd_su ze#)
  in mp (succEqO_to_anything O Q) (ruleTrans (ruleSym fwSu) fwZe)
