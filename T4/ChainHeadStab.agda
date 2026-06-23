{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChainHeadStab -- HEAD-STABILITY over a TRANSPARENT reduction trace, the
-- piece that was the long-standing  HeadStab  gap (blocked while traces were
-- OPAQUE object Pars E-witnesses; UNBLOCKED now that the equational theory is
-- presented EXTENSIONALLY as transparent conversion traces -- Thierry / the
-- external-LLM trace-presentation route).
--
-- A transparent reduction trace  a =>* w  is a meta chain of single cert steps,
-- each step a  CertM  whose source matches:
--
--   data ChainM : Term -> Term -> Set where
--     cnil  : ChainM a a
--     ccons : (c : CertM) -> src(codeC c) = a -> ChainM (tgt(codeC c)) w -> ChainM a w
--
-- Head-stability is then ONE meta induction on the chain, applying the per-step
-- head preservation T4.CertHeadStab.certHeadZeM / certHeadSuM at each link:
--
--   chainHeadZe : ChainM a w -> hd a = tagZe -> hd w = tagZe
--   chainHeadSu : ChainM a w -> hd a = tagSu -> hd w = tagSu
--
-- These are the two object-Deriv facts that, applied to the two reduction legs
-- of a join, give the  ze# -vs- su#  clash (the heart of Con(T0)).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ChainHeadStab where

open import T4.Base

open import T4.CertTree     using ( CertM ; codeC )
open import T4.CertHeadStab using ( certHeadZeM ; certHeadSuM )
open import T4.ParEnds      using ( src ; tgt )
open import T4.TrsCodeObj   using ( hd ; tagZe ; tagSu )

------------------------------------------------------------------------
-- SECTION 1.  Transparent reduction traces (meta chain of cert steps).

-- The middle term  m  is explicit with Deriv equations  src(codeC c)=a ,
-- tgt(codeC c)=m , so a chain composes with code-indexed traces (the object
-- src/tgt are fold applications, not Agda-equal to  code _ ; carry them as
-- Deriv side-conditions, not Agda indices).
data ChainM : Term -> Term -> Set where
  cnil  : {a : Term} -> ChainM a a
  ccons : {a m w : Term} (c : CertM) ->
          Deriv (eqF (ap1 src (codeC c)) a) ->
          Deriv (eqF (ap1 tgt (codeC c)) m) ->
          ChainM m w ->
          ChainM a w

------------------------------------------------------------------------
-- SECTION 2.  Head-stability by one induction on the chain.

chainHeadZe : {a w : Term} -> ChainM a w ->
              Deriv (eqF (hd a) tagZe) -> Deriv (eqF (hd w) tagZe)
chainHeadZe cnil hyp = hyp
chainHeadZe (ccons c srcEq tgtEq rest) hyp =
  let hsrc : Deriv (eqF (hd (ap1 src (codeC c))) tagZe)
      hsrc = ruleTrans (cong1 Fst srcEq) hyp
      htgt : Deriv (eqF (hd (ap1 tgt (codeC c))) tagZe)
      htgt = certHeadZeM c hsrc
      hm : Deriv (eqF (hd _) tagZe)
      hm = ruleTrans (ruleSym (cong1 Fst tgtEq)) htgt
  in chainHeadZe rest hm

chainHeadSu : {a w : Term} -> ChainM a w ->
              Deriv (eqF (hd a) tagSu) -> Deriv (eqF (hd w) tagSu)
chainHeadSu cnil hyp = hyp
chainHeadSu (ccons c srcEq tgtEq rest) hyp =
  let hsrc : Deriv (eqF (hd (ap1 src (codeC c))) tagSu)
      hsrc = ruleTrans (cong1 Fst srcEq) hyp
      htgt : Deriv (eqF (hd (ap1 tgt (codeC c))) tagSu)
      htgt = certHeadSuM c hsrc
      hm : Deriv (eqF (hd _) tagSu)
      hm = ruleTrans (ruleSym (cong1 Fst tgtEq)) htgt
  in chainHeadSu rest hm
