{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrFunValid -- DECIDABLE funcode validation, resolving the surjective-
-- pairing wall in the opaque triangle.  recon f reconstructs a funcode from its
-- head tag Fst f (the canonical form: cSuc/cZero/cId for Fun1 constants,
-- cComp(components) for C, cProj/cRec for Fun2); funValid f = eqDecO f (recon f)
-- is O iff f equals its reconstruction.  Then  funValid f = O  PROVIDES the
-- object reconstruction equation  f = cComp (Fst(Snd f)) ..  (via eqDecO_sound)
-- -- exactly what the opaque triangle's src_tri conjunct needs for a compound
-- carried fun, WITHOUT surjective pairing.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrFunValid where

open import T4.Base

open import T4.PrCodeObj using ( cSuc ; cZero ; cId ; cComp ; cProj ; cRec )
open import T4.PrDev using ( mkRec ; mkRec_val ; idxTest_fire ; idxTest_skip )
open import T4.PrSrc using ( mkComp ; mkComp_val )
open import T4.EqDecO using ( eqDecO ; eqDecO_sound )

open import BRA3.Church       using ( pi )
open import BRA3.PairAlgebra  using ( compose1U ; compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Component projections of a funcode and canonical branches.

projG : Fun1
projG = compose1U Fst Snd
projH1 : Fun1
projH1 = compose1U Fst (compose1U Snd Snd)
projH2 : Fun1
projH2 = compose1U Snd (compose1U Snd Snd)

cG : Term -> Term
cG f = ap1 Fst (ap1 Snd f)
cH1 : Term -> Term
cH1 f = ap1 Fst (ap1 Snd (ap1 Snd f))
cH2 : Term -> Term
cH2 f = ap1 Snd (ap1 Snd (ap1 Snd f))

projG_at : (f : Term) -> Deriv (eqF (ap1 projG f) (cG f))
projG_at f = compose1U_eq Fst Snd f
projH1_at : (f : Term) -> Deriv (eqF (ap1 projH1 f) (cH1 f))
projH1_at f = ruleTrans (compose1U_eq Fst (compose1U Snd Snd) f) (cong1 Fst (compose1U_eq Snd Snd f))
projH2_at : (f : Term) -> Deriv (eqF (ap1 projH2 f) (cH2 f))
projH2_at f = ruleTrans (compose1U_eq Snd (compose1U Snd Snd) f) (cong1 Snd (compose1U_eq Snd Snd f))

cSucBr cZeroBr cIdBr cProjBr cCompBr cRecBr junkBr : Fun1
cSucBr  = C pi (constN 3) Z
cZeroBr = C pi (constN 4) Z
cIdBr   = C pi (constN 5) Z
cProjBr = C pi (constN 7) Z
cCompBr = mkComp projG projH1 projH2
cRecBr  = mkRec projG projH1 projH2
junkBr  = constN 0

constBr_val : (k : Nat) (f : Term) ->
  Deriv (eqF (ap1 (C pi (constN k) Z) f) (ap2 Pair (natCode k) O))
constBr_val k f =
  ruleTrans (ax_C pi (constN k) Z f)
    (ruleTrans (congL pi (ap1 Z f) (constN_eq k f)) (congR pi (natCode k) (axZ f)))

cCompBr_val : (f : Term) -> Deriv (eqF (ap1 cCompBr f) (cComp (cG f) (cH1 f) (cH2 f)))
cCompBr_val f = mkComp_val projG projH1 projH2 f (cG f) (cH1 f) (cH2 f) (projG_at f) (projH1_at f) (projH2_at f)
cRecBr_val : (f : Term) -> Deriv (eqF (ap1 cRecBr f) (cRec (cG f) (cH1 f) (cH2 f)))
cRecBr_val f = mkRec_val projG projH1 projH2 f (cG f) (cH1 f) (cH2 f) (projG_at f) (projH1_at f) (projH2_at f)

------------------------------------------------------------------------
-- SECTION 1.  recon : reconstruct a funcode from Fst f.

testHd : Nat -> Fun1
testHd k = C natEqF Fst (constN k)

rec_l8 rec_l7 rec_l6 rec_l5 rec_l4 recon : Fun1
rec_l8 = C condFork (C pi cRecBr junkBr) (testHd 8)
rec_l7 = C condFork (C pi cProjBr rec_l8) (testHd 7)
rec_l6 = C condFork (C pi cCompBr rec_l7) (testHd 6)
rec_l5 = C condFork (C pi cIdBr rec_l6) (testHd 5)
rec_l4 = C condFork (C pi cZeroBr rec_l5) (testHd 4)
recon  = C condFork (C pi cSucBr rec_l4) (testHd 3)

private
  wn : (m k : Nat) -> ((Eq m k) -> Empty) -> NatNeqWitness m k
  wn m k p = decideNatNeq m k p

open import T4.DerSrc using ( fork_true_to_fst ; fork_false_to_snd )

------------------------------------------------------------------------
-- SECTION 2.  recon equations (dispatch on Fst f).

recon_s : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 3)) -> Deriv (eqF (ap1 recon f) cSuc)
recon_s f h3 =
  ruleTrans (fork_true_to_fst cSucBr rec_l4 (testHd 3) f (idxTest_fire Fst 3 f h3))
            (constBr_val 3 f)

recon_o : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 4)) -> Deriv (eqF (ap1 recon f) cZero)
recon_o f h4 =
  ruleTrans (fork_false_to_snd cSucBr rec_l4 (testHd 3) f (idxTest_skip Fst 4 3 f (wn 4 3 (\ ())) h4))
            (ruleTrans (fork_true_to_fst cZeroBr rec_l5 (testHd 4) f (idxTest_fire Fst 4 f h4))
                       (constBr_val 4 f))

recon_u : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 5)) -> Deriv (eqF (ap1 recon f) cId)
recon_u f h5 =
  ruleTrans (fork_false_to_snd cSucBr rec_l4 (testHd 3) f (idxTest_skip Fst 5 3 f (wn 5 3 (\ ())) h5))
    (ruleTrans (fork_false_to_snd cZeroBr rec_l5 (testHd 4) f (idxTest_skip Fst 5 4 f (wn 5 4 (\ ())) h5))
      (ruleTrans (fork_true_to_fst cIdBr rec_l6 (testHd 5) f (idxTest_fire Fst 5 f h5))
                 (constBr_val 5 f)))

recon_C : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 6)) ->
  Deriv (eqF (ap1 recon f) (cComp (cG f) (cH1 f) (cH2 f)))
recon_C f h6 =
  ruleTrans (fork_false_to_snd cSucBr rec_l4 (testHd 3) f (idxTest_skip Fst 6 3 f (wn 6 3 (\ ())) h6))
    (ruleTrans (fork_false_to_snd cZeroBr rec_l5 (testHd 4) f (idxTest_skip Fst 6 4 f (wn 6 4 (\ ())) h6))
      (ruleTrans (fork_false_to_snd cIdBr rec_l6 (testHd 5) f (idxTest_skip Fst 6 5 f (wn 6 5 (\ ())) h6))
        (ruleTrans (fork_true_to_fst cCompBr rec_l7 (testHd 6) f (idxTest_fire Fst 6 f h6))
                   (cCompBr_val f))))

recon_v : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 7)) -> Deriv (eqF (ap1 recon f) cProj)
recon_v f h7 =
  ruleTrans (fork_false_to_snd cSucBr rec_l4 (testHd 3) f (idxTest_skip Fst 7 3 f (wn 7 3 (\ ())) h7))
    (ruleTrans (fork_false_to_snd cZeroBr rec_l5 (testHd 4) f (idxTest_skip Fst 7 4 f (wn 7 4 (\ ())) h7))
      (ruleTrans (fork_false_to_snd cIdBr rec_l6 (testHd 5) f (idxTest_skip Fst 7 5 f (wn 7 5 (\ ())) h7))
        (ruleTrans (fork_false_to_snd cCompBr rec_l7 (testHd 6) f (idxTest_skip Fst 7 6 f (wn 7 6 (\ ())) h7))
          (ruleTrans (fork_true_to_fst cProjBr rec_l8 (testHd 7) f (idxTest_fire Fst 7 f h7))
                     (constBr_val 7 f)))))

recon_R : (f : Term) -> Deriv (eqF (ap1 Fst f) (natCode 8)) ->
  Deriv (eqF (ap1 recon f) (cRec (cG f) (cH1 f) (cH2 f)))
recon_R f h8 =
  ruleTrans (fork_false_to_snd cSucBr rec_l4 (testHd 3) f (idxTest_skip Fst 8 3 f (wn 8 3 (\ ())) h8))
    (ruleTrans (fork_false_to_snd cZeroBr rec_l5 (testHd 4) f (idxTest_skip Fst 8 4 f (wn 8 4 (\ ())) h8))
      (ruleTrans (fork_false_to_snd cIdBr rec_l6 (testHd 5) f (idxTest_skip Fst 8 5 f (wn 8 5 (\ ())) h8))
        (ruleTrans (fork_false_to_snd cCompBr rec_l7 (testHd 6) f (idxTest_skip Fst 8 6 f (wn 8 6 (\ ())) h8))
          (ruleTrans (fork_false_to_snd cProjBr rec_l8 (testHd 7) f (idxTest_skip Fst 8 7 f (wn 8 7 (\ ())) h8))
            (ruleTrans (fork_true_to_fst cRecBr junkBr (testHd 8) f (idxTest_fire Fst 8 f h8))
                       (cRecBr_val f))))))

------------------------------------------------------------------------
-- SECTION 3.  funValid and the reconstruction lemmas.

funValid : Term -> Term
funValid f = eqDecO f (ap1 recon f)

-- funValid f = O  =>  f = recon f .
funValid_to_recon : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF f (ap1 recon f))
funValid_to_recon f fv = eqDecO_sound f (ap1 recon f) fv

funValid_s : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF (ap1 Fst f) (natCode 3)) -> Deriv (eqF f cSuc)
funValid_s f fv h = ruleTrans (funValid_to_recon f fv) (recon_s f h)
funValid_o : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF (ap1 Fst f) (natCode 4)) -> Deriv (eqF f cZero)
funValid_o f fv h = ruleTrans (funValid_to_recon f fv) (recon_o f h)
funValid_u : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF (ap1 Fst f) (natCode 5)) -> Deriv (eqF f cId)
funValid_u f fv h = ruleTrans (funValid_to_recon f fv) (recon_u f h)
funValid_C : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF (ap1 Fst f) (natCode 6)) ->
  Deriv (eqF f (cComp (cG f) (cH1 f) (cH2 f)))
funValid_C f fv h = ruleTrans (funValid_to_recon f fv) (recon_C f h)
funValid_v : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF (ap1 Fst f) (natCode 7)) -> Deriv (eqF f cProj)
funValid_v f fv h = ruleTrans (funValid_to_recon f fv) (recon_v f h)
funValid_R : (f : Term) -> Deriv (eqF (funValid f) O) -> Deriv (eqF (ap1 Fst f) (natCode 8)) ->
  Deriv (eqF f (cRec (cG f) (cH1 f) (cH2 f)))
funValid_R f fv h = ruleTrans (funValid_to_recon f fv) (recon_R f h)
