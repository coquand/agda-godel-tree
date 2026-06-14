{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParHeadline -- STAGE 4b (deliverable 2d): the HEADLINE consistency atom
--     0 != s0     ( zeNotConvSuZe : Not (Conv ze (su ze)) )
-- the meta object analog of  ChurchRosserProto.zeNotConvSuZe .
--
-- This is the Church-Rosser COROLLARY: convertible terms are joinable
-- (convJoin, via T4.ParConfl.confluence), and  ze / su ze  are NOT joinable
-- (constructor clash: ze reduces only to ze, su ze only to su _, and ze != su _).
-- Replays the proto's headline section clause-for-clause over the META
-- StepsM / ParM developed in T4.ParConfl; TERMINATION IS NOT USED.
--
-- NB.  This is the META consistency of the toy equational theory.  Promoting
-- it to an OBJECT  Deriv -level non-convertibility (BRA |- Con(T0)) is the
-- (b)/(c) soundness bridge of attempt3 §10-§12 (object certificates from
-- T4.ParCertOf.certOf + the coded convertibility predicate), still ahead.

module T4.ParHeadline where

open import T4.ParReflPres using ( Tm ; ze ; su )
open import T4.ParStep     using ( StepM ; stSu )
open import T4.ParConfl    using
  ( Sg ; mkSg ; car ; prf ; Conj ; mkConj ; prjL ; prjR
  ; StepsM ; doneS ; moreS ; stepsTransM ; confluence )

------------------------------------------------------------------------
-- Minimal meta prelude (empty, negation, propositional equality).

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

Not : Set -> Set
Not A = A -> Empty

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl q = q

------------------------------------------------------------------------
-- Constructor stability:  ze and su _ reduce only to their own shapes.

zeStep : {u : Tm} -> StepM ze u -> Empty
zeStep ()

zeSteps : {u : Tm} -> StepsM ze u -> Eq ze u
zeSteps doneS         = refl
zeSteps (moreS st ss) = emptyElim (zeStep st)

-- Only  stSu  can reduce  su t , so the recursion is on a structural subterm.

suSteps : {t u : Tm} -> StepsM (su t) u -> Sg (\ t' -> Eq u (su t'))
suSteps {t} doneS             = mkSg t refl
suSteps (moreS (stSu st0) ss) = suSteps ss

zeNeqSu : {t : Tm} -> Eq ze (su t) -> Empty
zeNeqSu ()

------------------------------------------------------------------------
-- Joinability and convertibility.

Join : Tm -> Tm -> Set
Join t u = Sg (\ w -> Conj (StepsM t w) (StepsM u w))

joinSym : {t u : Tm} -> Join t u -> Join u t
joinSym (mkSg w p) = mkSg w (mkConj (prjR p) (prjL p))

joinTrans : {t u v : Tm} -> Join t u -> Join u v -> Join t v
joinTrans (mkSg w1 p1) (mkSg w2 p2) =
  let c = confluence (prjR p1) (prjL p2)
  in mkSg (car c)
       (mkConj (stepsTransM (prjL p1) (prjL (prf c)))
               (stepsTransM (prjR p2) (prjR (prf c))))

-- ze and su ze are not joinable.

zeNotJoinSuZe : Not (Join ze (su ze))
zeNotJoinSuZe (mkSg w p) =
  zeNeqSu (eqTrans (zeSteps (prjL p)) (prf (suSteps (prjR p))))

------------------------------------------------------------------------
-- Convertibility (equivalence closure of single-step reduction) and the
-- Church-Rosser corollary  convJoin , giving the headline.

data Conv : Tm -> Tm -> Set where
  cstep  : {t u : Tm}   -> StepM t u            -> Conv t u
  crefl  : {t : Tm}                             -> Conv t t
  csym   : {t u : Tm}   -> Conv t u             -> Conv u t
  ctrans : {t u v : Tm} -> Conv t u -> Conv u v -> Conv t v

convJoin : {t u : Tm} -> Conv t u -> Join t u
convJoin (cstep {t} {u} st) = mkSg u (mkConj (moreS st doneS) doneS)
convJoin (crefl {t})        = mkSg t (mkConj doneS doneS)
convJoin (csym c)           = joinSym (convJoin c)
convJoin (ctrans c1 c2)     = joinTrans (convJoin c1) (convJoin c2)

-- THE CONSISTENCY ATOM:  0 is not convertible to s 0.

zeNotConvSuZe : Not (Conv ze (su ze))
zeNotConvSuZe c = zeNotJoinSuZe (convJoin c)
