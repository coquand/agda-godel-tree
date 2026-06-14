{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ConvInterface -- the CR-terminal -> LOGIC-terminal INTERFACE: the three
-- convertibility lemmas the logical half (G3/cut-elimination, attempt3 §13)
-- needs from the atomic/Church-Rosser half to prove (EqSound)/(Cons).  All meta,
-- over the toy convertibility  Conv  (T4.ParHeadline), via confluence.
--
--   L1  Conv-congruence            convSu / convAd      (re-exported from EqSound)
--   L2  Conv-s-injectivity         convSuInj : Conv (su a)(su b) -> Conv a b
--   L3  uniform constructor clash  zeNotConvSuT : (t) -> Not (Conv ze (su t))
--
-- L2 and L3 are the eval-free soundness facts for the equality axioms
-- (attempt3 lines 314-318):  s injective  and  s x != 0  hold under  ≡
-- BECAUSE of confluence + constructor distinctness, NOT by evaluation.

module T4.ConvInterface where

open import T4.ParReflPres using ( Tm ; ze ; su ; ad )
open import T4.ParStep     using ( StepM ; stSu )
open import T4.ParConfl    using
  ( Sg ; mkSg ; car ; prf ; Conj ; mkConj ; prjL ; prjR
  ; StepsM ; doneS ; moreS )
open import T4.ParHeadline using
  ( Empty ; Not ; Eq ; refl ; eqTrans ; Join
  ; Conv ; cstep ; crefl ; csym ; ctrans ; convJoin
  ; zeSteps ; suSteps ; zeNeqSu )

-- L1: Conv-congruence is already proved in T4.EqSound; re-export.
open import T4.EqSound public using ( convSu ; convAd1 ; convAd2 ; convAd )

------------------------------------------------------------------------
-- Small meta-equality helpers.

eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
eqSym refl = refl

suInjEq : {a b : Tm} -> Eq (su a) (su b) -> Eq a b
suInjEq refl = refl

------------------------------------------------------------------------
-- Reduction sequences embed into convertibility.

stepsConv : {t u : Tm} -> StepsM t u -> Conv t u
stepsConv doneS         = crefl
stepsConv (moreS st ss) = ctrans (cstep st) (stepsConv ss)

------------------------------------------------------------------------
-- Head-stability for su WITH the inner reduction:  a reduct of  su t  is
-- some  su t'  with  t reducing to t' .

suStepsInner : {t u : Tm} ->
  StepsM (su t) u -> Sg (\ t' -> Conj (Eq u (su t')) (StepsM t t'))
suStepsInner {t} doneS = mkSg t (mkConj refl doneS)
suStepsInner (moreS (stSu st0) ss) =
  let r = suStepsInner ss
  in mkSg (car r) (mkConj (prjL (prf r)) (moreS st0 (prjR (prf r))))

------------------------------------------------------------------------
-- L2:  Conv-s-injectivity.  If  su a ≡ su b  then (confluence) they share a
-- reduct  su c , whence  a ≡ c ≡ b , i.e.  a ≡ b .

combineSuInj : {a b a' b' : Tm} ->
  Eq a' b' -> StepsM a a' -> StepsM b b' -> Conv a b
combineSuInj refl sa sb = ctrans (stepsConv sa) (csym (stepsConv sb))

convSuInj : {a b : Tm} -> Conv (su a) (su b) -> Conv a b
convSuInj c =
  let j  = convJoin c
      ra = suStepsInner (prjL (prf j))
      rb = suStepsInner (prjR (prf j))
      eqcc : Eq (su (car ra)) (su (car rb))
      eqcc = eqTrans (eqSym (prjL (prf ra))) (prjL (prf rb))
  in combineSuInj (suInjEq eqcc) (prjR (prf ra)) (prjR (prf rb))

------------------------------------------------------------------------
-- L3:  uniform constructor clash.   ze and  su t  share no reduct (ze reduces
-- only to ze, su t only to su _, and ze != su _), so are never convertible.

zeNotJoinSuT : (t : Tm) -> Not (Join ze (su t))
zeNotJoinSuT t (mkSg w p) =
  zeNeqSu (eqTrans (zeSteps (prjL p)) (prf (suSteps (prjR p))))

zeNotConvSuT : (t : Tm) -> Not (Conv ze (su t))
zeNotConvSuT t c = zeNotJoinSuT t (convJoin c)
