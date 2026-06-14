{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChurchRosserProto -- FIRST MILESTONE for the §8 route of attempt3
-- (BRA |- Con(T0) via free-cut elimination + Church-Rosser).
--
-- This is the CR HALF, de-risked on a representative ORTHOGONAL recursor TRS:
--   constructors   ze , su        (= 0 , s)
--   one recursor   ad             (= addition, defined by recursion on arg 1)
--     ad ze     y  ->  y
--     ad (su x) y  ->  su (ad x y)
-- left-linear + non-overlapping = orthogonal.  We prove Church-Rosser by
-- PARALLEL REDUCTION with Takahashi's COMPLETE DEVELOPMENT (the triangle
-- lemma gives the diamond directly), then derive
--     ¬ (ze ≡ su ze)      ( = the consistency atom  0 ≢ s0 )
-- by constructor-stability.   TERMINATION IS NOT USED anywhere -- the same
-- proof scales to the full non-terminating Church R.
--
-- Self-contained (no imports), ASCII, --safe --without-K --exact-split.

module T4.ChurchRosserProto where

------------------------------------------------------------------------
-- Minimal prelude

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

Not : Set -> Set
Not A = A -> Empty

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

data And (A B : Set) : Set where
  mkAnd : A -> B -> And A B

andL : {A B : Set} -> And A B -> A
andL (mkAnd a _) = a

andR : {A B : Set} -> And A B -> B
andR (mkAnd _ b) = b

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl q = q

eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px

------------------------------------------------------------------------
-- Terms of the toy TRS

data Tm : Set where
  ze : Tm
  su : Tm -> Tm
  ad : Tm -> Tm -> Tm

------------------------------------------------------------------------
-- One-step reduction (root rules + congruence)

data Step : Tm -> Tm -> Set where
  rO  : (y : Tm)                              -> Step (ad ze y) y
  rS  : (x y : Tm)                            -> Step (ad (su x) y) (su (ad x y))
  cSu : {t t' : Tm}   -> Step t t'            -> Step (su t) (su t')
  cA1 : {a a' b : Tm} -> Step a a'            -> Step (ad a b) (ad a' b)
  cA2 : {a b b' : Tm} -> Step b b'            -> Step (ad a b) (ad a b')

-- Reflexive-transitive closure

data Steps : Tm -> Tm -> Set where
  done : {t : Tm}                                  -> Steps t t
  more : {t u v : Tm} -> Step t u -> Steps u v      -> Steps t v

stepsTrans : {t u v : Tm} -> Steps t u -> Steps u v -> Steps t v
stepsTrans done       ss2 = ss2
stepsTrans (more s ss) ss2 = more s (stepsTrans ss ss2)

stepsSu : {t t' : Tm} -> Steps t t' -> Steps (su t) (su t')
stepsSu done        = done
stepsSu (more s ss) = more (cSu s) (stepsSu ss)

stepsA1 : {a a' b : Tm} -> Steps a a' -> Steps (ad a b) (ad a' b)
stepsA1 done        = done
stepsA1 (more s ss) = more (cA1 s) (stepsA1 ss)

stepsA2 : {a b b' : Tm} -> Steps b b' -> Steps (ad a b) (ad a b')
stepsA2 done        = done
stepsA2 (more s ss) = more (cA2 s) (stepsA2 ss)

stepsA : {a a' b b' : Tm} -> Steps a a' -> Steps b b' -> Steps (ad a b) (ad a' b')
stepsA sa sb = stepsTrans (stepsA1 sa) (stepsA2 sb)

------------------------------------------------------------------------
-- Parallel reduction

data Par : Tm -> Tm -> Set where
  pZe : Par ze ze
  pSu : {t t' : Tm}            -> Par t t' -> Par (su t) (su t')
  pAd : {a a' b b' : Tm}       -> Par a a' -> Par b b' -> Par (ad a b) (ad a' b')
  pRO : {y y' : Tm}            -> Par y y' -> Par (ad ze y) y'
  pRS : {x x' y y' : Tm}       -> Par x x' -> Par y y' -> Par (ad (su x) y) (su (ad x' y'))

parRefl : (t : Tm) -> Par t t
parRefl ze       = pZe
parRefl (su t)   = pSu (parRefl t)
parRefl (ad a b) = pAd (parRefl a) (parRefl b)

-- Step  <=  Par  <=  Steps

stepPar : {t u : Tm} -> Step t u -> Par t u
stepPar (rO y)   = pRO (parRefl y)
stepPar (rS x y) = pRS (parRefl x) (parRefl y)
stepPar (cSu s)  = pSu (stepPar s)
stepPar (cA1 s)  = pAd (stepPar s) (parRefl _)
stepPar (cA2 s)  = pAd (parRefl _) (stepPar s)

parSteps : {t u : Tm} -> Par t u -> Steps t u
parSteps pZe              = done
parSteps (pSu p)          = stepsSu (parSteps p)
parSteps (pAd pa pb)      = stepsA (parSteps pa) (parSteps pb)
parSteps (pRO {y} p)      = more (rO y) (parSteps p)
parSteps (pRS {x}{x'}{y} px py) =
  more (rS x y) (stepsSu (stepsA (parSteps px) (parSteps py)))

------------------------------------------------------------------------
-- Complete development (Takahashi) and the triangle lemma

dev : Tm -> Tm
dev ze              = ze
dev (su t)          = su (dev t)
dev (ad ze y)       = dev y
dev (ad (su x) y)   = su (ad (dev x) (dev y))
dev (ad (ad p q) y) = ad (dev (ad p q)) (dev y)

-- For every parallel step  Par t u ,  u  parallel-reduces to  dev t .

tri : {t u : Tm} -> Par t u -> Par u (dev t)
tri pZe                      = pZe
tri (pSu p)                  = pSu (tri p)
tri (pAd pZe pb)             = pRO (tri pb)
tri (pAd (pSu px) pb)        = pRS (tri px) (tri pb)
tri (pAd (pAd pa1 pa2) pb)   = pAd (tri (pAd pa1 pa2)) (tri pb)
tri (pAd (pRO p) pb)         = pAd (tri (pRO p)) (tri pb)
tri (pAd (pRS px py) pb)     = pAd (tri (pRS px py)) (tri pb)
tri (pRO p)                  = tri p
tri (pRS px py)              = pSu (pAd (tri px) (tri py))

-- Diamond for Par, immediate from the triangle.

diamond : {t u1 u2 : Tm} -> Par t u1 -> Par t u2 ->
          Sigma Tm (\ w -> And (Par u1 w) (Par u2 w))
diamond {t} p1 p2 = mkSigma (dev t) (mkAnd (tri p1) (tri p2))

------------------------------------------------------------------------
-- Confluence of  Par*  (strip + tiling), hence of  Steps*

data Pars : Tm -> Tm -> Set where
  pdone : {t : Tm}                                  -> Pars t t
  pmore : {t u v : Tm} -> Par t u -> Pars u v        -> Pars t v

strip : {t u v : Tm} -> Par t u -> Pars t v ->
        Sigma Tm (\ w -> And (Pars u w) (Par v w))
strip {t}{u} p pdone = mkSigma u (mkAnd pdone p)
strip p (pmore q qs) =
  let d = diamond p q
      r = strip (andR (snd d)) qs
  in mkSigma (fst r) (mkAnd (pmore (andL (snd d)) (andL (snd r))) (andR (snd r)))

confl : {t v1 v2 : Tm} -> Pars t v1 -> Pars t v2 ->
        Sigma Tm (\ w -> And (Pars v1 w) (Pars v2 w))
confl {t}{v1}{v2} pdone qs = mkSigma v2 (mkAnd qs pdone)
confl (pmore p ps) qs =
  let s = strip p qs
      r = confl ps (andL (snd s))
  in mkSigma (fst r) (mkAnd (andL (snd r)) (pmore (andR (snd s)) (andR (snd r))))

stepsPars : {t u : Tm} -> Steps t u -> Pars t u
stepsPars done        = pdone
stepsPars (more s ss) = pmore (stepPar s) (stepsPars ss)

parsSteps : {t u : Tm} -> Pars t u -> Steps t u
parsSteps pdone        = done
parsSteps (pmore p ps) = stepsTrans (parSteps p) (parsSteps ps)

-- Church-Rosser for the toy TRS.

confluence : {t v1 v2 : Tm} -> Steps t v1 -> Steps t v2 ->
             Sigma Tm (\ w -> And (Steps v1 w) (Steps v2 w))
confluence s1 s2 =
  let r = confl (stepsPars s1) (stepsPars s2)
  in mkSigma (fst r) (mkAnd (parsSteps (andL (snd r))) (parsSteps (andR (snd r))))

------------------------------------------------------------------------
-- Constructor stability  ->  ze and su ze have no common reduct

zeStep : {u : Tm} -> Step ze u -> Empty
zeStep ()

zeSteps : {u : Tm} -> Steps ze u -> Eq ze u
zeSteps done        = refl
zeSteps (more s ss) = emptyElim (zeStep s)

-- Only  cSu  can reduce  su t , so the recursion is on a structural subterm.

suSteps : {t u : Tm} -> Steps (su t) u -> Sigma Tm (\ t' -> Eq u (su t'))
suSteps {t} done            = mkSigma t refl
suSteps (more (cSu s0) ss)  = suSteps ss

zeNeqSu : {t : Tm} -> Eq ze (su t) -> Empty
zeNeqSu ()

------------------------------------------------------------------------
-- Joinability, convertibility, and the consistency atom

Join : Tm -> Tm -> Set
Join t u = Sigma Tm (\ w -> And (Steps t w) (Steps u w))

joinSym : {t u : Tm} -> Join t u -> Join u t
joinSym (mkSigma w p) = mkSigma w (mkAnd (andR p) (andL p))

joinTrans : {t u v : Tm} -> Join t u -> Join u v -> Join t v
joinTrans (mkSigma w1 p1) (mkSigma w2 p2) =
  let c = confluence (andR p1) (andL p2)
  in mkSigma (fst c)
       (mkAnd (stepsTrans (andL p1) (andL (snd c)))
              (stepsTrans (andR p2) (andR (snd c))))

-- ze and su ze are not joinable.

zeNotJoinSuZe : Not (Join ze (su ze))
zeNotJoinSuZe (mkSigma w p) =
  zeNeqSu (eqTrans (zeSteps (andL p)) (snd (suSteps (andR p))))

-- Convertibility (the equivalence closure of Step) and the headline:
-- 0 ≢ s0 -- consistency of the toy equational theory.

data Conv : Tm -> Tm -> Set where
  cstep  : {t u : Tm}   -> Step t u                -> Conv t u
  crefl  : {t : Tm}                                -> Conv t t
  csym   : {t u : Tm}   -> Conv t u                -> Conv u t
  ctrans : {t u v : Tm} -> Conv t u -> Conv u v     -> Conv t v

-- Church-Rosser corollary: convertible terms are joinable.

convJoin : {t u : Tm} -> Conv t u -> Join t u
convJoin (cstep {t}{u} s) = mkSigma u (mkAnd (more s done) done)
convJoin (crefl {t})      = mkSigma t (mkAnd done done)
convJoin (csym c)         = joinSym (convJoin c)
convJoin (ctrans c1 c2)   = joinTrans (convJoin c1) (convJoin c2)

-- THE CONSISTENCY ATOM:  0 is not convertible to s 0.

zeNotConvSuZe : Not (Conv ze (su ze))
zeNotConvSuZe c = zeNotJoinSuZe (convJoin c)
