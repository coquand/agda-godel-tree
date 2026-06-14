{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChurchRosserBRA -- STEP (2) of attempt3: the meta Church-Rosser proof
-- ported from the toy TRS to CHURCH'S ACTUAL recursor signature (BRA3 Term /
-- Fun1 / Fun2), the 6 computation rules (axioms 1,2,3,8,9,10):
--
--   (1) a1 o t                  -> kO
--   (2) a1 u t                  -> t
--   (3) a2 v a b                -> b
--   (4) a1 (C g h1 h2) t        -> a2 g (a1 h1 t) (a1 h2 t)
--   (5) a2 (R g h1 h2) x kO     -> a1 g x
--   (6) a2 (R g h1 h2) x (s n)  -> a2 h1 (a2 h2 x n) (a2 (R g h1 h2) x n)
--
-- Constructors with NO rule: kO, var, s.  The system is ORTHOGONAL (left-linear
-- + non-overlapping; attempt3 §12), so it is CONFLUENT WITHOUT TERMINATION.
-- We prove that here by parallel reduction + Takahashi complete development,
-- and derive the consistency atom  ¬ (kO ≡ a1 s kO)   ( = 0 ≢ s0 ).
--
-- Self-contained (own copies of Term/Fun1/Fun2), ASCII, --safe --without-K
-- --exact-split, no holes / no postulates.

module T4.ChurchRosserBRA where

------------------------------------------------------------------------
-- Minimal prelude

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

Not : Set -> Set
Not A = A -> Empty

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

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

------------------------------------------------------------------------
-- Church's term language (mirror of BRA3.Term)

data Fun1 : Set
data Fun2 : Set
data Tm   : Set

data Fun1 where
  fs : Fun1                          -- successor (constructor: no rule)
  fo : Fun1                          -- zero functor   (rule 1)
  fu : Fun1                          -- identity       (rule 2)
  fC : Fun2 -> Fun1 -> Fun1 -> Fun1  -- composition     (rule 4)

data Fun2 where
  fv : Fun2                          -- second projection (rule 3)
  fR : Fun1 -> Fun2 -> Fun2 -> Fun2  -- primitive recursion (rules 5,6)

data Tm where
  kO  : Tm
  var : Nat -> Tm
  a1  : Fun1 -> Tm -> Tm
  a2  : Fun2 -> Tm -> Tm -> Tm

------------------------------------------------------------------------
-- One-step reduction

data Step : Tm -> Tm -> Set where
  sO  : (t : Tm)                                  -> Step (a1 fo t) kO
  sU  : (t : Tm)                                  -> Step (a1 fu t) t
  sV  : (a b : Tm)                                -> Step (a2 fv a b) b
  sC  : (g : Fun2) (h1 h2 : Fun1) (t : Tm)        -> Step (a1 (fC g h1 h2) t) (a2 g (a1 h1 t) (a1 h2 t))
  sRb : (g : Fun1) (h1 h2 : Fun2) (x : Tm)        -> Step (a2 (fR g h1 h2) x kO) (a1 g x)
  sRs : (g : Fun1) (h1 h2 : Fun2) (x n : Tm)      -> Step (a2 (fR g h1 h2) x (a1 fs n))
                                                          (a2 h1 (a2 h2 x n) (a2 (fR g h1 h2) x n))
  c1  : {f : Fun1} {t t' : Tm}   -> Step t t'      -> Step (a1 f t) (a1 f t')
  c2L : {g : Fun2} {a a' b : Tm} -> Step a a'      -> Step (a2 g a b) (a2 g a' b)
  c2R : {g : Fun2} {a b b' : Tm} -> Step b b'      -> Step (a2 g a b) (a2 g a b')

data Steps : Tm -> Tm -> Set where
  done : {t : Tm}                                  -> Steps t t
  more : {t u v : Tm} -> Step t u -> Steps u v      -> Steps t v

stepsTrans : {t u v : Tm} -> Steps t u -> Steps u v -> Steps t v
stepsTrans done        ss2 = ss2
stepsTrans (more s ss)  ss2 = more s (stepsTrans ss ss2)

stepsC1 : {f : Fun1} {t t' : Tm} -> Steps t t' -> Steps (a1 f t) (a1 f t')
stepsC1 done        = done
stepsC1 (more s ss) = more (c1 s) (stepsC1 ss)

stepsC2L : {g : Fun2} {a a' b : Tm} -> Steps a a' -> Steps (a2 g a b) (a2 g a' b)
stepsC2L done        = done
stepsC2L (more s ss) = more (c2L s) (stepsC2L ss)

stepsC2R : {g : Fun2} {a b b' : Tm} -> Steps b b' -> Steps (a2 g a b) (a2 g a b')
stepsC2R done        = done
stepsC2R (more s ss) = more (c2R s) (stepsC2R ss)

stepsC2 : {g : Fun2} {a a' b b' : Tm} -> Steps a a' -> Steps b b' -> Steps (a2 g a b) (a2 g a' b')
stepsC2 sa sb = stepsTrans (stepsC2L sa) (stepsC2R sb)

------------------------------------------------------------------------
-- Parallel reduction

data Par : Tm -> Tm -> Set where
  pO   : Par kO kO
  pV   : (k : Nat) -> Par (var k) (var k)
  p1   : {f : Fun1} {t t' : Tm}      -> Par t t' -> Par (a1 f t) (a1 f t')
  p2   : {g : Fun2} {a a' b b' : Tm} -> Par a a' -> Par b b' -> Par (a2 g a b) (a2 g a' b')
  pRO  : (t : Tm)                     -> Par (a1 fo t) kO
  pRU  : {t t' : Tm}                  -> Par t t' -> Par (a1 fu t) t'
  pRV  : {a b b' : Tm}                -> Par b b' -> Par (a2 fv a b) b'
  pRC  : {g : Fun2} {h1 h2 : Fun1} {t t' : Tm} ->
         Par t t' -> Par (a1 (fC g h1 h2) t) (a2 g (a1 h1 t') (a1 h2 t'))
  pRRb : {g : Fun1} {h1 h2 : Fun2} {x x' : Tm} ->
         Par x x' -> Par (a2 (fR g h1 h2) x kO) (a1 g x')
  pRRs : {g : Fun1} {h1 h2 : Fun2} {x x' n n' : Tm} ->
         Par x x' -> Par n n' ->
         Par (a2 (fR g h1 h2) x (a1 fs n))
             (a2 h1 (a2 h2 x' n') (a2 (fR g h1 h2) x' n'))

parRefl : (t : Tm) -> Par t t
parRefl kO          = pO
parRefl (var k)     = pV k
parRefl (a1 f t)    = p1 (parRefl t)
parRefl (a2 g a b)  = p2 (parRefl a) (parRefl b)

stepPar : {t u : Tm} -> Step t u -> Par t u
stepPar (sO t)        = pRO t
stepPar (sU t)        = pRU (parRefl t)
stepPar (sV a b)      = pRV (parRefl b)
stepPar (sC g h1 h2 t) = pRC (parRefl t)
stepPar (sRb g h1 h2 x) = pRRb (parRefl x)
stepPar (sRs g h1 h2 x n) = pRRs (parRefl x) (parRefl n)
stepPar (c1 s)        = p1 (stepPar s)
stepPar (c2L s)       = p2 (stepPar s) (parRefl _)
stepPar (c2R s)       = p2 (parRefl _) (stepPar s)

parSteps : {t u : Tm} -> Par t u -> Steps t u
parSteps pO              = done
parSteps (pV k)          = done
parSteps (p1 p)          = stepsC1 (parSteps p)
parSteps (p2 pa pb)      = stepsC2 (parSteps pa) (parSteps pb)
parSteps (pRO t)         = more (sO t) done
parSteps (pRU {t} p)     = more (sU t) (parSteps p)
parSteps (pRV {a}{b} p)  = more (sV a b) (parSteps p)
parSteps (pRC {g}{h1}{h2}{t} p) =
  more (sC g h1 h2 t) (stepsC2 (stepsC1 (parSteps p)) (stepsC1 (parSteps p)))
parSteps (pRRb {g}{h1}{h2}{x} p) =
  more (sRb g h1 h2 x) (stepsC1 (parSteps p))
parSteps (pRRs {g}{h1}{h2}{x}{x'}{n} px pn) =
  more (sRs g h1 h2 x n)
       (stepsC2 (stepsC2 (parSteps px) (parSteps pn))
                (stepsC2 (parSteps px) (parSteps pn)))

------------------------------------------------------------------------
-- Complete development (Takahashi)

dev : Tm -> Tm
dev kO                              = kO
dev (var k)                         = var k
dev (a1 fs t)                       = a1 fs (dev t)
dev (a1 fo t)                       = kO
dev (a1 fu t)                       = dev t
dev (a1 (fC g h1 h2) t)             = a2 g (a1 h1 (dev t)) (a1 h2 (dev t))
dev (a2 fv a b)                     = dev b
dev (a2 (fR g h1 h2) x kO)          = a1 g (dev x)
dev (a2 (fR g h1 h2) x (a1 fs n))   = a2 h1 (a2 h2 (dev x) (dev n)) (a2 (fR g h1 h2) (dev x) (dev n))
dev (a2 (fR g h1 h2) x (var k))     = a2 (fR g h1 h2) (dev x) (var k)
dev (a2 (fR g h1 h2) x (a1 fo n))   = a2 (fR g h1 h2) (dev x) (dev (a1 fo n))
dev (a2 (fR g h1 h2) x (a1 fu n))   = a2 (fR g h1 h2) (dev x) (dev (a1 fu n))
dev (a2 (fR g h1 h2) x (a1 (fC g' k1 k2) n)) = a2 (fR g h1 h2) (dev x) (dev (a1 (fC g' k1 k2) n))
dev (a2 (fR g h1 h2) x (a2 g' a b)) = a2 (fR g h1 h2) (dev x) (dev (a2 g' a b))

------------------------------------------------------------------------
-- The triangle:  Par t u  ->  Par u (dev t)

tri : {t u : Tm} -> Par t u -> Par u (dev t)
tri pO                       = pO
tri (pV k)                   = pV k
-- p1 : split on the Fun1 head
tri (p1 {fs} p)              = p1 (tri p)
tri (p1 {fo} p)              = pRO _
tri (p1 {fu} p)              = pRU (tri p)
tri (p1 {fC g h1 h2} p)      = pRC (tri p)
-- p2 with head v : dev = dev b
tri (p2 {fv} pa pb)          = pRV (tri pb)
-- p2 with head R : split on the second-argument reduction pb
tri (p2 {fR g h1 h2} pa pO)              = pRRb (tri pa)
tri (p2 {fR g h1 h2} pa (p1 {fs} pn))    = pRRs (tri pa) (tri pn)
tri (p2 {fR g h1 h2} pa (pV k))          = p2 (tri pa) (tri (pV k))
tri (p2 {fR g h1 h2} pa (p1 {fo} pn))    = p2 (tri pa) (tri (p1 {fo} pn))
tri (p2 {fR g h1 h2} pa (p1 {fu} pn))    = p2 (tri pa) (tri (p1 {fu} pn))
tri (p2 {fR g h1 h2} pa (p1 {fC g' k1 k2} pn)) = p2 (tri pa) (tri (p1 {fC g' k1 k2} pn))
tri (p2 {fR g h1 h2} pa (p2 {g'} pq1 pq2)) = p2 (tri pa) (tri (p2 {g'} pq1 pq2))
tri (p2 {fR g h1 h2} pa (pRO n))         = p2 (tri pa) (tri (pRO n))
tri (p2 {fR g h1 h2} pa (pRU pn))        = p2 (tri pa) (tri (pRU pn))
tri (p2 {fR g h1 h2} pa (pRV {a0} pn))   = p2 (tri pa) (tri (pRV {a0} pn))
tri (p2 {fR g h1 h2} pa (pRC pn))        = p2 (tri pa) (tri (pRC pn))
tri (p2 {fR g h1 h2} pa (pRRb {g'}{j1}{j2} pn)) = p2 (tri pa) (tri (pRRb {g'}{j1}{j2} pn))
tri (p2 {fR g h1 h2} pa (pRRs px pn))    = p2 (tri pa) (tri (pRRs px pn))
-- root reductions
tri (pRO t)                  = pO
tri (pRU p)                  = tri p
tri (pRV p)                  = tri p
tri (pRC {g}{h1}{h2} p)      = p2 {g} (p1 {h1} (tri p)) (p1 {h2} (tri p))
tri (pRRb p)                 = p1 (tri p)
tri (pRRs {g}{h1}{h2} px pn) = p2 {h1} (p2 {h2} (tri px) (tri pn)) (p2 {fR g h1 h2} (tri px) (tri pn))

diamond : {t u1 u2 : Tm} -> Par t u1 -> Par t u2 ->
          Sigma Tm (\ w -> And (Par u1 w) (Par u2 w))
diamond {t} p1d p2d = mkSigma (dev t) (mkAnd (tri p1d) (tri p2d))

------------------------------------------------------------------------
-- Confluence of Par* (strip + tiling), hence of Steps*

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

-- Church-Rosser for Church's recursor TRS.

confluence : {t v1 v2 : Tm} -> Steps t v1 -> Steps t v2 ->
             Sigma Tm (\ w -> And (Steps v1 w) (Steps v2 w))
confluence s1 s2 =
  let r = confl (stepsPars s1) (stepsPars s2)
  in mkSigma (fst r) (mkAnd (parsSteps (andL (snd r))) (parsSteps (andR (snd r))))

------------------------------------------------------------------------
-- Constructor stability  ->  kO and  a1 fs kO  ( = 0 and s0 )  not joinable

-- No rule reduces kO (every Step LHS is a1/a2-headed).
oStep : {u : Tm} -> Step kO u -> Empty
oStep ()

oSteps : {u : Tm} -> Steps kO u -> Eq kO u
oSteps done        = refl
oSteps (more s ss) = emptyElim (oStep s)

-- s has NO root rule, so only c1 reduces  a1 fs t .
sSteps : {t u : Tm} -> Steps (a1 fs t) u -> Sigma Tm (\ t' -> Eq u (a1 fs t'))
sSteps {t} done             = mkSigma t refl
sSteps (more (c1 s0) ss)    = sSteps ss

oNeqS : {t : Tm} -> Eq kO (a1 fs t) -> Empty
oNeqS ()

------------------------------------------------------------------------
-- Joinability, convertibility, and the consistency atom  0 ≢ s0

Join : Tm -> Tm -> Set
Join t u = Sigma Tm (\ w -> And (Steps t w) (Steps u w))

joinSym : {t u : Tm} -> Join t u -> Join u t
joinSym (mkSigma w p) = mkSigma w (mkAnd (andR p) (andL p))

joinTrans : {t u v : Tm} -> Join t u -> Join u v -> Join t v
joinTrans (mkSigma w1 p1j) (mkSigma w2 p2j) =
  let c = confluence (andR p1j) (andL p2j)
  in mkSigma (fst c)
       (mkAnd (stepsTrans (andL p1j) (andL (snd c)))
              (stepsTrans (andR p2j) (andR (snd c))))

oNotJoinSO : Not (Join kO (a1 fs kO))
oNotJoinSO (mkSigma w p) =
  oNeqS (eqTrans (oSteps (andL p)) (snd (sSteps (andR p))))

data Conv : Tm -> Tm -> Set where
  cstep  : {t u : Tm}   -> Step t u                -> Conv t u
  crefl  : {t : Tm}                                -> Conv t t
  csym   : {t u : Tm}   -> Conv t u                -> Conv u t
  ctrans : {t u v : Tm} -> Conv t u -> Conv u v     -> Conv t v

convJoin : {t u : Tm} -> Conv t u -> Join t u
convJoin (cstep {t}{u} s) = mkSigma u (mkAnd (more s done) done)
convJoin (crefl {t})      = mkSigma t (mkAnd done done)
convJoin (csym c)         = joinSym (convJoin c)
convJoin (ctrans c1c c2c) = joinTrans (convJoin c1c) (convJoin c2c)

-- THE CONSISTENCY ATOM for Church's recursor theory:  0 is not convertible s0.

oNotConvSO : Not (Conv kO (a1 fs kO))
oNotConvSO c = oNotJoinSO (convJoin c)
