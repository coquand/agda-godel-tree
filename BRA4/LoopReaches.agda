{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.LoopReaches -- Abstract module for the mu-loop's halting trace with
-- variable-fuel composition.  Parametric in the hit-detector  p , the
-- first-hit position  z  (a Term), and the firstness pair  (dHit, dBelow) .
--
-- Provides:
--   * SECTION 1:  pFlip = isZero . p  with pFlip_at_hit / pFlip_below
--   * SECTION 2:  re-export of FirstHit.Search at  p
--   * SECTION 3:  TReaches infrastructure for Term-fueled aggregation:
--     - ClosedAtVar k record + closure lemmas (cav_O, cav_ap1, cav_ap2,
--       cav_var, cav_natCode)
--     - sigma_at_O_univ / sigma_at_succ_univ (Closed-free)
--     - iter_add_term : iter f c (sigma b a) = iter f (iter f c b) a
--     - TReaches record + refl / step1 / eq_target / from_reach / trans
--
-- The Term-fueled aggregation handles the Σ m(i) sum over scan iterations
-- where per-iteration meta-Nat fuel m(i) varies with i (the case for our
-- R-recursive predicate hitKdef Lstar (outKdef Lstar)).
--
-- The main simulation theorem (Section 4 = MuSimulation.muSimulation_correct)
-- lives in BRA4/MuSimulation.agda.

module BRA4.LoopReaches where

open import BRA4.Base
open import BRA4.EvalU
  using ( mcode1 ; mcodeMu )
open import BRA4.EvalUStep using ( stepU )
open import BRA4.EvalUCorrect
  using ( Reaches ; mkReach ; reach_step1 ; reach_trans ; reach_eq_target
        ; steps ; runs )
open import BRA4.FirstHit using ( module Search )

open import BRA3.Church          using
  ( isZero ; TisZeroZ ; TisZeroSucc ; sigma ; s2 ; T34 )
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.PairAlgebra     using ( compose1U ; compose1U_eq )
open import BRA3.Logic           using ( prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive  using ( compI )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import BRA3.CourseOfValues  using ( iter )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.Formula         using ( substT )

------------------------------------------------------------------------
-- The abstract loop module.

module Loop
  (p : Fun1)
  (p_le_one : (r : Term) -> Deriv (leq (ap1 p r) (ap1 s O)))
  (z : Term)
  (dHit : Deriv (eqF (ap1 p z) (ap1 s O)))
  (dBelow : (x : Term) ->
            Deriv (imp (leq (ap1 s x) z) (eqF (ap1 p x) O)))
  where

  ----------------------------------------------------------------------
  -- SECTION 1.  pFlip = isZero . p .

  pFlip : Fun1
  pFlip = compose1U isZero p

  pFlip_unfold :
    (r : Term) -> Deriv (eqF (ap1 pFlip r) (ap1 isZero (ap1 p r)))
  pFlip_unfold r = compose1U_eq isZero p r

  pFlip_at_hit : Deriv (eqF (ap1 pFlip z) O)
  pFlip_at_hit =
    let e1 : Deriv (eqF (ap1 isZero (ap1 p z)) (ap1 isZero (ap1 s O)))
        e1 = cong1 isZero dHit
        e2 : Deriv (eqF (ap1 isZero (ap1 s O)) O)
        e2 = ruleInst 0 O TisZeroSucc
    in ruleTrans (pFlip_unfold z) (ruleTrans e1 e2)

  pFlip_below :
    (x : Term) ->
    Deriv (imp (leq (ap1 s x) z) (eqF (ap1 pFlip x) (ap1 s O)))
  pFlip_below x =
    let congZ : Deriv (imp (eqF (ap1 p x) O)
                            (eqF (ap1 isZero (ap1 p x)) (ap1 isZero O)))
        congZ = ax_eqCong1 isZero (ap1 p x) O
        toSO : Deriv (imp (eqF (ap1 isZero (ap1 p x)) (ap1 isZero O))
                          (eqF (ap1 isZero (ap1 p x)) (ap1 s O)))
        toSO = appendEqRight (ap1 isZero (ap1 p x)) (ap1 isZero O) (ap1 s O) TisZeroZ
        chain1 : Deriv (imp (leq (ap1 s x) z) (eqF (ap1 isZero (ap1 p x)) (ap1 s O)))
        chain1 = compI (dBelow x) (compI congZ toSO)
        bridge : Deriv (imp (eqF (ap1 isZero (ap1 p x)) (ap1 s O))
                            (eqF (ap1 pFlip x) (ap1 s O)))
        bridge = prependEqLeft (ap1 pFlip x) (ap1 isZero (ap1 p x)) (ap1 s O)
                   (pFlip_unfold x)
    in compI chain1 bridge

  ----------------------------------------------------------------------
  -- SECTION 2.  Re-export FirstHit.Search at  p .

  open Search p p_le_one public

------------------------------------------------------------------------
-- SECTION 3.  ClosedAtVar + iter_add_term + TReaches infrastructure.
-- These live OUTSIDE the Loop module (the Term-fuel composition is independent
-- of the abstract predicate parameters).

record ClosedAtVar (k : Nat) (t : Term) : Set where
  constructor mkCAV
  field
    cavSubst : (b : Term) -> Eq (substT k b t) t

open ClosedAtVar public

cav_O : (k : Nat) -> ClosedAtVar k O
cav_O k = mkCAV (\ _ -> refl)

cav_ap1 : (k : Nat) (f : Fun1) (t : Term) ->
          ClosedAtVar k t -> ClosedAtVar k (ap1 f t)
cav_ap1 k f t ct = mkCAV (\ b -> eqCong (ap1 f) (cavSubst ct b))

cav_ap2 : (k : Nat) (g : Fun2) (a b : Term) ->
          ClosedAtVar k a -> ClosedAtVar k b -> ClosedAtVar k (ap2 g a b)
cav_ap2 k g a b ca cb = mkCAV (\ b' ->
  eqTrans
    (eqCong (\ x -> ap2 g x (substT k b' b)) (cavSubst ca b'))
    (eqCong (\ y -> ap2 g a y) (cavSubst cb b')))

cav_var : (k j : Nat) -> Eq (natEq k j) false -> ClosedAtVar k (var j)
cav_var k j neq = mkCAV (\ b ->
  eqSubst (\ x -> Eq (boolCase x b (var j)) (var j)) (eqSym neq) refl)

cav_natCode : (k : Nat) (n : Nat) -> ClosedAtVar k (natCode n)
cav_natCode k zero    = cav_O k
cav_natCode k (suc n) = cav_ap1 k s (natCode n) (cav_natCode k n)

------------------------------------------------------------------------
-- Universal sigma reduction lemmas.

sigma_at_O_univ : (a : Term) -> Deriv (eqF (ap2 sigma a O) a)
sigma_at_O_univ a = ruleTrans (ax_R_base u s2 v a) (ax_u a)

sigma_at_succ_univ : (a n : Term) ->
  Deriv (eqF (ap2 sigma a (ap1 s n)) (ap1 s (ap2 sigma a n)))
sigma_at_succ_univ a n = ruleInst2 1 n 0 a refl T34

------------------------------------------------------------------------
-- iter_add at Term level.

iter_add_base_natural :
  (c b : Term) ->
  Deriv (eqF (ap2 (iter stepU) c (ap2 sigma b O))
              (ap2 (iter stepU) (ap2 (iter stepU) c b) O))
iter_add_base_natural c b =
  let lhs : Deriv (eqF (ap2 (iter stepU) c (ap2 sigma b O))
                        (ap2 (iter stepU) c b))
      lhs = congR (iter stepU) c (sigma_at_O_univ b)
      rhs : Deriv (eqF (ap2 (iter stepU) (ap2 (iter stepU) c b) O)
                        (ap2 (iter stepU) c b))
      rhs = iter_base_univ stepU (ap2 (iter stepU) c b)
  in ruleTrans lhs (ruleSym rhs)

iter_add_step_natural :
  (c b : Term) ->
  Deriv (imp (eqF (ap2 (iter stepU) c (ap2 sigma b (var 5)))
                   (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5)))
              (eqF (ap2 (iter stepU) c (ap2 sigma b (ap1 s (var 5))))
                    (ap2 (iter stepU) (ap2 (iter stepU) c b) (ap1 s (var 5)))))
iter_add_step_natural c b =
  let P : Formula
      P = eqF (ap2 (iter stepU) c (ap2 sigma b (var 5)))
              (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5))
      ev1 : Deriv (eqF (ap2 (iter stepU) c (ap2 sigma b (ap1 s (var 5))))
                        (ap2 (iter stepU) c (ap1 s (ap2 sigma b (var 5)))))
      ev1 = congR (iter stepU) c (sigma_at_succ_univ b (var 5))
      ev2 : Deriv (eqF (ap2 (iter stepU) c (ap1 s (ap2 sigma b (var 5))))
                        (ap1 stepU (ap2 (iter stepU) c (ap2 sigma b (var 5)))))
      ev2 = iter_step_univ stepU c (ap2 sigma b (var 5))
      ev3 : Deriv (eqF (ap2 (iter stepU) (ap2 (iter stepU) c b) (ap1 s (var 5)))
                        (ap1 stepU (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5))))
      ev3 = iter_step_univ stepU (ap2 (iter stepU) c b) (var 5)
      lhsChain : Deriv (eqF (ap2 (iter stepU) c (ap2 sigma b (ap1 s (var 5))))
                             (ap1 stepU (ap2 (iter stepU) c (ap2 sigma b (var 5)))))
      lhsChain = ruleTrans ev1 ev2
      ihToStepRHS : Deriv (imp P (eqF (ap1 stepU (ap2 (iter stepU) c (ap2 sigma b (var 5))))
                                       (ap1 stepU (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5)))))
      ihToStepRHS = ax_eqCong1 stepU
                      (ap2 (iter stepU) c (ap2 sigma b (var 5)))
                      (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5))
      stepRHSEq : Deriv (eqF (ap1 stepU (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5)))
                              (ap2 (iter stepU) (ap2 (iter stepU) c b) (ap1 s (var 5))))
      stepRHSEq = ruleSym ev3
      imp_stepRHS : Deriv (imp P (eqF (ap1 stepU (ap2 (iter stepU) c (ap2 sigma b (var 5))))
                                       (ap2 (iter stepU) (ap2 (iter stepU) c b) (ap1 s (var 5)))))
      imp_stepRHS =
        compI ihToStepRHS
          (appendEqRight
             (ap1 stepU (ap2 (iter stepU) c (ap2 sigma b (var 5))))
             (ap1 stepU (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5)))
             (ap2 (iter stepU) (ap2 (iter stepU) c b) (ap1 s (var 5)))
             stepRHSEq)
  in compI imp_stepRHS
       (prependEqLeft
          (ap2 (iter stepU) c (ap2 sigma b (ap1 s (var 5))))
          (ap1 stepU (ap2 (iter stepU) c (ap2 sigma b (var 5))))
          (ap2 (iter stepU) (ap2 (iter stepU) c b) (ap1 s (var 5)))
          lhsChain)

iter_add_term :
  (a b c : Term) ->
  ClosedAtVar 5 b -> ClosedAtVar 5 c ->
  Deriv (eqF (ap2 (iter stepU) c (ap2 sigma b a))
              (ap2 (iter stepU) (ap2 (iter stepU) c b) a))
iter_add_term a b c cb cc =
  let P : Formula
      P = eqF (ap2 (iter stepU) c (ap2 sigma b (var 5)))
              (ap2 (iter stepU) (ap2 (iter stepU) c b) (var 5))

      svar : Term
      svar = ap1 s (var 5)

      cb_at_svar : Eq (substT 5 svar b) b
      cb_at_svar = cavSubst cb svar
      cc_at_svar : Eq (substT 5 svar c) c
      cc_at_svar = cavSubst cc svar
      cb_at_O : Eq (substT 5 O b) b
      cb_at_O = cavSubst cb O
      cc_at_O : Eq (substT 5 O c) c
      cc_at_O = cavSubst cc O

      base_coerced : Deriv (eqF (ap2 (iter stepU) (substT 5 O c) (ap2 sigma (substT 5 O b) O))
                                 (ap2 (iter stepU) (ap2 (iter stepU) (substT 5 O c) (substT 5 O b)) O))
      base_coerced =
        eqSubst
          (\ b' -> Deriv (eqF (ap2 (iter stepU) (substT 5 O c) (ap2 sigma b' O))
                               (ap2 (iter stepU) (ap2 (iter stepU) (substT 5 O c) b') O)))
          (eqSym cb_at_O)
          (eqSubst
             (\ c' -> Deriv (eqF (ap2 (iter stepU) c' (ap2 sigma b O))
                                  (ap2 (iter stepU) (ap2 (iter stepU) c' b) O)))
             (eqSym cc_at_O)
             (iter_add_base_natural c b))

      step_coerced : Deriv (imp P
                                 (eqF (ap2 (iter stepU) (substT 5 svar c) (ap2 sigma (substT 5 svar b) svar))
                                       (ap2 (iter stepU) (ap2 (iter stepU) (substT 5 svar c) (substT 5 svar b)) svar)))
      step_coerced =
        eqSubst
          (\ b' -> Deriv (imp P
                                (eqF (ap2 (iter stepU) (substT 5 svar c) (ap2 sigma b' svar))
                                      (ap2 (iter stepU) (ap2 (iter stepU) (substT 5 svar c) b') svar))))
          (eqSym cb_at_svar)
          (eqSubst
             (\ c' -> Deriv (imp P
                                   (eqF (ap2 (iter stepU) c' (ap2 sigma b svar))
                                         (ap2 (iter stepU) (ap2 (iter stepU) c' b) svar))))
             (eqSym cc_at_svar)
             (iter_add_step_natural c b))

      univ : Deriv P
      univ = ruleIndNat 5 {P = P} base_coerced step_coerced

      raw : Deriv (eqF (ap2 (iter stepU) (substT 5 a c) (ap2 sigma (substT 5 a b) a))
                        (ap2 (iter stepU) (ap2 (iter stepU) (substT 5 a c) (substT 5 a b)) a))
      raw = ruleInst 5 a univ

      eb : Eq (substT 5 a b) b
      eb = cavSubst cb a
      ec : Eq (substT 5 a c) c
      ec = cavSubst cc a
  in eqSubst
       (\ b' -> Deriv (eqF (ap2 (iter stepU) c (ap2 sigma b' a))
                            (ap2 (iter stepU) (ap2 (iter stepU) c b') a)))
       eb
       (eqSubst
          (\ c' -> Deriv (eqF (ap2 (iter stepU) c' (ap2 sigma (substT 5 a b) a))
                               (ap2 (iter stepU) (ap2 (iter stepU) c' (substT 5 a b)) a)))
          ec
          raw)

------------------------------------------------------------------------
-- TReaches: Term-fueled Reaches with ClosedAtVar 5 propagation.

record TReaches (c c' : Term) : Set where
  constructor mkTReach
  field
    tsteps     : Term
    tstepsCAV5 : ClosedAtVar 5 tsteps
    truns      : Deriv (eqF (ap2 (iter stepU) c tsteps) c')

open TReaches public

treach_refl : (c : Term) -> TReaches c c
treach_refl c = mkTReach O (cav_O 5) (iter_base_univ stepU c)

treach_step1 : {c c' : Term} -> Deriv (eqF (ap1 stepU c) c') -> TReaches c c'
treach_step1 {c} {c'} e =
  mkTReach (ap1 s O) (cav_ap1 5 s O (cav_O 5))
    (ruleTrans (iter_step_univ stepU c O)
      (ruleTrans (cong1 stepU (iter_base_univ stepU c)) e))

treach_eq_target : {c c' c'' : Term} -> TReaches c c' -> Deriv (eqF c' c'') -> TReaches c c''
treach_eq_target (mkTReach n cn e) e' = mkTReach n cn (ruleTrans e e')

treach_from_reach : {c c' : Term} -> Reaches c c' -> TReaches c c'
treach_from_reach {c} {c'} r = mkTReach (natCode (steps r)) (cav_natCode 5 (steps r)) (runs r)

treach_trans : {c c' c'' : Term} -> ClosedAtVar 5 c ->
               TReaches c c' -> TReaches c' c'' -> TReaches c c''
treach_trans {c} {c'} {c''} cc (mkTReach n1 cn1 e1) (mkTReach n2 cn2 e2) =
  let addEq : Deriv (eqF (ap2 (iter stepU) c (ap2 sigma n1 n2))
                          (ap2 (iter stepU) (ap2 (iter stepU) c n1) n2))
      addEq = iter_add_term n2 n1 c cn1 cc
      via_e1 : Deriv (eqF (ap2 (iter stepU) (ap2 (iter stepU) c n1) n2)
                           (ap2 (iter stepU) c' n2))
      via_e1 = congL (iter stepU) n2 e1
  in mkTReach (ap2 sigma n1 n2) (cav_ap2 5 sigma n1 n2 cn1 cn2)
       (ruleTrans addEq (ruleTrans via_e1 e2))
