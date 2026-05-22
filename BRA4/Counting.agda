{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.Counting -- the injectivity unit step for the arbitrary-injection
-- pigeonhole (Gate-1 route R3).  Builds on BRA4.PHP, which already has the
-- count  Csum , the range bound  Crange , the by-cases combinator, and the
-- assembly  php_via_unit_step  reducing the whole pigeonhole to ONE lemma
--
--   unit_step : InjBelow idx N -> UnitStep idx N .
--
-- Here we discharge that lemma.  The mathematics is Skolem 1923 Df. 2
-- (BRA4/Skolem23.pdf):  [a < t+1] = [a < t] + [a = t] , summed over the
-- index range, gives  C(t+1) = C(t) + #{ j : idx j = t } , and injectivity
-- bounds the equality-count by 1, so  C(t+1) <= C(t) + 1 = s (C t) .
--
-- This file is Sigma_1-FREE: pure BRA arithmetic, no  thmT , no provability.

module BRA4.Counting where

open import BRA4.Base
open import BRA4.PHP
open import BRA4.Code     using ( falseF )

open import BRA4.RuleInst3 using ( simSubst3F ; five_step_F )

open import BRA3.RuleInst2 using
  ( ruleInst2 ; NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right ; le-trans
  ; maxN ; maxN-le-left ; maxN-le-right ; maxVarT ; maxVarF
  ; natEq-lt-false ; natEq_sym )

open import BRA4.LeqMono  using ( leq_trans )

open import BRA3.Church       using
  ( sub ; sigma ; T33 ; T34 ; T36 ; T39 ; predecessor ; T_p_S_v0 )
open import BRA3.ChurchLeq    using ( leq ; T76 )
open import BRA3.ChurchT69    using ( T69 )
open import BRA3.ChurchT73    using ( T73 )
open import BRA3.ChurchT81    using ( T81 )
open import BRA3.ChurchT82    using ( T82 )
open import BRA3.ChurchT85    using ( T85 )
open import BRA3.ChurchT68    using ( T68 )
open import BRA3.ChurchT87    using ( T87 ; notLeqSucSelf )
open import BRA3.ChurchSubSucc using ( T_sub_O ; T57sub )
open import BRA3.ChurchStrictTrich using ( strictTrich )
open import BRA3.Logic        using ( eqSymImp ; prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive using
  ( liftP ; compI ; bComb ; bCombTwo ; axContrapos ; axExFalso ; DNE )

------------------------------------------------------------------------
------------------------------------------------------------------------
-- A 3-variable simultaneous-substitution rule at the fixed indices
-- (0, 1, 2), the natural extension of  BRA3.RuleInst2.ruleInst2 .
--
-- It is needed because the sum-split below rearranges nested sigma's of
-- four ABSTRACT-headed terms (Csum / EqSum at an abstract numeral bound),
-- where nested  ruleInst  on the 3-var theorems T39 / T86 would get stuck
-- on  substT  of an abstract subterm.  Simultaneous substitution (via the
-- meta-level  simSubst3F  + the  five_step_F  bridge already proven in
-- BRA4.RuleInst3) places the substituents at the leaves without ever
-- traversing them, exactly as  ruleInst2  does for two variables.

ruleInst3v :
  (a b c : Term) {P : Formula} ->
  Deriv P ->
  Deriv (simSubst3F zero a (suc zero) b (suc (suc zero)) c P)
ruleInst3v a b c {P} dP =
  let
    base : Nat
    base = maxN (maxVarF P) (maxN (maxVarT a) (maxN (maxVarT b) (maxVarT c)))

    c1 : Nat
    c1 = suc (suc (suc base))

    c2 : Nat
    c2 = suc (suc (suc (suc base)))

    P<=base : NatLe (maxVarF P) base
    P<=base = maxN-le-left (maxVarF P) (maxN (maxVarT a) (maxN (maxVarT b) (maxVarT c)))

    a<=base : NatLe (maxVarT a) base
    a<=base = le-trans (maxN-le-left (maxVarT a) (maxN (maxVarT b) (maxVarT c)))
                       (maxN-le-right (maxVarF P) (maxN (maxVarT a) (maxN (maxVarT b) (maxVarT c))))

    b<=base : NatLe (maxVarT b) base
    b<=base = le-trans (maxN-le-left (maxVarT b) (maxVarT c))
                (le-trans (maxN-le-right (maxVarT a) (maxN (maxVarT b) (maxVarT c)))
                          (maxN-le-right (maxVarF P) (maxN (maxVarT a) (maxN (maxVarT b) (maxVarT c)))))

    base<=c1 : NatLe base c1
    base<=c1 = le-suc-right (le-suc-right (le-suc-right (le-refl base)))

    base<=c2 : NatLe base c2
    base<=c2 = le-suc-right base<=c1

    P<=c1 : NatLe (maxVarF P) c1
    P<=c1 = le-trans P<=base base<=c1
    P<=c2 : NatLe (maxVarF P) c2
    P<=c2 = le-trans P<=base base<=c2
    a<=c1 : NatLe (maxVarT a) c1
    a<=c1 = le-trans a<=base base<=c1
    a<=c2 : NatLe (maxVarT a) c2
    a<=c2 = le-trans a<=base base<=c2
    b<=c2 : NatLe (maxVarT b) c2
    b<=c2 = le-trans b<=base base<=c2

    c1ne0 : Eq (natEq c1 zero) false
    c1ne0 = natEq-lt-false c1 zero (le-suc (le-zero (suc (suc base))))
    c1ne1 : Eq (natEq c1 (suc zero)) false
    c1ne1 = natEq-lt-false c1 (suc zero) (le-suc (le-suc (le-zero (suc base))))
    c1ne2 : Eq (natEq c1 (suc (suc zero))) false
    c1ne2 = natEq-lt-false c1 (suc (suc zero)) (le-suc (le-suc (le-suc (le-zero base))))
    c2ne0 : Eq (natEq c2 zero) false
    c2ne0 = natEq-lt-false c2 zero (le-suc (le-zero (suc (suc (suc base)))))
    c2ne1 : Eq (natEq c2 (suc zero)) false
    c2ne1 = natEq-lt-false c2 (suc zero) (le-suc (le-suc (le-zero (suc (suc base)))))
    c2ne2 : Eq (natEq c2 (suc (suc zero))) false
    c2ne2 = natEq-lt-false c2 (suc (suc zero)) (le-suc (le-suc (le-suc (le-zero (suc base)))))
    c1nec2 : Eq (natEq c1 c2) false
    c1nec2 = eqTrans (natEq_sym c1 c2) (natEq-lt-false c2 c1 (le-refl c2))

    step1 = ruleInst (suc zero) (var c1) dP
    step2 = ruleInst (suc (suc zero)) (var c2) step1
    step3 = ruleInst zero a step2
    step4 = ruleInst c1 b step3
    step5 = ruleInst c2 c step4

    bridge = five_step_F zero a (suc zero) b (suc (suc zero)) c c1 c2
               refl refl refl
               c1ne0 c1ne1 c1ne2 c2ne0 c2ne1 c2ne2 c1nec2
               a<=c1 a<=c2 b<=c2 P P<=c1 P<=c2
  in eqSubst Deriv bridge step5

------------------------------------------------------------------------
-- Sigma algebra (all universal in abstract Terms, built from ruleInst2 /
-- ruleInst3v + the congruence helpers, never nested ruleInst).

-- commutativity:  sigma a b = sigma b a .
sigma_comm : (a b : Term) -> Deriv (eqF (ap2 sigma a b) (ap2 sigma b a))
sigma_comm a b = ruleInst2 zero a (suc zero) b refl T36

-- associativity:  sigma a (sigma b c) = sigma (sigma a b) c .
sigma_assoc :
  (a b c : Term) ->
  Deriv (eqF (ap2 sigma a (ap2 sigma b c)) (ap2 sigma (ap2 sigma a b) c))
sigma_assoc a b c = ruleInst3v a b c T39

-- middle-four interchange:  (a+b)+(c+d) = (a+c)+(b+d) .
interchange :
  (a b c d : Term) ->
  Deriv (eqF (ap2 sigma (ap2 sigma a b) (ap2 sigma c d))
              (ap2 sigma (ap2 sigma a c) (ap2 sigma b d)))
interchange a b c d =
  let e0 : Deriv (eqF (ap2 sigma (ap2 sigma a b) (ap2 sigma c d))
                       (ap2 sigma a (ap2 sigma b (ap2 sigma c d))))
      e0 = ruleSym (sigma_assoc a b (ap2 sigma c d))

      e1 : Deriv (eqF (ap2 sigma a (ap2 sigma b (ap2 sigma c d)))
                       (ap2 sigma a (ap2 sigma (ap2 sigma b c) d)))
      e1 = congR sigma a (sigma_assoc b c d)

      e2 : Deriv (eqF (ap2 sigma a (ap2 sigma (ap2 sigma b c) d))
                       (ap2 sigma a (ap2 sigma (ap2 sigma c b) d)))
      e2 = congR sigma a (congL sigma d (sigma_comm b c))

      e3 : Deriv (eqF (ap2 sigma a (ap2 sigma (ap2 sigma c b) d))
                       (ap2 sigma a (ap2 sigma c (ap2 sigma b d))))
      e3 = congR sigma a (ruleSym (sigma_assoc c b d))

      e4 : Deriv (eqF (ap2 sigma a (ap2 sigma c (ap2 sigma b d)))
                       (ap2 sigma (ap2 sigma a c) (ap2 sigma b d)))
      e4 = sigma_assoc a c (ap2 sigma b d)
  in ruleTrans e0 (ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4)))

-- sigma x (s O) = s x .
sigma_x_one : (x : Term) -> Deriv (eqF (ap2 sigma x (ap1 s O)) (ap1 s x))
sigma_x_one x =
  ruleTrans (ruleInst2 zero x (suc zero) O refl T34)
            (cong1 s (T33 x))

-- 0 <= x .
leqZ : (x : Term) -> Deriv (leq O x)
leqZ x = ruleInst zero x T76

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Order helpers (universal, imp-form so they compose under by-cases).

-- Successor is injective:  imp (s a = s b) (a = b) .
--   pred (s a) = a  [T_p_S_v0] , then  s a = s b  =>  pred (s a) = pred (s b)
--   =>  a = pred (s b) = b .
s_inj_imp :
  (a b : Term) -> Deriv (imp (eqF (ap1 s a) (ap1 s b)) (eqF a b))
s_inj_imp a b =
  let pa : Deriv (eqF (ap1 predecessor (ap1 s a)) a)
      pa = ruleInst zero a T_p_S_v0
      pb : Deriv (eqF (ap1 predecessor (ap1 s b)) b)
      pb = ruleInst zero b T_p_S_v0
      s1 : Deriv (imp (eqF (ap1 s a) (ap1 s b))
                       (eqF (ap1 predecessor (ap1 s a)) (ap1 predecessor (ap1 s b))))
      s1 = ax_eqCong1 predecessor (ap1 s a) (ap1 s b)
      s2 : Deriv (imp (eqF (ap1 predecessor (ap1 s a)) (ap1 predecessor (ap1 s b)))
                       (eqF a (ap1 predecessor (ap1 s b))))
      s2 = prependEqLeft a (ap1 predecessor (ap1 s a)) (ap1 predecessor (ap1 s b))
                          (ruleSym pa)
      s3 : Deriv (imp (eqF a (ap1 predecessor (ap1 s b))) (eqF a b))
      s3 = appendEqRight a (ap1 predecessor (ap1 s b)) b pb
  in compI s1 (compI s2 s3)

-- Antisymmetry, imp-form:  given  a <= b ,  imp (b <= a) (a = b) .
--   T87 :  a <= b  =>  s (b - a) = (s b) - a .
--   With  b <= a  i.e.  b - a = O :  s (b-a) = s O , so  (s b) - a = s O ,
--   so  s b = s a  [T69] , so  a = b  [s injective + symmetry] .
antisym_imp :
  (a b : Term) -> Deriv (leq a b) -> Deriv (imp (leq b a) (eqF a b))
antisym_imp a b leAB =
  let t87 : Deriv (eqF (ap1 s (ap2 sub b a)) (ap2 sub (ap1 s b) a))
      t87 = mp (ruleInst2 zero a (suc zero) b refl T87) leAB
      p1 : Deriv (imp (eqF (ap2 sub b a) O)
                       (eqF (ap1 s (ap2 sub b a)) (ap1 s O)))
      p1 = ax_eqCong1 s (ap2 sub b a) O
      p2 : Deriv (imp (eqF (ap1 s (ap2 sub b a)) (ap1 s O))
                       (eqF (ap2 sub (ap1 s b) a) (ap1 s O)))
      p2 = prependEqLeft (ap2 sub (ap1 s b) a) (ap1 s (ap2 sub b a)) (ap1 s O)
                          (ruleSym t87)
      p3 : Deriv (imp (eqF (ap2 sub (ap1 s b) a) (ap1 s O))
                       (eqF (ap1 s b) (ap1 s a)))
      p3 = ruleInst2 zero (ap1 s b) (suc zero) a refl T69
      p4 : Deriv (imp (eqF (ap1 s b) (ap1 s a)) (eqF a b))
      p4 = compI (s_inj_imp b a) (eqSymImp b a)
  in compI p1 (compI p2 (compI p3 p4))

-- a <= b  and  a /= b  imply  s a <= b  ( a < b strictly ).
--   neg (b <= a)  via antisymmetry, then strictTrich.
lt_from_le_neq :
  (a b : Term) ->
  Deriv (leq a b) -> Deriv (neg (eqF a b)) -> Deriv (leq (ap1 s a) b)
lt_from_le_neq a b leAB neAB =
  let nlba : Deriv (neg (leq b a))
      nlba = negIntro (leq b a) (eqF a b)
               (antisym_imp a b leAB)
               (liftP (leq b a) neAB)
  in mp (ruleInst2 zero b (suc zero) a refl strictTrich) nlba

-- x /= 0  implies  1 <= x .
--   leq x O  is interchangeable with  x = O  (T_sub_O), so  neg (x = O)
--   gives  neg (x <= O) , and strictTrich gives  s O <= x .
nonzero_ge_one :
  (x : Term) -> Deriv (neg (eqF x O)) -> Deriv (leq (ap1 s O) x)
nonzero_ge_one x neX =
  let leXO_to_eq : Deriv (imp (leq x O) (eqF x O))
      leXO_to_eq = prependEqLeft x (ap2 sub x O) O (ruleSym (T_sub_O x))
      nlxO : Deriv (neg (leq x O))
      nlxO = negIntro (leq x O) (eqF x O) leXO_to_eq (liftP (leq x O) neX)
  in mp (ruleInst2 zero x (suc zero) O refl strictTrich) nlxO

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Deduction-theorem helpers (Carneiro / ndw2.pdf style): to prove a fact
-- under an object hypothesis, carry  imp H _  through the derivation, with
-- mp -> bComb , axiom/lemma -> liftP H , hypothesis -> identP H .

-- Apply a fixed implication  Z -> Z'  under two carried hypotheses.
mapUnder2 :
  (phi psi : Formula) {Z Z' : Formula} ->
  Deriv (imp Z Z') -> Deriv (imp phi (imp psi Z)) ->
  Deriv (imp phi (imp psi Z'))
mapUnder2 phi psi zz' d = bCombTwo (liftP phi (liftP psi zz')) d

-- Combine two carried hypotheses (S-combinator under  imp H ).
bComb2 :
  {H Q1 Q2 G : Formula} ->
  Deriv (imp H (imp Q1 (imp Q2 G))) ->
  Deriv (imp H Q1) -> Deriv (imp H Q2) -> Deriv (imp H G)
bComb2 f a1 a2 = bComb (bComb f a1) a2

-- from  X -> falseF  is derivable when  neg X  holds (ex falso).
negToImpFalse : (X : Formula) -> Deriv (neg X) -> Deriv (imp X falseF)
negToImpFalse X nx = bComb (axExFalso X falseF) (liftP X nx)

-- imp-form of impFalseToNeg.
impFalseToNeg_imp : (X : Formula) -> Deriv (imp (imp X falseF) (neg X))
impFalseToNeg_imp X =
  bComb (axContrapos X falseF) (liftP (imp X falseF) negFalseF)

------------------------------------------------------------------------
-- leq rewriting + small order facts (imp-form).

-- rewrite the SECOND argument of leq by an equation.
leq_eqR : (a b c : Term) -> Deriv (eqF b c) -> Deriv (leq a b) -> Deriv (leq a c)
leq_eqR a b c bc ab =
  ruleTrans (ruleSym (mp (ax_eqCongR sub b c a) bc)) ab

-- p = O  implies  leq p r   (imp-form).
leq_of_left_zero_imp : (p r : Term) -> Deriv (imp (eqF p O) (leq p r))
leq_of_left_zero_imp p r =
  compI (ax_eqCongL sub p O r)
        (appendEqRight (ap2 sub p r) (ap2 sub O r) O (ruleInst zero r T76))

-- p = s O  implies  leq p (s O)   (imp-form).
leq_of_left_eq_one : (p : Term) -> Deriv (imp (eqF p (ap1 s O)) (leq p (ap1 s O)))
leq_of_left_eq_one p =
  compI (ax_eqCongL sub p (ap1 s O) (ap1 s O))
        (appendEqRight (ap2 sub p (ap1 s O)) (ap2 sub (ap1 s O) (ap1 s O)) O
                       (ruleInst zero (ap1 s O) T73))

-- p = s O  and  q = s O  imply  leq p q   (curried imp-form).
leq_both_one_imp :
  (p q : Term) ->
  Deriv (imp (eqF p (ap1 s O)) (imp (eqF q (ap1 s O)) (leq p q)))
leq_both_one_imp p q =
  let U' : Term
      U' = ap2 sub p q
      V' : Term
      V' = ap2 sub (ap1 s O) q
      W' : Term
      W' = ap2 sub (ap1 s O) (ap1 s O)
      r1 : Deriv (imp (eqF p (ap1 s O)) (eqF U' V'))
      r1 = ax_eqCongL sub p (ap1 s O) q
      r2 : Deriv (imp (eqF q (ap1 s O)) (eqF V' W'))
      r2 = ax_eqCongR sub q (ap1 s O) (ap1 s O)
      base : Deriv (eqF W' O)
      base = ruleInst zero (ap1 s O) T73
      r2' : Deriv (imp (eqF q (ap1 s O)) (eqF V' O))
      r2' = compI r2 (appendEqRight V' W' O base)
      r1sym : Deriv (imp (eqF p (ap1 s O)) (eqF V' U'))
      r1sym = compI r1 (eqSymImp U' V')
      X1 : Deriv (imp (eqF p (ap1 s O)) (imp (eqF V' O) (eqF U' O)))
      X1 = compI r1sym (ax_eqTrans V' U' O)
      first : Deriv (imp (eqF p (ap1 s O))
                          (imp (eqF q (ap1 s O)) (imp (eqF V' O) (eqF U' O))))
      first = compI X1 (axK (imp (eqF V' O) (eqF U' O)) (eqF q (ap1 s O)))
      second : Deriv (imp (eqF p (ap1 s O)) (imp (eqF q (ap1 s O)) (eqF V' O)))
      second = liftP (eqF p (ap1 s O)) r2'
  in bCombTwo first second

------------------------------------------------------------------------
-- Antisymmetry, fully curried imp-form:  imp (a<=b) (imp (b<=a) (a=b)) .
-- (the meta version  antisym_imp  above takes  a<=b  as a Deriv; this is
-- the doubly-varying Carneiro lift, needed inside by-cases branches.)

antisym_curry :
  (a b : Term) -> Deriv (imp (leq a b) (imp (leq b a) (eqF a b)))
antisym_curry a b =
  let phi : Formula
      phi = leq a b
      psi : Formula
      psi = leq b a
      P : Term
      P = ap1 s (ap2 sub b a)
      Q : Term
      Q = ap2 sub (ap1 s b) a
      W : Formula
      W = eqF P Q
      T87inst : Deriv (imp phi W)
      T87inst = ruleInst2 zero a (suc zero) b refl T87
      t87L : Deriv (imp phi (imp psi W))
      t87L = compI T87inst (axK W psi)
      sL : Deriv (imp phi (imp psi (eqF P (ap1 s O))))
      sL = liftP phi (ax_eqCong1 s (ap2 sub b a) O)
      combineWR : Deriv (imp W (imp (eqF P (ap1 s O)) (eqF Q (ap1 s O))))
      combineWR = ax_eqTrans P Q (ap1 s O)
      step_a : Deriv (imp phi (imp psi (imp (eqF P (ap1 s O)) (eqF Q (ap1 s O)))))
      step_a = mapUnder2 phi psi combineWR t87L
      e1L : Deriv (imp phi (imp psi (eqF Q (ap1 s O))))
      e1L = bCombTwo step_a sL
      e2L : Deriv (imp phi (imp psi (eqF (ap1 s b) (ap1 s a))))
      e2L = mapUnder2 phi psi (ruleInst2 zero (ap1 s b) (suc zero) a refl T69) e1L
  in mapUnder2 phi psi (compI (s_inj_imp b a) (eqSymImp b a)) e2L

-- a <= b  and  a /= b  imply  s a <= b   (imp-form, neq fixed).
lt_from_le_neq_imp :
  (a b : Term) ->
  Deriv (neg (eqF a b)) -> Deriv (imp (leq a b) (leq (ap1 s a) b))
lt_from_le_neq_imp a b neAB =
  let phi : Formula
      phi = leq a b
      psi : Formula
      psi = leq b a
      AC : Deriv (imp phi (imp psi (eqF a b)))
      AC = antisym_curry a b
      g : Deriv (imp (eqF a b) falseF)
      g = negToImpFalse (eqF a b) neAB
      F2 : Deriv (imp phi (imp psi falseF))
      F2 = bCombTwo (liftP phi (liftP psi g)) AC
      NL : Deriv (imp phi (neg (leq b a)))
      NL = compI F2 (impFalseToNeg_imp (leq b a))
      ST : Deriv (imp (neg (leq b a)) (leq (ap1 s a) b))
      ST = ruleInst2 zero b (suc zero) a refl strictTrich
  in compI NL ST

-- x /= 0  implies  1 <= x   (imp-form).
nonzero_ge_one_imp : (x : Term) -> Deriv (imp (neg (eqF x O)) (leq (ap1 s O) x))
nonzero_ge_one_imp x =
  let leXO_to_eq : Deriv (imp (leq x O) (eqF x O))
      leXO_to_eq = prependEqLeft x (ap2 sub x O) O (ruleSym (T_sub_O x))
      contra : Deriv (imp (neg (eqF x O)) (neg (leq x O)))
      contra = mp (axContrapos (leq x O) (eqF x O)) leXO_to_eq
      strict : Deriv (imp (neg (leq x O)) (leq (ap1 s O) x))
      strict = ruleInst2 zero x (suc zero) O refl strictTrich
  in compI contra strict

------------------------------------------------------------------------
-- indLt indicator facts (imp-form).

-- a < b  (i.e. s a <= b)  implies  indLt a b = s O .
indLt_at_lt_imp : (a b : Term) -> Deriv (imp (leq (ap1 s a) b) (eqF (indLt a b) (ap1 s O)))
indLt_at_lt_imp a b =
  compI (ax_eqCongR sub (ap2 sub (ap1 s a) b) O (ap1 s O))
        (appendEqRight (ap2 sub (ap1 s O) (ap2 sub (ap1 s a) b))
                       (ap2 sub (ap1 s O) O) (ap1 s O)
                       (T_sub_O (ap1 s O)))

-- NOT (a < b)  implies  indLt a b = O  (the indicator is 0 above range).
indLt_at_ge_imp : (a b : Term) -> Deriv (imp (neg (leq (ap1 s a) b)) (eqF (indLt a b) O))
indLt_at_ge_imp a b = nonzero_ge_one_imp (ap2 sub (ap1 s a) b)

-- indLt a b <= s O  (the indicator is bounded by 1).
indLt_le_one : (a b : Term) -> Deriv (leq (indLt a b) (ap1 s O))
indLt_le_one a b =
  let h1 : Deriv (imp (leq (ap1 s a) b) (leq (indLt a b) (ap1 s O)))
      h1 = compI (indLt_at_lt_imp a b) (leq_of_left_eq_one (indLt a b))
      h2 : Deriv (imp (neg (leq (ap1 s a) b)) (leq (indLt a b) (ap1 s O)))
      h2 = compI (indLt_at_ge_imp a b) (leq_of_left_zero_imp (indLt a b) (ap1 s O))
  in byCases (leq (ap1 s a) b) (leq (indLt a b) (ap1 s O)) h1 h2

------------------------------------------------------------------------
-- Reassembly:  y <= x  implies  sigma y (sub x y) = x .
-- by-cases on  sub x y = O  ( x <= y ): the strict case is T68 + comm; the
-- boundary case  x <= y  combines with  y <= x  via antisymmetry.

reassembly :
  (x y : Term) -> Deriv (leq y x) -> Deriv (eqF (ap2 sigma y (ap2 sub x y)) x)
reassembly x y leyx =
  let A : Term
      A = ap2 sigma y (ap2 sub x y)
      -- h1: x <= y case.
      f1 : Deriv (imp (eqF (ap2 sub x y) O) (eqF A y))
      f1 = compI (ax_eqCongR sigma (ap2 sub x y) O y)
                 (appendEqRight A (ap2 sigma y O) y (T33 y))
      f1sym : Deriv (imp (eqF (ap2 sub x y) O) (eqF y A))
      f1sym = compI f1 (eqSymImp A y)
      f2 : Deriv (imp (eqF (ap2 sub x y) O) (eqF y x))
      f2 = antisym_imp y x leyx
      g : Deriv (imp (eqF (ap2 sub x y) O) (imp (eqF y x) (eqF A x)))
      g = compI f1sym (ax_eqTrans y A x)
      h1 : Deriv (imp (eqF (ap2 sub x y) O) (eqF A x))
      h1 = bComb g f2
      -- h2: not (x <= y) case  (T68).
      t68xy : Deriv (imp (neg (eqF (ap2 sub x y) O)) (eqF (ap2 sigma (ap2 sub x y) y) x))
      t68xy = ruleInst2 zero x (suc zero) y refl T68
      h2 : Deriv (imp (neg (eqF (ap2 sub x y) O)) (eqF A x))
      h2 = compI t68xy
                 (prependEqLeft A (ap2 sigma (ap2 sub x y) y) x
                                (sigma_comm y (ap2 sub x y)))
  in byCases (eqF (ap2 sub x y) O) (eqF A x) h1 h2

------------------------------------------------------------------------
-- indLt monotone in the upper argument:  indLt a t <= indLt a (s t) .

indLt_mono_upper :
  (a t : Term) -> Deriv (leq (indLt a t) (indLt a (ap1 s t)))
indLt_mono_upper a t =
  let Y : Term
      Y = indLt a t
      X : Term
      X = indLt a (ap1 s t)
      A1 : Deriv (imp (leq (ap1 s a) t) (eqF Y (ap1 s O)))
      A1 = indLt_at_lt_imp a t
      A2 : Deriv (imp (leq (ap1 s a) t) (eqF X (ap1 s O)))
      A2 = compI (ruleInst2 zero (ap1 s a) (suc zero) t refl T81)
                 (indLt_at_lt_imp a (ap1 s t))
      h1 : Deriv (imp (leq (ap1 s a) t) (leq Y X))
      h1 = bComb2 (liftP (leq (ap1 s a) t) (leq_both_one_imp Y X)) A1 A2
      h2 : Deriv (imp (neg (leq (ap1 s a) t)) (leq Y X))
      h2 = compI (indLt_at_ge_imp a t) (leq_of_left_zero_imp Y X)
  in byCases (leq (ap1 s a) t) (leq Y X) h1 h2

------------------------------------------------------------------------
-- The equality indicator  eqInd a t = indLt a (s t) - indLt a t  in {0,1}.

eqInd : Term -> Term -> Term
eqInd a t = ap2 sub (indLt a (ap1 s t)) (indLt a t)

-- Skolem Df. 2 split:  indLt a (s t) = sigma (indLt a t) (eqInd a t) .
indLt_succ_split :
  (a t : Term) ->
  Deriv (eqF (indLt a (ap1 s t)) (ap2 sigma (indLt a t) (eqInd a t)))
indLt_succ_split a t =
  ruleSym (reassembly (indLt a (ap1 s t)) (indLt a t) (indLt_mono_upper a t))

-- eqInd a t <= s O .
eqInd_le_one : (a t : Term) -> Deriv (leq (eqInd a t) (ap1 s O))
eqInd_le_one a t =
  let t85 : Deriv (leq (eqInd a t) (ap2 sigma (eqInd a t) (indLt a t)))
      t85 = ruleInst2 zero (eqInd a t) (suc zero) (indLt a t) refl T85
      commE : Deriv (eqF (ap2 sigma (eqInd a t) (indLt a t))
                          (ap2 sigma (indLt a t) (eqInd a t)))
      commE = sigma_comm (eqInd a t) (indLt a t)
      splitE : Deriv (eqF (ap2 sigma (indLt a t) (eqInd a t)) (indLt a (ap1 s t)))
      splitE = ruleSym (indLt_succ_split a t)
      bridgeE : Deriv (eqF (ap2 sigma (eqInd a t) (indLt a t)) (indLt a (ap1 s t)))
      bridgeE = ruleTrans commE splitE
      leqEX : Deriv (leq (eqInd a t) (indLt a (ap1 s t)))
      leqEX = leq_eqR (eqInd a t) (ap2 sigma (eqInd a t) (indLt a t))
                      (indLt a (ap1 s t)) bridgeE t85
  in leq_trans (eqInd a t) (indLt a (ap1 s t)) (ap1 s O)
               leqEX (indLt_le_one a (ap1 s t))

-- a /= t  implies  eqInd a t = O .
--   eqInd a t = sub (indLt a (s t)) (indLt a t)  and  eqF (sub X Y) O = leq X Y .
--   by-cases on  a <= t : the  not (a<=t)  branch gives indLt a (s t) = O
--   directly; the  a <= t  branch upgrades to  a < t  (via  a /= t ), making
--   both indicators 1.
eqInd_at_neq :
  (a t : Term) -> Deriv (neg (eqF a t)) -> Deriv (eqF (eqInd a t) O)
eqInd_at_neq a t neAt =
  let X : Term
      X = indLt a (ap1 s t)
      Y : Term
      Y = indLt a t
      -- h1: a <= t  ->  a < t  ->  X = Y = s O .
      A1 : Deriv (imp (leq a t) (eqF X (ap1 s O)))
      A1 = compI (lt_from_le_neq_imp a t neAt)
                 (compI (ruleInst2 zero (ap1 s a) (suc zero) t refl T81)
                        (indLt_at_lt_imp a (ap1 s t)))
      A2 : Deriv (imp (leq a t) (eqF Y (ap1 s O)))
      A2 = compI (lt_from_le_neq_imp a t neAt) (indLt_at_lt_imp a t)
      h1 : Deriv (imp (leq a t) (leq X Y))
      h1 = bComb2 (liftP (leq a t) (leq_both_one_imp X Y)) A1 A2
      -- h2: not (a <= t)  ->  indLt a (s t) = O .
      bridge_eq : Deriv (eqF X (ap2 sub (ap1 s O) (ap2 sub a t)))
      bridge_eq = congR sub (ap1 s O) (ruleInst2 zero a (suc zero) t refl T57sub)
      B1 : Deriv (imp (neg (leq a t)) (eqF X O))
      B1 = compI (nonzero_ge_one_imp (ap2 sub a t))
                 (prependEqLeft X (ap2 sub (ap1 s O) (ap2 sub a t)) O bridge_eq)
      h2 : Deriv (imp (neg (leq a t)) (leq X Y))
      h2 = compI B1 (leq_of_left_zero_imp X Y)
  in byCases (leq a t) (leq X Y) h1 h2

------------------------------------------------------------------------
-- Carried-hypothesis combinators (the Carneiro lift, one extra level):
-- by-cases / negation-introduction UNDER a carried object hypothesis  phi .

mapUnder1 :
  (phi : Formula) {Z Z' : Formula} ->
  Deriv (imp Z Z') -> Deriv (imp phi Z) -> Deriv (imp phi Z')
mapUnder1 phi zz' d = bComb (liftP phi zz') d

bCombThree :
  {P1 P2 P3 Q Rf : Formula} ->
  Deriv (imp P1 (imp P2 (imp P3 (imp Q Rf)))) ->
  Deriv (imp P1 (imp P2 (imp P3 Q))) ->
  Deriv (imp P1 (imp P2 (imp P3 Rf)))
bCombThree {P1} {P2} {P3} {Q} {Rf} D1 D2 =
  bCombTwo (bCombTwo (liftP P1 (liftP P2 (axS P3 Q Rf))) D1) D2

negIntroUnder :
  (phi P Q : Formula) ->
  Deriv (imp phi (imp P Q)) -> Deriv (imp phi (imp P (neg Q))) ->
  Deriv (imp phi (neg P))
negIntroUnder phi P Q h1 h2 =
  let a0 : Deriv (imp phi (imp P (imp Q (imp (neg Q) falseF))))
      a0 = liftP phi (liftP P (axExFalso Q falseF))
      a1 : Deriv (imp phi (imp P (imp (neg Q) falseF)))
      a1 = bCombTwo a0 h1
      a2 : Deriv (imp phi (imp P falseF))
      a2 = bCombTwo a1 h2
  in mapUnder1 phi (impFalseToNeg_imp P) a2

byCasesUnder :
  (phi A G : Formula) ->
  Deriv (imp phi (imp A G)) -> Deriv (imp phi (imp (neg A) G)) ->
  Deriv (imp phi G)
byCasesUnder phi A G h1 h2 =
  let e1 : Deriv (imp phi (imp (neg G) (neg A)))
      e1 = mapUnder1 phi (axContrapos A G) h1
      e2 : Deriv (imp phi (imp (neg G) (neg (neg A))))
      e2 = mapUnder1 phi (axContrapos (neg A) G) h2
      nng : Deriv (imp phi (neg (neg G)))
      nng = negIntroUnder phi (neg G) (neg A) e1 e2
  in mapUnder1 phi (DNE G) nng

------------------------------------------------------------------------
-- lt_from_le_neq with the disequality CARRIED (for use inside by-cases).
--   imp (neg (a=t)) (imp (a<=t) (s a <= t)) .

lt_from_le_neq_carried :
  (a t : Term) ->
  Deriv (imp (neg (eqF a t)) (imp (leq a t) (leq (ap1 s a) t)))
lt_from_le_neq_carried a t =
  let phi : Formula
      phi = neg (eqF a t)
      A : Formula
      A = leq a t
      B : Formula
      B = leq t a
      gU : Deriv (imp phi (imp (eqF a t) falseF))
      gU = bCombTwo (liftP phi (axExFalso (eqF a t) falseF)) (axK phi (eqF a t))
      ac3 : Deriv (imp phi (imp A (imp B (eqF a t))))
      ac3 = liftP phi (antisym_curry a t)
      gU2 : Deriv (imp phi (imp A (imp (eqF a t) falseF)))
      gU2 = mapUnder1 phi (axK (imp (eqF a t) falseF) A) gU
      gU3 : Deriv (imp phi (imp A (imp B (imp (eqF a t) falseF))))
      gU3 = mapUnder2 phi A (axK (imp (eqF a t) falseF) B) gU2
      bf : Deriv (imp phi (imp A (imp B falseF)))
      bf = bCombThree gU3 ac3
      toNeg : Deriv (imp phi (imp A (neg B)))
      toNeg = mapUnder2 phi A (impFalseToNeg_imp B) bf
  in mapUnder2 phi A (ruleInst2 zero t (suc zero) a refl strictTrich) toNeg

------------------------------------------------------------------------
-- eqInd_at_neq in imp-form (disequality carried).

eqInd_at_neq_imp :
  (a t : Term) -> Deriv (imp (neg (eqF a t)) (eqF (eqInd a t) O))
eqInd_at_neq_imp a t =
  let phi : Formula
      phi = neg (eqF a t)
      X : Term
      X = indLt a (ap1 s t)
      Y : Term
      Y = indLt a t
      ltc : Deriv (imp phi (imp (leq a t) (leq (ap1 s a) t)))
      ltc = lt_from_le_neq_carried a t
      A1U : Deriv (imp phi (imp (leq a t) (eqF X (ap1 s O))))
      A1U = mapUnder2 phi (leq a t)
              (compI (ruleInst2 zero (ap1 s a) (suc zero) t refl T81)
                     (indLt_at_lt_imp a (ap1 s t))) ltc
      A2U : Deriv (imp phi (imp (leq a t) (eqF Y (ap1 s O))))
      A2U = mapUnder2 phi (leq a t) (indLt_at_lt_imp a t) ltc
      h1U_tmp : Deriv (imp phi (imp (leq a t) (imp (eqF Y (ap1 s O)) (leq X Y))))
      h1U_tmp = bCombTwo (liftP phi (liftP (leq a t) (leq_both_one_imp X Y))) A1U
      h1U : Deriv (imp phi (imp (leq a t) (leq X Y)))
      h1U = bCombTwo h1U_tmp A2U
      h2U : Deriv (imp phi (imp (neg (leq a t)) (leq X Y)))
      h2U = liftP phi
              (compI (compI (nonzero_ge_one_imp (ap2 sub a t))
                            (prependEqLeft X (ap2 sub (ap1 s O) (ap2 sub a t)) O
                               (congR sub (ap1 s O)
                                  (ruleInst2 zero a (suc zero) t refl T57sub))))
                     (leq_of_left_zero_imp X Y))
  in byCasesUnder phi (leq a t) (leq X Y) h1U h2U

------------------------------------------------------------------------
------------------------------------------------------------------------
-- The equality-count  EqSum idx N t = sum_{j=0}^{N} [ idx j = t ]  and the
-- sum split  Csum N (s t) = sigma (Csum N t) (EqSum N t)  (Skolem Df. 2,
-- summed) plus  EqSum N t <= 1  under injectivity.

EqSum : Fun1 -> Nat -> Term -> Term
EqSum idx zero    t = eqInd (ap1 idx (natCode zero)) t
EqSum idx (suc N) t =
  ap2 sigma (EqSum idx N t) (eqInd (ap1 idx (natCode (suc N))) t)

-- Csum N (s t) = sigma (Csum N t) (EqSum N t)  by meta-induction on N,
-- using the per-term split + the four-term interchange.
Csum_succ_split :
  (idx : Fun1) (N : Nat) (t : Term) ->
  Deriv (eqF (Csum idx N (ap1 s t)) (ap2 sigma (Csum idx N t) (EqSum idx N t)))
Csum_succ_split idx zero t = indLt_succ_split (ap1 idx (natCode zero)) t
Csum_succ_split idx (suc M) t =
  let a : Term
      a = Csum idx M t
      b : Term
      b = EqSum idx M t
      c : Term
      c = indLt (ap1 idx (natCode (suc M))) t
      d : Term
      d = eqInd (ap1 idx (natCode (suc M))) t
      e_IH : Deriv (eqF (Csum idx M (ap1 s t)) (ap2 sigma a b))
      e_IH = Csum_succ_split idx M t
      e_pt : Deriv (eqF (indLt (ap1 idx (natCode (suc M))) (ap1 s t)) (ap2 sigma c d))
      e_pt = indLt_succ_split (ap1 idx (natCode (suc M))) t
      e1 : Deriv (eqF (ap2 sigma (Csum idx M (ap1 s t))
                                  (indLt (ap1 idx (natCode (suc M))) (ap1 s t)))
                       (ap2 sigma (ap2 sigma a b)
                                  (indLt (ap1 idx (natCode (suc M))) (ap1 s t))))
      e1 = congL sigma (indLt (ap1 idx (natCode (suc M))) (ap1 s t)) e_IH
      e2 : Deriv (eqF (ap2 sigma (ap2 sigma a b)
                                  (indLt (ap1 idx (natCode (suc M))) (ap1 s t)))
                       (ap2 sigma (ap2 sigma a b) (ap2 sigma c d)))
      e2 = congR sigma (ap2 sigma a b) e_pt
      e3 : Deriv (eqF (ap2 sigma (ap2 sigma a b) (ap2 sigma c d))
                       (ap2 sigma (ap2 sigma a c) (ap2 sigma b d)))
      e3 = interchange a b c d
  in ruleTrans e1 (ruleTrans e2 e3)

------------------------------------------------------------------------
-- Injectivity (contrapositive form):  distinct indices have distinct images.

InjBelow : Fun1 -> Nat -> Set
InjBelow idx N =
  (i j : Nat) -> NatLe i N -> NatLe j N -> (Eq i j -> Empty) ->
  Deriv (neg (eqF (ap1 idx (natCode i)) (ap1 idx (natCode j))))

------------------------------------------------------------------------
-- Meta-arithmetic on  NatLe  (the index bookkeeping).

notLeSucSelfNat : {n : Nat} -> NatLe (suc n) n -> Empty
notLeSucSelfNat {zero} ()
notLeSucSelfNat {suc m} (le-suc le) = notLeSucSelfNat {m} le

notEqSucOfLe : {j m : Nat} -> NatLe j m -> Eq j (suc m) -> Empty
notEqSucOfLe {j} {m} le eq =
  notLeSucSelfNat {m} (eqSubst (\ k -> NatLe k m) eq le)

------------------------------------------------------------------------
-- imp-form transitivity / zero-sum / leq-rewrite, carried under  phi .

under1_trans :
  {phi : Formula} {A B D : Term} ->
  Deriv (imp phi (eqF A B)) -> Deriv (imp phi (eqF B D)) ->
  Deriv (imp phi (eqF A D))
under1_trans {phi} {A} {B} {D} f g =
  bComb (compI (compI f (eqSymImp A B)) (ax_eqTrans B A D)) g

sigma_both_zero_imp :
  (phi : Formula) (A B : Term) ->
  Deriv (imp phi (eqF A O)) -> Deriv (imp phi (eqF B O)) ->
  Deriv (imp phi (eqF (ap2 sigma A B) O))
sigma_both_zero_imp phi A B ihA ihB =
  let r1 : Deriv (imp phi (eqF (ap2 sigma A B) (ap2 sigma O B)))
      r1 = compI ihA (ax_eqCongL sigma A O B)
      r2 : Deriv (imp phi (eqF (ap2 sigma O B) (ap2 sigma O O)))
      r2 = compI ihB (ax_eqCongR sigma B O O)
      r3 : Deriv (imp phi (eqF (ap2 sigma O O) O))
      r3 = liftP phi (T33 O)
  in under1_trans (under1_trans r1 r2) r3

-- from  a = b  conclude  leq a c , given  leq b c   (imp-form).
leq_eqL_imp :
  (a b c : Term) -> Deriv (leq b c) -> Deriv (imp (eqF a b) (leq a c))
leq_eqL_imp a b c bc =
  compI (ax_eqCongL sub a b c)
        (appendEqRight (ap2 sub a c) (ap2 sub b c) O bc)

-- sigma O x = x .
sigma_O_left : (x : Term) -> Deriv (eqF (ap2 sigma O x) x)
sigma_O_left x = ruleTrans (sigma_comm O x) (T33 x)

------------------------------------------------------------------------
-- a /= b  and  b = t  imply  a /= t   (imp-form, the disequality of A/B
-- carried as a fixed Deriv, the hit  b = t  as the antecedent).

neq_via_hit_imp :
  (a b t : Term) ->
  Deriv (neg (eqF a b)) -> Deriv (imp (eqF b t) (neg (eqF a t)))
neq_via_hit_imp a b t nAB =
  let phi : Formula
      phi = eqF b t
      J : Deriv (imp (eqF a t) (imp (eqF t b) (eqF a b)))
      J = compI (eqSymImp a t) (ax_eqTrans t a b)
      phiToTB : Deriv (imp phi (eqF t b))
      phiToTB = eqSymImp b t
      J' : Deriv (imp phi (imp (eqF a t) (imp (eqF t b) (eqF a b))))
      J' = liftP phi J
      phiToTB' : Deriv (imp phi (imp (eqF a t) (eqF t b)))
      phiToTB' = mapUnder1 phi (axK (eqF t b) (eqF a t)) phiToTB
      PAB : Deriv (imp phi (imp (eqF a t) (eqF a b)))
      PAB = bCombTwo J' phiToTB'
  in negIntroUnder phi (eqF a t) (eqF a b) PAB
       (liftP phi (liftP (eqF a t) nAB))

------------------------------------------------------------------------
-- EqSum is 0 when every summand is 0 (imp-form, family carried under phi).

EqSum_zero_imp :
  (idx : Fun1) (M : Nat) (t : Term) (phi : Formula) ->
  ((j : Nat) -> NatLe j M ->
     Deriv (imp phi (eqF (eqInd (ap1 idx (natCode j)) t) O))) ->
  Deriv (imp phi (eqF (EqSum idx M t) O))
EqSum_zero_imp idx zero t phi fam = fam zero (le-zero zero)
EqSum_zero_imp idx (suc M) t phi fam =
  let ih : Deriv (imp phi (eqF (EqSum idx M t) O))
      ih = EqSum_zero_imp idx M t phi (\ j leJM -> fam j (le-suc-right leJM))
      tail : Deriv (imp phi (eqF (eqInd (ap1 idx (natCode (suc M))) t) O))
      tail = fam (suc M) (le-refl (suc M))
  in sigma_both_zero_imp phi (EqSum idx M t)
       (eqInd (ap1 idx (natCode (suc M))) t) ih tail

-- under the "hit"  idx (s M) = t , the prefix sum  EqSum M t  is 0
-- (injectivity: every earlier index has a different image, so /= t).
prefix_no_hit_imp :
  (idx : Fun1) (N : Nat) -> InjBelow idx N -> (t : Term) (M : Nat) ->
  NatLe (suc M) N ->
  Deriv (imp (eqF (ap1 idx (natCode (suc M))) t) (eqF (EqSum idx M t) O))
prefix_no_hit_imp idx N inj t M leSucMN =
  EqSum_zero_imp idx M t (eqF (ap1 idx (natCode (suc M))) t)
    (\ j leJM ->
       let idxjNeIdxSucM :
             Deriv (neg (eqF (ap1 idx (natCode j)) (ap1 idx (natCode (suc M)))))
           idxjNeIdxSucM =
             inj j (suc M) (le-trans leJM (le-pred-right leSucMN)) leSucMN
                 (notEqSucOfLe leJM)
       in compI (neq_via_hit_imp (ap1 idx (natCode j))
                                  (ap1 idx (natCode (suc M))) t idxjNeIdxSucM)
                (eqInd_at_neq_imp (ap1 idx (natCode j)) t))

------------------------------------------------------------------------
-- EqSum N t <= 1  under injectivity, by induction on the partial bound M.

EqSum_le_one :
  (idx : Fun1) (N : Nat) -> InjBelow idx N -> (t : Term) (M : Nat) ->
  NatLe M N -> Deriv (leq (EqSum idx M t) (ap1 s O))
EqSum_le_one idx N inj t zero leMN = eqInd_le_one (ap1 idx (natCode zero)) t
EqSum_le_one idx N inj t (suc M) leSucMN =
  let hit : Formula
      hit = eqF (ap1 idx (natCode (suc M))) t
      EM : Term
      EM = EqSum idx M t
      newd : Term
      newd = eqInd (ap1 idx (natCode (suc M))) t
      ihM : Deriv (leq EM (ap1 s O))
      ihM = EqSum_le_one idx N inj t M (le-pred-right leSucMN)
      -- h1 (hit):  prefix is 0, so EqSum (suc M) = sigma O newd = newd <= 1 .
      h1_cong : Deriv (imp (eqF EM O) (eqF (ap2 sigma EM newd) newd))
      h1_cong = compI (ax_eqCongL sigma EM O newd)
                      (appendEqRight (ap2 sigma EM newd) (ap2 sigma O newd) newd
                                     (sigma_O_left newd))
      h1_inner : Deriv (imp (eqF EM O) (leq (ap2 sigma EM newd) (ap1 s O)))
      h1_inner = compI h1_cong
                       (leq_eqL_imp (ap2 sigma EM newd) newd (ap1 s O)
                                    (eqInd_le_one (ap1 idx (natCode (suc M))) t))
      h1 : Deriv (imp hit (leq (ap2 sigma EM newd) (ap1 s O)))
      h1 = compI (prefix_no_hit_imp idx N inj t M leSucMN) h1_inner
      -- h2 (miss):  newd = 0, so EqSum (suc M) = sigma EM O = EM <= 1 [IH].
      h2_cong : Deriv (imp (eqF newd O) (eqF (ap2 sigma EM newd) EM))
      h2_cong = compI (ax_eqCongR sigma newd O EM)
                      (appendEqRight (ap2 sigma EM newd) (ap2 sigma EM O) EM
                                     (T33 EM))
      h2_inner : Deriv (imp (eqF newd O) (leq (ap2 sigma EM newd) (ap1 s O)))
      h2_inner = compI h2_cong
                       (leq_eqL_imp (ap2 sigma EM newd) EM (ap1 s O) ihM)
      h2 : Deriv (imp (neg hit) (leq (ap2 sigma EM newd) (ap1 s O)))
      h2 = compI (eqInd_at_neq_imp (ap1 idx (natCode (suc M))) t) h2_inner
  in byCases hit (leq (ap2 sigma EM newd) (ap1 s O)) h1 h2

------------------------------------------------------------------------
------------------------------------------------------------------------
-- The unit step and the arbitrary-injection pigeonhole.

-- sigma X Y <= s X  whenever  Y <= s O  (by-cases on  Y = O ).
sigma_le_succ :
  (X Y : Term) -> Deriv (leq Y (ap1 s O)) -> Deriv (leq (ap2 sigma X Y) (ap1 s X))
sigma_le_succ X Y leY1 =
  let leqXsX : Deriv (leq X (ap1 s X))
      leqXsX = mp (ruleInst2 zero X (suc zero) X refl T81) (ruleInst zero X T73)
      -- h1 :  Y = O  ->  sigma X Y = X <= s X .
      h1cong : Deriv (imp (eqF Y O) (eqF (ap2 sigma X Y) X))
      h1cong = compI (ax_eqCongR sigma Y O X)
                     (appendEqRight (ap2 sigma X Y) (ap2 sigma X O) X (T33 X))
      h1 : Deriv (imp (eqF Y O) (leq (ap2 sigma X Y) (ap1 s X)))
      h1 = compI h1cong (leq_eqL_imp (ap2 sigma X Y) X (ap1 s X) leqXsX)
      -- h2 :  Y /= O , Y <= s O  =>  Y = s O  =>  sigma X Y = s X .
      YeqSO : Deriv (imp (neg (eqF Y O)) (eqF Y (ap1 s O)))
      YeqSO =
        compI (mp (axContrapos (leq Y O) (eqF Y O))
                  (prependEqLeft Y (ap2 sub Y O) O (ruleSym (T_sub_O Y))))
              (mp (ruleInst2 zero Y (suc zero) O refl T82) leY1)
      h2cong : Deriv (imp (eqF Y (ap1 s O)) (eqF (ap2 sigma X Y) (ap1 s X)))
      h2cong = compI (ax_eqCongR sigma Y (ap1 s O) X)
                     (appendEqRight (ap2 sigma X Y) (ap2 sigma X (ap1 s O)) (ap1 s X)
                                    (sigma_x_one X))
      h2 : Deriv (imp (neg (eqF Y O)) (leq (ap2 sigma X Y) (ap1 s X)))
      h2 = compI YeqSO
                 (compI h2cong
                        (leq_eqL_imp (ap2 sigma X Y) (ap1 s X) (ap1 s X)
                                     (ruleInst zero (ap1 s X) T73)))
  in byCases (eqF Y O) (leq (ap2 sigma X Y) (ap1 s X)) h1 h2

-- THE UNIT STEP:  C(t+1) <= s (C t)  at  t = natCode k , consuming
-- injectivity through  EqSum_le_one .
unit_step : (idx : Fun1) (N : Nat) -> InjBelow idx N -> UnitStep idx N
unit_step idx N inj k leKN =
  let t : Term
      t = natCode k
      split : Deriv (eqF (Csum idx N (ap1 s t))
                          (ap2 sigma (Csum idx N t) (EqSum idx N t)))
      split = Csum_succ_split idx N t
      eqle : Deriv (leq (EqSum idx N t) (ap1 s O))
      eqle = EqSum_le_one idx N inj t N (le-refl N)
      sls : Deriv (leq (ap2 sigma (Csum idx N t) (EqSum idx N t))
                        (ap1 s (Csum idx N t)))
      sls = sigma_le_succ (Csum idx N t) (EqSum idx N t) eqle
  in leq_eqL (Csum idx N (ap1 s t))
             (ap2 sigma (Csum idx N t) (EqSum idx N t))
             (ap1 s (Csum idx N t))
             split sls

------------------------------------------------------------------------
-- THE THEOREM.  No injection of  {0,...,N}  into  {0,...,N-1}  exists:
-- if  idx  maps every  j <= N  below  N  (MapsBelow) and is injective on
-- that range (InjBelow), we derive  falseF .  This is the
-- arbitrary-injection pigeonhole, the Gate-1 (a)-fork combinatorial core.

no_injection_into_smaller :
  (idx : Fun1) (N : Nat) -> MapsBelow idx N -> InjBelow idx N -> Deriv falseF
no_injection_into_smaller idx N mb inj =
  php_via_unit_step idx N mb (unit_step idx N inj)
