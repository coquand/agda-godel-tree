{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CountingObj -- the OBJECT-N arbitrary-injection pigeonhole
-- (Kritchman-Raz Phase KR-C / "Spike C").
--
-- BRA4.Counting already proves the arbitrary-injection pigeonhole
-- (no_injection_into_smaller), but it is META in the codomain bound N:
-- the count  Csum idx N t  is built by Agda recursion on the meta  Nat N
-- into an N-deep  sigma-tree, and the conclusion needs the unary  natCode N .
-- For the Berry/KR use  N = 2^{c.ell}  is exponential in the length budget,
-- so BOTH the N-fold meta term and  natCode N  are non-constructible.
--
-- This file removes the meta-N dependence (the "(P2) upgrade").  The count
-- is an OBJECT functor  csumObj idx : Fun2 ,
--
--   ap2 (csumObj idx) t m  "="  sum_{j=0}^{m} indLt(idx j, t) ,
--
-- defined once via the BRA recursor  R  (constant size, no meta unfolding),
-- and every fact about it is an OBJECT  ruleIndNat  on the index, instantiated
-- ONCE at the (closed, Bin-compressed)  N  by  ruleInst .  The threshold  t
-- stays an OPEN term (var 0) throughout -- mirroring  SpikeB.linearBound_obj
-- and reusing the threshold-uniform per-term arithmetic of BRA4.Counting
-- verbatim (indLt_succ_split / eqInd_le_one / eqInd_at_neq_imp / sigma_le_succ
-- / interchange / the by-cases combinators -- all universal in the Term t).
--
-- KEY OBSERVATION that makes the port cheap: the Counting lemmas are already
-- UNIVERSAL IN t and only meta in N, so the genuinely new work is just the
-- index recursion redone as object  ruleIndNat .  Two combinator facts make
-- the recursors expressible: an arbitrary  Fun1 idx  carries no free variable
-- (so it is substitution-invariant), and the constant  s(idx O)  is
--  compose1U s (compose1U idx o)  (since  o t = O  for every t).
--
-- Sigma_1-FREE: pure BRA arithmetic, no  thmT , no provability.

module BRA4.CountingObj where

open import BRA4.Base
open import BRA4.PHP
  using ( indLt ; indLt_at_O ; indLt_at_lt ; byCases ; leq_eqL ; leq_substL
        ; succ_mono )
open import BRA4.Counting
  using ( eqInd ; indLt_succ_split ; interchange ; sigma_x_one ; leqZ
        ; eqInd_le_one ; eqInd_at_neq_imp ; sigma_le_succ ; sigma_O_left
        ; leq_eqL_imp ; sigma_both_zero_imp ; neq_via_hit_imp ; leq_eqR
        ; byCasesUnder ; mapUnder1 ; mapUnder2 ; bComb2 ; indLt_le_one
        ; indLt_at_lt_imp ; bCombThree ; impFalseToNeg_imp ; under1_trans )
open import BRA4.SpikeB using ( succ_mono_imp ; leq_trans_imp )
open import BRA4.Code   using ( falseF )

open import BRA4.LeqMono using ( leq_trans )

open import BRA3.Church       using ( sub ; sigma ; pi ; T33 )
open import BRA3.ChurchLeq    using ( leq ; T76 )
open import BRA3.ChurchT73    using ( T73 )
open import BRA3.ChurchT81    using ( T81 )
open import BRA3.ChurchT87    using ( notLeqSucSelf )
open import BRA3.RuleInst2    using ( ruleInst2 )
open import BRA3.Logic        using ( eqSymImp ; prependEqLeft ; appendEqRight )
open import BRA3.Contrapositive using
  ( axExFalso ; bComb ; bCombTwo ; liftP ; compI ; axContrapos ; DNE )

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 1.  The object count functors.
--
-- We package the strict-less-than indicator and the equality indicator as
-- Fun2's so the summand of each recursor is a single composition.

-- indLtF :  ap2 indLtF a t = indLt a t = sub (s O) (sub (s a) t) .
indLtF : Fun2
indLtF = Fan (Lift1 (constN (suc zero))) (Fan (Lift1 s) v sub) sub

-- indLtStF :  ap2 indLtStF a t = indLt a (s t) = sub (s O) (sub (s a) (s t)) .
indLtStF : Fun2
indLtStF = Fan (Lift1 (constN (suc zero))) (Fan (Lift1 s) (Lift2 s) sub) sub

-- eqIndF :  ap2 eqIndF a t = eqInd a t = sub (indLt a (s t)) (indLt a t) .
eqIndF : Fun2
eqIndF = Fan indLtStF indLtF sub

------------------------------------------------------------------------
-- Evaluation lemmas for the indicator functors (universal in a, t).

indLtF_eq : (a t : Term) -> Deriv (eqF (ap2 indLtF a t) (indLt a t))
indLtF_eq a t =
  let e1 : Deriv (eqF (ap2 indLtF a t)
                       (ap2 sub (ap2 (Lift1 (constN (suc zero))) a t)
                                (ap2 (Fan (Lift1 s) v sub) a t)))
      e1 = axFan (Lift1 (constN (suc zero))) (Fan (Lift1 s) v sub) sub a t

      eHead : Deriv (eqF (ap2 (Lift1 (constN (suc zero))) a t) (ap1 s O))
      eHead = ruleTrans (axLift (constN (suc zero)) a t) (constN_eq (suc zero) a)

      eInner : Deriv (eqF (ap2 (Fan (Lift1 s) v sub) a t)
                           (ap2 sub (ap1 s a) t))
      eInner =
        ruleTrans (axFan (Lift1 s) v sub a t)
          (ruleTrans (congL sub (ap2 v a t) (axLift s a t))
                     (congR sub (ap1 s a) (ax_v a t)))

      e2 : Deriv (eqF (ap2 sub (ap2 (Lift1 (constN (suc zero))) a t)
                               (ap2 (Fan (Lift1 s) v sub) a t))
                       (ap2 sub (ap1 s O) (ap2 sub (ap1 s a) t)))
      e2 = ruleTrans (congL sub (ap2 (Fan (Lift1 s) v sub) a t) eHead)
                     (congR sub (ap1 s O) eInner)
  in ruleTrans e1 e2

indLtStF_eq : (a t : Term) -> Deriv (eqF (ap2 indLtStF a t) (indLt a (ap1 s t)))
indLtStF_eq a t =
  let e1 : Deriv (eqF (ap2 indLtStF a t)
                       (ap2 sub (ap2 (Lift1 (constN (suc zero))) a t)
                                (ap2 (Fan (Lift1 s) (Lift2 s) sub) a t)))
      e1 = axFan (Lift1 (constN (suc zero))) (Fan (Lift1 s) (Lift2 s) sub) sub a t

      eHead : Deriv (eqF (ap2 (Lift1 (constN (suc zero))) a t) (ap1 s O))
      eHead = ruleTrans (axLift (constN (suc zero)) a t) (constN_eq (suc zero) a)

      eInner : Deriv (eqF (ap2 (Fan (Lift1 s) (Lift2 s) sub) a t)
                           (ap2 sub (ap1 s a) (ap1 s t)))
      eInner =
        ruleTrans (axFan (Lift1 s) (Lift2 s) sub a t)
          (ruleTrans (congL sub (ap2 (Lift2 s) a t) (axLift s a t))
                     (congR sub (ap1 s a) (axLift2 s a t)))

      e2 : Deriv (eqF (ap2 sub (ap2 (Lift1 (constN (suc zero))) a t)
                               (ap2 (Fan (Lift1 s) (Lift2 s) sub) a t))
                       (ap2 sub (ap1 s O) (ap2 sub (ap1 s a) (ap1 s t))))
      e2 = ruleTrans (congL sub (ap2 (Fan (Lift1 s) (Lift2 s) sub) a t) eHead)
                     (congR sub (ap1 s O) eInner)
  in ruleTrans e1 e2

eqIndF_eq : (a t : Term) -> Deriv (eqF (ap2 eqIndF a t) (eqInd a t))
eqIndF_eq a t =
  let e1 : Deriv (eqF (ap2 eqIndF a t)
                       (ap2 sub (ap2 indLtStF a t) (ap2 indLtF a t)))
      e1 = axFan indLtStF indLtF sub a t

      e2 : Deriv (eqF (ap2 sub (ap2 indLtStF a t) (ap2 indLtF a t))
                       (ap2 sub (indLt a (ap1 s t)) (indLt a t)))
      e2 = ruleTrans (congL sub (ap2 indLtF a t) (indLtStF_eq a t))
                     (congR sub (indLt a (ap1 s t)) (indLtF_eq a t))
  in ruleTrans e1 e2

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 2.  The object sum recursor.
--
-- For any indicator  indF : Fun2  and arbitrary index map  idx : Fun1 ,
--
--   sumRec indF idx : Fun2 ,
--   ap2 (sumRec indF idx) t m  =  sum_{j=0}^{m} indF(idx j, t) ,
--
-- via the BRA recursor  R , recursing on the SECOND argument (the index
-- range  m ), with the threshold  t  as the parameter.  Base summand is at
-- index 0 (the term  idx O = idx (o t) , constant in t); the step summand is
-- at the running top index  s m  (recovered as  idx (s (Snd q))  from the
-- packaged input  q = pi t m ).

bodyF1 : Fun2 -> Fun1 -> Fun1
bodyF1 indF idx = C indF (compose1U idx o) u

stepSummand : Fun2 -> Fun1 -> Fun1
stepSummand indF idx = C indF (compose1U idx (compose1U s Snd)) Fst

sumRec : Fun2 -> Fun1 -> Fun2
sumRec indF idx =
  R (bodyF1 indF idx) (Fan v (Lift1 (stepSummand indF idx)) sigma) pi

------------------------------------------------------------------------
-- Generic Fan-step evaluation:  Fan v (Lift1 F) sigma  applied to a
-- packaged input  q  and accumulator  prev  is  sigma prev (F q) .

gstep_eq :
  (F : Fun1) (q prev : Term) ->
  Deriv (eqF (ap2 (Fan v (Lift1 F) sigma) q prev) (ap2 sigma prev (ap1 F q)))
gstep_eq F q prev =
  ruleTrans (axFan v (Lift1 F) sigma q prev)
    (ruleTrans (congL sigma (ap2 (Lift1 F) q prev) (ax_v q prev))
               (congR sigma prev (axLift F q prev)))

------------------------------------------------------------------------
-- Base / step summand evaluations.

bodyF1_eq :
  (indF : Fun2) (idx : Fun1) (t : Term) ->
  Deriv (eqF (ap1 (bodyF1 indF idx) t) (ap2 indF (ap1 idx O) t))
bodyF1_eq indF idx t =
  let s1 : Deriv (eqF (ap1 (bodyF1 indF idx) t)
                       (ap2 indF (ap1 (compose1U idx o) t) (ap1 u t)))
      s1 = ax_C indF (compose1U idx o) u t

      headEq : Deriv (eqF (ap1 (compose1U idx o) t) (ap1 idx O))
      headEq = ruleTrans (axComp idx o t) (cong1 idx (ax_o t))

      s2 : Deriv (eqF (ap2 indF (ap1 (compose1U idx o) t) (ap1 u t))
                       (ap2 indF (ap1 idx O) t))
      s2 = ruleTrans (congL indF (ap1 u t) headEq)
                     (congR indF (ap1 idx O) (ax_u t))
  in ruleTrans s1 s2

stepSummand_at_pi :
  (indF : Fun2) (idx : Fun1) (t m : Term) ->
  Deriv (eqF (ap1 (stepSummand indF idx) (ap2 pi t m))
              (ap2 indF (ap1 idx (ap1 s m)) t))
stepSummand_at_pi indF idx t m =
  let s1 : Deriv (eqF (ap1 (stepSummand indF idx) (ap2 pi t m))
                       (ap2 indF (ap1 (compose1U idx (compose1U s Snd)) (ap2 pi t m))
                                 (ap1 Fst (ap2 pi t m))))
      s1 = ax_C indF (compose1U idx (compose1U s Snd)) Fst (ap2 pi t m)

      inner : Deriv (eqF (ap1 (compose1U s Snd) (ap2 pi t m)) (ap1 s m))
      inner = ruleTrans (axComp s Snd (ap2 pi t m)) (cong1 s (axSnd t m))

      headEq : Deriv (eqF (ap1 (compose1U idx (compose1U s Snd)) (ap2 pi t m))
                           (ap1 idx (ap1 s m)))
      headEq = ruleTrans (axComp idx (compose1U s Snd) (ap2 pi t m)) (cong1 idx inner)

      s2 : Deriv (eqF (ap2 indF (ap1 (compose1U idx (compose1U s Snd)) (ap2 pi t m))
                                (ap1 Fst (ap2 pi t m)))
                       (ap2 indF (ap1 idx (ap1 s m)) t))
      s2 = ruleTrans (congL indF (ap1 Fst (ap2 pi t m)) headEq)
                     (congR indF (ap1 idx (ap1 s m)) (axFst t m))
  in ruleTrans s1 s2

------------------------------------------------------------------------
-- The generic recursor unfold lemmas.

sumRec_at_O :
  (indF : Fun2) (idx : Fun1) (t : Term) ->
  Deriv (eqF (ap2 (sumRec indF idx) t O) (ap2 indF (ap1 idx O) t))
sumRec_at_O indF idx t =
  ruleTrans (ax_R_base (bodyF1 indF idx)
                       (Fan v (Lift1 (stepSummand indF idx)) sigma) pi t)
            (bodyF1_eq indF idx t)

sumRec_succ :
  (indF : Fun2) (idx : Fun1) (t m : Term) ->
  Deriv (eqF (ap2 (sumRec indF idx) t (ap1 s m))
              (ap2 sigma (ap2 (sumRec indF idx) t m)
                         (ap2 indF (ap1 idx (ap1 s m)) t)))
sumRec_succ indF idx t m =
  let prev : Term
      prev = ap2 (sumRec indF idx) t m

      rstep : Deriv (eqF (ap2 (sumRec indF idx) t (ap1 s m))
                          (ap2 (Fan v (Lift1 (stepSummand indF idx)) sigma)
                               (ap2 pi t m) prev))
      rstep = ax_R_step (bodyF1 indF idx)
                        (Fan v (Lift1 (stepSummand indF idx)) sigma) pi t m

      gstep : Deriv (eqF (ap2 (Fan v (Lift1 (stepSummand indF idx)) sigma)
                              (ap2 pi t m) prev)
                          (ap2 sigma prev (ap1 (stepSummand indF idx) (ap2 pi t m))))
      gstep = gstep_eq (stepSummand indF idx) (ap2 pi t m) prev
  in ruleTrans rstep
       (ruleTrans gstep
         (congR sigma prev (stepSummand_at_pi indF idx t m)))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 3.  The two concrete count functors and their recursion equations.

-- csumObj idx (t, m) = sum_{j=0}^{m} indLt(idx j, t)  -- the count below t.
csumObj : Fun1 -> Fun2
csumObj idx = sumRec indLtF idx

-- eqSumObj idx (t, m) = sum_{j=0}^{m} eqInd(idx j, t)  -- the equality count.
eqSumObj : Fun1 -> Fun2
eqSumObj idx = sumRec eqIndF idx

csum_at_O :
  (idx : Fun1) (t : Term) ->
  Deriv (eqF (ap2 (csumObj idx) t O) (indLt (ap1 idx O) t))
csum_at_O idx t =
  ruleTrans (sumRec_at_O indLtF idx t) (indLtF_eq (ap1 idx O) t)

csum_succ :
  (idx : Fun1) (t m : Term) ->
  Deriv (eqF (ap2 (csumObj idx) t (ap1 s m))
              (ap2 sigma (ap2 (csumObj idx) t m) (indLt (ap1 idx (ap1 s m)) t)))
csum_succ idx t m =
  ruleTrans (sumRec_succ indLtF idx t m)
            (congR sigma (ap2 (csumObj idx) t m) (indLtF_eq (ap1 idx (ap1 s m)) t))

eqsum_at_O :
  (idx : Fun1) (t : Term) ->
  Deriv (eqF (ap2 (eqSumObj idx) t O) (eqInd (ap1 idx O) t))
eqsum_at_O idx t =
  ruleTrans (sumRec_at_O eqIndF idx t) (eqIndF_eq (ap1 idx O) t)

eqsum_succ :
  (idx : Fun1) (t m : Term) ->
  Deriv (eqF (ap2 (eqSumObj idx) t (ap1 s m))
              (ap2 sigma (ap2 (eqSumObj idx) t m) (eqInd (ap1 idx (ap1 s m)) t)))
eqsum_succ idx t m =
  ruleTrans (sumRec_succ eqIndF idx t m)
            (congR sigma (ap2 (eqSumObj idx) t m) (eqIndF_eq (ap1 idx (ap1 s m)) t))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 4.  Object leq + bounded-induction infrastructure.

-- leq N N  (reflexivity at any term).
leqNN : (x : Term) -> Deriv (leq x x)
leqNN x = ruleInst zero x T73

-- x <= s x .
leq_x_sx : (x : Term) -> Deriv (leq x (ap1 s x))
leq_x_sx x = mp (ruleInst2 zero x (suc zero) x refl T81) (leqNN x)

-- s a <= b  implies  a <= b   (imp-form predecessor on the left).
le_pred_imp : (a b : Term) -> Deriv (imp (leq (ap1 s a) b) (leq a b))
le_pred_imp a b = mp (leq_trans_imp a (ap1 s a) b) (leq_x_sx a)

-- Coerce a Deriv along the closedness of N: rewrite N to substT k b N
-- (needed to feed a hand-built base/step into ruleIndNat, whose substF
-- leaves a stuck  substT k b N  when N is an abstract closed Term).
closeCoe :
  {N : Term} -> Closed N -> (k : Nat) (b : Term) (mot : Term -> Formula) ->
  Deriv (mot N) -> Deriv (mot (substT k b N))
closeCoe {N} clN k b mot d =
  eqSubst (\ X -> Deriv (mot X)) (eqSym (Closed.closedAt clN k b)) d

-- Transitivity of an equation under TWO carried hypotheses.
trans2 :
  (phi psi : Formula) (X Y Z : Term) ->
  Deriv (imp phi (imp psi (eqF X Y))) ->
  Deriv (imp phi (imp psi (eqF Y Z))) ->
  Deriv (imp phi (imp psi (eqF X Z)))
trans2 phi psi X Y Z exy eyz =
  let -- ax_eqTrans is the common-LEFT form  (x=y) -> (x=z) -> (y=z) ,
      -- so standard transitivity needs  Y=X  (symmetry of exy) first.
      e_yx : Deriv (imp phi (imp psi (eqF Y X)))
      e_yx = mapUnder2 phi psi (eqSymImp X Y) exy
      lifted : Deriv (imp phi (imp psi (imp (eqF Y X) (imp (eqF Y Z) (eqF X Z)))))
      lifted = liftP phi (liftP psi (ax_eqTrans Y X Z))
      step1 : Deriv (imp phi (imp psi (imp (eqF Y Z) (eqF X Z))))
      step1 = bCombTwo lifted e_yx
  in bCombTwo step1 eyz

-- The generic carried-bound induction STEP assembler:  from
--   shrink    : (s m <= N) -> (m <= N)
--   realStep  : (s m <= N) -> Q(m) -> Q(s m)
-- build the ruleIndNat step  imp (imp (m<=N) Q(m)) (imp (s m<=N) Q(s m)) .
indBoundStep :
  (m N : Term) (Q Qs : Formula) ->
  Deriv (imp (leq (ap1 s m) N) (leq m N)) ->
  Deriv (imp (leq (ap1 s m) N) (imp Q Qs)) ->
  Deriv (imp (imp (leq m N) Q) (imp (leq (ap1 s m) N) Qs))
indBoundStep m N Q Qs shrink realStep =
  let phi : Formula
      phi = imp (leq m N) Q
      psi : Formula
      psi = leq (ap1 s m) N
      e_phiK : Deriv (imp phi (imp psi phi))
      e_phiK = axK phi psi
      e_leqmN : Deriv (imp phi (imp psi (leq m N)))
      e_leqmN = liftP phi shrink
      e_Q : Deriv (imp phi (imp psi Q))
      e_Q = bCombTwo e_phiK e_leqmN
      realStep' : Deriv (imp phi (imp psi (imp Q Qs)))
      realStep' = liftP phi realStep
  in bCombTwo realStep' e_Q

-- Object MapsBelow / InjBelow: meta-families over an index TERM.
MapsBelowObj : Fun1 -> Term -> Set
MapsBelowObj idx N =
  (j : Term) -> Deriv (imp (leq j N) (leq (ap1 s (ap1 idx j)) N))

-- Object BOUNDED injectivity:  i < j  AND  j <= N  imply  idx i /= idx j .
-- This is the KR-supplied notion -- con_inj only constrains NAMED
-- (compressible) numbers <= N, so injectivity is naturally bounded; the
-- larger index j carries  leq j N  (and  i < j  gives  i <= N  for free).
-- Imp-form (curried) so it composes under carried hypotheses.  The bound on
-- the larger index threads through  prefix_zero_obj / eqsum_le_one_obj  as a
-- carried hypothesis (topB), instantiated at  N  in  unitStep_obj .
InjBelowObj : Fun1 -> Term -> Set
InjBelowObj idx N =
  (i j : Term) ->
  Deriv (imp (leq (ap1 s i) j)
             (imp (leq j N) (neg (eqF (ap1 idx i) (ap1 idx j)))))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 5.  C(0) = 0  (the count at threshold 0), object form.
--
--   ap2 (csumObj idx) O m = O   for all index bounds m  (open in var 0),
-- by object  ruleIndNat  on the index  var 0 .  No N, no MapsBelow.

c0_obj : (idx : Fun1) -> Deriv (eqF (ap2 (csumObj idx) O (var zero)) O)
c0_obj idx = ruleIndNat zero {P = Pc} base step
  where
    Pc : Formula
    Pc = eqF (ap2 (csumObj idx) O (var zero)) O

    base : Deriv (eqF (ap2 (csumObj idx) O O) O)
    base = ruleTrans (csum_at_O idx O) (indLt_at_O (ap1 idx O))

    step : Deriv (imp Pc (eqF (ap2 (csumObj idx) O (ap1 s (var zero))) O))
    step =
      let A : Term
          A = ap2 (csumObj idx) O (var zero)
          d : Term
          d = indLt (ap1 idx (ap1 s (var zero))) O
          LHS : Term
          LHS = ap2 (csumObj idx) O (ap1 s (var zero))

          d_eq : Deriv (eqF d O)
          d_eq = indLt_at_O (ap1 idx (ap1 s (var zero)))

          r1 : Deriv (imp (eqF A O) (eqF (ap2 sigma A d) (ap2 sigma O d)))
          r1 = ax_eqCongL sigma A O d

          r2 : Deriv (eqF (ap2 sigma O d) O)
          r2 = ruleTrans (sigma_O_left d) d_eq

          inner : Deriv (imp (eqF A O) (eqF (ap2 sigma A d) O))
          inner = compI r1 (appendEqRight (ap2 sigma A d) (ap2 sigma O d) O r2)

          succEq : Deriv (eqF LHS (ap2 sigma A d))
          succEq = csum_succ idx O (var zero)
      in compI inner (prependEqLeft LHS (ap2 sigma A d) O succEq)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 6.  C(N) = N + 1  (the range bound), object form.
--
--   ap2 (csumObj idx) N N = s N   under object MapsBelow:  every index
-- j <= N has  idx j < N , so every indicator is 1 and the sum over
-- j = 0..N is  N + 1 .  By object  ruleIndNat  on the index (carrying the
-- bound  j <= N  through the step), instantiated at  N .

crange_obj :
  (idx : Fun1) (N : Term) -> Closed N -> MapsBelowObj idx N ->
  Deriv (eqF (ap2 (csumObj idx) N N) (ap1 s N))
crange_obj idx N clN mb = mp finalCoerced (leqNN N)
  where
    Pc : Formula
    Pc = imp (leq (var zero) N)
             (eqF (ap2 (csumObj idx) N (var zero)) (ap1 s (var zero)))

    -- base:  imp (leq O N) (csumObj idx N O = s O) , then coerce N.
    baseReal : Deriv (imp (leq O N)
                          (eqF (ap2 (csumObj idx) N O) (ap1 s O)))
    baseReal =
      compI (compI (mb O) (indLt_at_lt_imp (ap1 idx O) N))
            (prependEqLeft (ap2 (csumObj idx) N O) (indLt (ap1 idx O) N)
                           (ap1 s O) (csum_at_O idx N))

    base : Deriv (substF zero O Pc)
    base = closeCoe clN zero O
             (\ X -> imp (leq O X) (eqF (ap2 (csumObj idx) X O) (ap1 s O)))
             baseReal

    -- step:  the carried-bound induction step, then coerce N in the consequent.
    realStep :
      Deriv (imp (leq (ap1 s (var zero)) N)
                 (imp (eqF (ap2 (csumObj idx) N (var zero)) (ap1 s (var zero)))
                      (eqF (ap2 (csumObj idx) N (ap1 s (var zero)))
                           (ap1 s (ap1 s (var zero))))))
    realStep =
      let m : Term
          m = var zero
          sm : Term
          sm = ap1 s (var zero)
          A : Term
          A = ap2 (csumObj idx) N m
          Asm : Term
          Asm = ap2 (csumObj idx) N sm
          d : Term
          d = indLt (ap1 idx sm) N
          phi : Formula
          phi = leq sm N
          psi : Formula
          psi = eqF A sm

          hitInd : Deriv (imp phi (eqF d (ap1 s O)))
          hitInd = compI (mb sm) (indLt_at_lt_imp (ap1 idx sm) N)

          E0 : Deriv (imp phi (imp psi (eqF Asm (ap2 sigma A d))))
          E0 = liftP phi (liftP psi (csum_succ idx N m))

          E1 : Deriv (imp phi (imp psi (eqF (ap2 sigma A d) (ap2 sigma sm d))))
          E1 = liftP phi (ax_eqCongL sigma A sm d)

          E2 : Deriv (imp phi (imp psi
                  (eqF (ap2 sigma sm d) (ap2 sigma sm (ap1 s O)))))
          E2 = mapUnder1 phi
                 (axK (eqF (ap2 sigma sm d) (ap2 sigma sm (ap1 s O))) psi)
                 (compI hitInd (ax_eqCongR sigma d (ap1 s O) sm))

          E3 : Deriv (imp phi (imp psi
                  (eqF (ap2 sigma sm (ap1 s O)) (ap1 s sm))))
          E3 = liftP phi (liftP psi (sigma_x_one sm))

          E01 : Deriv (imp phi (imp psi (eqF Asm (ap2 sigma sm d))))
          E01 = trans2 phi psi Asm (ap2 sigma A d) (ap2 sigma sm d) E0 E1

          E012 : Deriv (imp phi (imp psi (eqF Asm (ap2 sigma sm (ap1 s O)))))
          E012 = trans2 phi psi Asm (ap2 sigma sm d) (ap2 sigma sm (ap1 s O)) E01 E2
      in trans2 phi psi Asm (ap2 sigma sm (ap1 s O)) (ap1 s sm) E012 E3

    stepReal : Deriv (imp Pc
                 (imp (leq (ap1 s (var zero)) N)
                      (eqF (ap2 (csumObj idx) N (ap1 s (var zero)))
                           (ap1 s (ap1 s (var zero))))))
    stepReal =
      indBoundStep (var zero) N
        (eqF (ap2 (csumObj idx) N (var zero)) (ap1 s (var zero)))
        (eqF (ap2 (csumObj idx) N (ap1 s (var zero))) (ap1 s (ap1 s (var zero))))
        (le_pred_imp (var zero) N)
        realStep

    step : Deriv (imp Pc (substF zero (ap1 s (var zero)) Pc))
    step = closeCoe clN zero (ap1 s (var zero))
             (\ X -> imp Pc
                (imp (leq (ap1 s (var zero)) X)
                     (eqF (ap2 (csumObj idx) X (ap1 s (var zero)))
                          (ap1 s (ap1 s (var zero))))))
             stepReal

    ind : Deriv Pc
    ind = ruleIndNat zero {P = Pc} base step

    finalSubst : Deriv (substF zero N Pc)
    finalSubst = ruleInst zero N ind

    finalCoerced :
      Deriv (imp (leq N N) (eqF (ap2 (csumObj idx) N N) (ap1 s N)))
    finalCoerced =
      eqSubst (\ X -> Deriv (imp (leq N X)
                                 (eqF (ap2 (csumObj idx) X N) (ap1 s N))))
              (Closed.closedAt clN zero N) finalSubst

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 7.  The threshold split (Skolem Df. 2, summed) -- object form.
--
--   csumObj idx (s t) m = sigma (csumObj idx t m) (eqSumObj idx t m)
--
-- "as the threshold rises by 1, the count rises by the number of indices
-- whose image equals t".  Open in the threshold (var 0) and proved by
-- object  ruleIndNat  on the index (var 1), reusing the per-term split
-- indLt_succ_split and the four-term  interchange  (both universal in t).
-- No N appears, so instantiation at the index bound  N  is capture-free.

csum_threshold_split_obj :
  (idx : Fun1) ->
  Deriv (eqF (ap2 (csumObj idx) (ap1 s (var zero)) (var (suc zero)))
              (ap2 sigma (ap2 (csumObj idx) (var zero) (var (suc zero)))
                         (ap2 (eqSumObj idx) (var zero) (var (suc zero)))))
csum_threshold_split_obj idx = ruleIndNat (suc zero) {P = Psplit} base step
  where
    t0 : Term
    t0 = var zero
    st0 : Term
    st0 = ap1 s (var zero)
    m1 : Term
    m1 = var (suc zero)
    sm1 : Term
    sm1 = ap1 s (var (suc zero))

    Psplit : Formula
    Psplit = eqF (ap2 (csumObj idx) st0 m1)
                 (ap2 sigma (ap2 (csumObj idx) t0 m1) (ap2 (eqSumObj idx) t0 m1))

    -- base (m1 := O):  uses the per-term split at index 0.
    base : Deriv (eqF (ap2 (csumObj idx) st0 O)
                       (ap2 sigma (ap2 (csumObj idx) t0 O)
                                  (ap2 (eqSumObj idx) t0 O)))
    base =
      let e_lhs : Deriv (eqF (ap2 (csumObj idx) st0 O) (indLt (ap1 idx O) st0))
          e_lhs = csum_at_O idx st0
          e_split : Deriv (eqF (indLt (ap1 idx O) st0)
                               (ap2 sigma (indLt (ap1 idx O) t0)
                                          (eqInd (ap1 idx O) t0)))
          e_split = indLt_succ_split (ap1 idx O) t0
          e_rhs1 : Deriv (eqF (indLt (ap1 idx O) t0) (ap2 (csumObj idx) t0 O))
          e_rhs1 = ruleSym (csum_at_O idx t0)
          e_rhs2 : Deriv (eqF (eqInd (ap1 idx O) t0) (ap2 (eqSumObj idx) t0 O))
          e_rhs2 = ruleSym (eqsum_at_O idx t0)
      in ruleTrans e_lhs
           (ruleTrans e_split
             (ruleTrans (congL sigma (eqInd (ap1 idx O) t0) e_rhs1)
                        (congR sigma (ap2 (csumObj idx) t0 O) e_rhs2)))

    -- step (m1 := s m1):  the four-term interchange, using the IH (Psplit).
    step : Deriv (imp Psplit
              (eqF (ap2 (csumObj idx) st0 sm1)
                   (ap2 sigma (ap2 (csumObj idx) t0 sm1)
                              (ap2 (eqSumObj idx) t0 sm1))))
    step =
      let a : Term
          a = ap2 (csumObj idx) t0 m1
          b : Term
          b = ap2 (eqSumObj idx) t0 m1
          c : Term
          c = indLt (ap1 idx sm1) t0
          d : Term
          d = eqInd (ap1 idx sm1) t0
          CMst : Term                                   -- csumObj idx (s t) m
          CMst = ap2 (csumObj idx) st0 m1
          I : Term                                      -- indLt(idx(s m), s t)
          I = indLt (ap1 idx sm1) st0
          LHS' : Term
          LHS' = ap2 (csumObj idx) st0 sm1
          RHS' : Term
          RHS' = ap2 sigma (ap2 (csumObj idx) t0 sm1) (ap2 (eqSumObj idx) t0 sm1)
          mid : Term
          mid = ap2 sigma (ap2 sigma a c) (ap2 sigma b d)

          c1 : Deriv (eqF LHS' (ap2 sigma CMst I))
          c1 = csum_succ idx st0 m1
          e_pt : Deriv (eqF I (ap2 sigma c d))
          e_pt = indLt_succ_split (ap1 idx sm1) t0

          congP : Deriv (imp Psplit (eqF (ap2 sigma CMst I)
                                          (ap2 sigma (ap2 sigma a b) I)))
          congP = ax_eqCongL sigma CMst (ap2 sigma a b) I

          preP : Deriv (imp Psplit (eqF LHS' (ap2 sigma (ap2 sigma a b) I)))
          preP = compI congP
                   (prependEqLeft LHS' (ap2 sigma CMst I)
                                  (ap2 sigma (ap2 sigma a b) I) c1)

          purePost : Deriv (eqF (ap2 sigma (ap2 sigma a b) I) mid)
          purePost = ruleTrans (congR sigma (ap2 sigma a b) e_pt)
                               (interchange a b c d)

          lhsChain : Deriv (imp Psplit (eqF LHS' mid))
          lhsChain = compI preP
                       (appendEqRight LHS' (ap2 sigma (ap2 sigma a b) I) mid purePost)

          r1 : Deriv (eqF (ap2 (csumObj idx) t0 sm1) (ap2 sigma a c))
          r1 = csum_succ idx t0 m1
          r2 : Deriv (eqF (ap2 (eqSumObj idx) t0 sm1) (ap2 sigma b d))
          r2 = eqsum_succ idx t0 m1
          rhsEq : Deriv (eqF RHS' mid)
          rhsEq = ruleTrans (congL sigma (ap2 (eqSumObj idx) t0 sm1) r1)
                            (congR sigma (ap2 sigma a c) r2)
      in compI lhsChain (appendEqRight LHS' mid RHS' (ruleSym rhsEq))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 8.  Toolkit for the at-most-one-hit count (nested object
-- inductions with carried hypotheses).

-- Identity implication.
identImp : (A : Formula) -> Deriv (imp A A)
identImp A = mp (mp (axS A (imp A A) A) (axK A (imp A A))) (axK A A)

-- Swap the two antecedents of a curried implication.
swapImp : {A B Cf : Formula} -> Deriv (imp A (imp B Cf)) -> Deriv (imp B (imp A Cf))
swapImp {A} {B} {Cf} d = bCombTwo (liftP B d) (axK B A)

-- Compose two implications under a carried hypothesis  h .
compIUnder :
  (h : Formula) {A B Cf : Formula} ->
  Deriv (imp h (imp A B)) -> Deriv (imp h (imp B Cf)) -> Deriv (imp h (imp A Cf))
compIUnder h {A} {B} {Cf} f g =
  bCombTwo (mapUnder1 h (axK (imp B Cf) A) g) f

-- Apply a fixed implication under THREE carried hypotheses.
mapUnder3 :
  (h1 h2 h3 : Formula) {Z Z' : Formula} ->
  Deriv (imp Z Z') ->
  Deriv (imp h1 (imp h2 (imp h3 Z))) ->
  Deriv (imp h1 (imp h2 (imp h3 Z')))
mapUnder3 h1 h2 h3 zz' d = bCombThree (liftP h1 (liftP h2 (liftP h3 zz'))) d

-- Transitivity of an equation under THREE carried hypotheses.
trans3 :
  (h1 h2 h3 : Formula) (X Y Z : Term) ->
  Deriv (imp h1 (imp h2 (imp h3 (eqF X Y)))) ->
  Deriv (imp h1 (imp h2 (imp h3 (eqF Y Z)))) ->
  Deriv (imp h1 (imp h2 (imp h3 (eqF X Z))))
trans3 h1 h2 h3 X Y Z exy eyz =
  let e_yx : Deriv (imp h1 (imp h2 (imp h3 (eqF Y X))))
      e_yx = mapUnder3 h1 h2 h3 (eqSymImp X Y) exy
      lifted : Deriv (imp h1 (imp h2 (imp h3
                 (imp (eqF Y X) (imp (eqF Y Z) (eqF X Z))))))
      lifted = liftP h1 (liftP h2 (liftP h3 (ax_eqTrans Y X Z)))
      step1 : Deriv (imp h1 (imp h2 (imp h3 (imp (eqF Y Z) (eqF X Z)))))
      step1 = bCombThree lifted e_yx
  in bCombThree step1 eyz

-- Negation introduction under TWO carried hypotheses.
negIntroUnder2 :
  (phi psi P Q : Formula) ->
  Deriv (imp phi (imp psi (imp P Q))) ->
  Deriv (imp phi (imp psi (imp P (neg Q)))) ->
  Deriv (imp phi (imp psi (neg P)))
negIntroUnder2 phi psi P Q h1 h2 =
  let a0 : Deriv (imp phi (imp psi (imp P (imp Q (imp (neg Q) falseF)))))
      a0 = liftP phi (liftP psi (liftP P (axExFalso Q falseF)))
      a1 : Deriv (imp phi (imp psi (imp P (imp (neg Q) falseF))))
      a1 = bCombThree a0 h1
      a2 : Deriv (imp phi (imp psi (imp P falseF)))
      a2 = bCombThree a1 h2
  in mapUnder2 phi psi (impFalseToNeg_imp P) a2

-- a /= c  and  c = t  imply  a /= t , with  a /= c  CARRIED under  psi .
notEq_via_hit_under :
  (psi : Formula) (a c t : Term) ->
  Deriv (imp psi (neg (eqF a c))) ->
  Deriv (imp psi (imp (eqF c t) (neg (eqF a t))))
notEq_via_hit_under psi a c t nAC =
  let hb : Formula
      hb = eqF c t
      hc : Formula
      hc = eqF a t
      -- h1: under [psi, c=t, a=t] derive a=c (both equal t).
      get_ta : Deriv (imp psi (imp hb (imp hc (eqF t a))))
      get_ta = mapUnder3 psi hb hc (eqSymImp a t)
                 (liftP psi (liftP hb (identImp hc)))
      get_tc : Deriv (imp psi (imp hb (imp hc (eqF t c))))
      get_tc = mapUnder3 psi hb hc (eqSymImp c t)
                 (liftP psi (axK hb hc))
      lifted_tr : Deriv (imp psi (imp hb (imp hc
                    (imp (eqF t a) (imp (eqF t c) (eqF a c))))))
      lifted_tr = liftP psi (liftP hb (liftP hc (ax_eqTrans t a c)))
      s1 : Deriv (imp psi (imp hb (imp hc (imp (eqF t c) (eqF a c)))))
      s1 = bCombThree lifted_tr get_ta
      h1 : Deriv (imp psi (imp hb (imp hc (eqF a c))))
      h1 = bCombThree s1 get_tc
      -- h2: under [psi, c=t, a=t] derive  neg (a=c)  (the carried disequality).
      addKK : Deriv (imp (neg (eqF a c)) (imp hb (imp hc (neg (eqF a c)))))
      addKK = compI (axK (neg (eqF a c)) hc)
                    (axK (imp hc (neg (eqF a c))) hb)
      h2 : Deriv (imp psi (imp hb (imp hc (neg (eqF a c)))))
      h2 = mapUnder1 psi addKK nAC
  in negIntroUnder2 psi hb hc (eqF a c) h1 h2

-- Bounded-induction step with a fixed front hypothesis  hit .
indBoundStepH :
  (hit : Formula) (m bnd : Term) (Q Qs : Formula) ->
  Deriv (imp (leq (ap1 s m) bnd) (leq m bnd)) ->
  Deriv (imp hit (imp (leq (ap1 s m) bnd) (imp Q Qs))) ->
  Deriv (imp (imp hit (imp (leq m bnd) Q))
             (imp hit (imp (leq (ap1 s m) bnd) Qs)))
indBoundStepH hit m bnd Q Qs shrink realStep =
  let phi : Formula
      phi = imp hit (imp (leq m bnd) Q)
      pb' : Formula
      pb' = leq (ap1 s m) bnd
      e_phi : Deriv (imp phi (imp hit (imp pb' phi)))
      e_phi = mapUnder2 phi hit (axK phi pb') (axK phi hit)
      e_pb : Deriv (imp phi (imp hit (imp pb' (leq m bnd))))
      e_pb = liftP phi (liftP hit shrink)
      e_hit : Deriv (imp phi (imp hit (imp pb' hit)))
      e_hit = mapUnder2 phi hit (axK hit pb') (liftP phi (identImp hit))
      e_phiHit : Deriv (imp phi (imp hit (imp pb' (imp (leq m bnd) Q))))
      e_phiHit = bCombThree e_phi e_hit
      e_Q : Deriv (imp phi (imp hit (imp pb' Q)))
      e_Q = bCombThree e_phiHit e_pb
      realStep' : Deriv (imp phi (imp hit (imp pb' (imp Q Qs))))
      realStep' = liftP phi realStep
  in bCombThree realStep' e_Q

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 8b.  FOUR-level toolkit (mechanical +1-level lifts of the
-- three-level combinators above), for the BOUNDED prefix_zero / eqsum
-- inductions which carry the codomain bound  topB = leq (s v1) N  in
-- ADDITION to the hit and prefix-bound hypotheses.

-- bComb at FOUR carried hypotheses.
bComb4 :
  {P1 P2 P3 P4 Q Rf : Formula} ->
  Deriv (imp P1 (imp P2 (imp P3 (imp P4 (imp Q Rf))))) ->
  Deriv (imp P1 (imp P2 (imp P3 (imp P4 Q)))) ->
  Deriv (imp P1 (imp P2 (imp P3 (imp P4 Rf))))
bComb4 {P1} {P2} {P3} {P4} {Q} {Rf} D1 D2 =
  bCombThree (bCombThree (liftP P1 (liftP P2 (liftP P3 (axS P4 Q Rf)))) D1) D2

-- Apply a fixed implication under FOUR carried hypotheses.
mapUnder4 :
  (h1 h2 h3 h4 : Formula) {Z Z' : Formula} ->
  Deriv (imp Z Z') ->
  Deriv (imp h1 (imp h2 (imp h3 (imp h4 Z)))) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp h4 Z'))))
mapUnder4 h1 h2 h3 h4 zz' d =
  bComb4 (liftP h1 (liftP h2 (liftP h3 (liftP h4 zz')))) d

-- Transitivity of an equation under FOUR carried hypotheses.
trans4 :
  (h1 h2 h3 h4 : Formula) (X Y Z : Term) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp h4 (eqF X Y))))) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp h4 (eqF Y Z))))) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp h4 (eqF X Z)))))
trans4 h1 h2 h3 h4 X Y Z exy eyz =
  let e_yx : Deriv (imp h1 (imp h2 (imp h3 (imp h4 (eqF Y X)))))
      e_yx = mapUnder4 h1 h2 h3 h4 (eqSymImp X Y) exy
      lifted : Deriv (imp h1 (imp h2 (imp h3 (imp h4
                 (imp (eqF Y X) (imp (eqF Y Z) (eqF X Z)))))))
      lifted = liftP h1 (liftP h2 (liftP h3 (liftP h4 (ax_eqTrans Y X Z))))
      step1 : Deriv (imp h1 (imp h2 (imp h3 (imp h4 (imp (eqF Y Z) (eqF X Z))))))
      step1 = bComb4 lifted e_yx
  in bComb4 step1 eyz

-- Negation introduction under THREE carried hypotheses.
negIntroUnder3 :
  (h1 h2 h3 P Q : Formula) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp P Q)))) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp P (neg Q))))) ->
  Deriv (imp h1 (imp h2 (imp h3 (neg P))))
negIntroUnder3 h1 h2 h3 P Q d1 d2 =
  let a0 : Deriv (imp h1 (imp h2 (imp h3 (imp P (imp Q (imp (neg Q) falseF))))))
      a0 = liftP h1 (liftP h2 (liftP h3 (liftP P (axExFalso Q falseF))))
      a1 : Deriv (imp h1 (imp h2 (imp h3 (imp P (imp (neg Q) falseF)))))
      a1 = bComb4 a0 d1
      a2 : Deriv (imp h1 (imp h2 (imp h3 (imp P falseF))))
      a2 = bComb4 a1 d2
  in mapUnder3 h1 h2 h3 (impFalseToNeg_imp P) a2

-- Compose two implications under TWO carried hypotheses.
compIUnder2 :
  (h1 h2 : Formula) {A B Cf : Formula} ->
  Deriv (imp h1 (imp h2 (imp A B))) ->
  Deriv (imp h1 (imp h2 (imp B Cf))) ->
  Deriv (imp h1 (imp h2 (imp A Cf)))
compIUnder2 h1 h2 {A} {B} {Cf} f g =
  bCombThree (mapUnder2 h1 h2 (axK (imp B Cf) A) g) f

-- By-cases under TWO carried hypotheses.
byCasesUnder2 :
  (h1 h2 A G : Formula) ->
  Deriv (imp h1 (imp h2 (imp A G))) ->
  Deriv (imp h1 (imp h2 (imp (neg A) G))) ->
  Deriv (imp h1 (imp h2 G))
byCasesUnder2 h1 h2 A G c1 c2 =
  let e1 : Deriv (imp h1 (imp h2 (imp (neg G) (neg A))))
      e1 = mapUnder2 h1 h2 (axContrapos A G) c1
      e2 : Deriv (imp h1 (imp h2 (imp (neg G) (neg (neg A)))))
      e2 = mapUnder2 h1 h2 (axContrapos (neg A) G) c2
      nng : Deriv (imp h1 (imp h2 (neg (neg G))))
      nng = negIntroUnder2 h1 h2 (neg G) (neg A) e1 e2
  in mapUnder2 h1 h2 (DNE G) nng

-- Bounded-induction step with TWO fixed front hypotheses  h1 , h2 .
-- (= indBoundStepH with one extra leading hypothesis.)
indBoundStepHB :
  (h1 h2 : Formula) (m bnd : Term) (Q Qs : Formula) ->
  Deriv (imp (leq (ap1 s m) bnd) (leq m bnd)) ->
  Deriv (imp h1 (imp h2 (imp (leq (ap1 s m) bnd) (imp Q Qs)))) ->
  Deriv (imp (imp h1 (imp h2 (imp (leq m bnd) Q)))
             (imp h1 (imp h2 (imp (leq (ap1 s m) bnd) Qs))))
indBoundStepHB h1 h2 m bnd Q Qs shrink realStep =
  let phi : Formula
      phi = imp h1 (imp h2 (imp (leq m bnd) Q))
      pb' : Formula
      pb' = leq (ap1 s m) bnd
      e_phi : Deriv (imp phi (imp h1 (imp h2 (imp pb' phi))))
      e_phi = mapUnder3 phi h1 h2 (axK phi pb')
                (mapUnder1 phi (axK (imp h2 phi) h1) (axK phi h2))
      e_h1 : Deriv (imp phi (imp h1 (imp h2 (imp pb' h1))))
      e_h1 = mapUnder3 phi h1 h2 (axK h1 pb') (liftP phi (axK h1 h2))
      e_h2 : Deriv (imp phi (imp h1 (imp h2 (imp pb' h2))))
      e_h2 = mapUnder3 phi h1 h2 (axK h2 pb') (liftP phi (liftP h1 (identImp h2)))
      -- from phi (= h1->h2->(leq m bnd)->Q) recover, under [h1,h2,pb'], (leq m bnd)->Q
      e_phiApp : Deriv (imp phi (imp h1 (imp h2 (imp pb' (imp (leq m bnd) Q)))))
      e_phiApp = bComb4 (bComb4 e_phi e_h1) e_h2
      e_pb : Deriv (imp phi (imp h1 (imp h2 (imp pb' (leq m bnd)))))
      e_pb = liftP phi (liftP h1 (liftP h2 shrink))
      e_Q : Deriv (imp phi (imp h1 (imp h2 (imp pb' Q))))
      e_Q = bComb4 e_phiApp e_pb
      realStep' : Deriv (imp phi (imp h1 (imp h2 (imp pb' (imp Q Qs)))))
      realStep' = liftP phi realStep
  in bComb4 realStep' e_Q

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 9.  prefix_zero_obj (BOUNDED):  under the top bound  topB =
-- (s var1 <= N)  and the hit  idx (s var1) = t , the prefix equality-sum
-- eqSumObj idx t var1  is  O  (no earlier index hits t , by BOUNDED
-- injectivity -- topB discharges the codomain bound on the larger index).
-- Inner object  ruleIndNat  on the prefix index var2, carrying
-- [topB, hit, prefix-bound] (4-level step).  Open in t = var 0 and the top
-- index var 1.  N is an abstract closed Term (coerced under the inner
-- ruleIndNat / ruleInst by  closeCoe ).

prefix_zero_obj :
  (idx : Fun1) (N : Term) -> Closed N -> InjBelowObj idx N ->
  Deriv (imp (leq (ap1 s (var (suc zero))) N)
             (imp (eqF (ap1 idx (ap1 s (var (suc zero)))) (var zero))
                  (eqF (ap2 (eqSumObj idx) (var zero) (var (suc zero))) O)))
prefix_zero_obj idx N clN inj =
  bCombTwo instLeq (liftP topB (liftP hit (leqNN v1)))
  where
    t : Term
    t = var zero
    v1 : Term
    v1 = var (suc zero)
    v2 : Term
    v2 = var (suc (suc zero))
    topB : Formula
    topB = leq (ap1 s v1) N
    hit : Formula
    hit = eqF (ap1 idx (ap1 s v1)) t

    -- under [topB, hit, (s j <= s v1)] the j-th summand is 0.  Bounded
    -- injectivity:  inj j (s v1)  needs  topB = (s v1 <= N) , supplied as the
    -- outermost carried hypothesis (swapImp puts topB outside the i<j bound).
    summand_zero :
      (j : Term) ->
      Deriv (imp topB (imp hit (imp (leq (ap1 s j) (ap1 s v1))
                                    (eqF (eqInd (ap1 idx j) t) O))))
    summand_zero j =
      let psi : Formula
          psi = leq (ap1 s j) (ap1 s v1)
          a : Term
          a = ap1 idx j
          c : Term
          c = ap1 idx (ap1 s v1)
          P_ : Formula
          P_ = eqF a t
          Qd : Formula
          Qd = eqF a c
          -- bounded injectivity, topB pulled outside:
          nAC0 : Deriv (imp topB (imp psi (neg Qd)))
          nAC0 = swapImp (inj j (ap1 s v1))
          -- insert hit (2nd carried):
          nAC : Deriv (imp topB (imp hit (imp psi (neg Qd))))
          nAC = mapUnder1 topB (axK (imp psi (neg Qd)) hit) nAC0
          -- d2:  a=t  weakens to  neg (a=c)  (carried disequality).
          d2 : Deriv (imp topB (imp hit (imp psi (imp P_ (neg Qd)))))
          d2 = mapUnder3 topB hit psi (axK (neg Qd) P_) nAC
          -- d1:  under [topB,hit,psi,P_=a=t], derive  a=c  (hit gives c=t).
          d1 : Deriv (imp topB (imp hit (imp psi (imp P_ Qd))))
          d1 =
            let get_ta : Deriv (imp topB (imp hit (imp psi (imp P_ (eqF t a)))))
                get_ta = mapUnder4 topB hit psi P_ (eqSymImp a t)
                           (liftP topB (liftP hit (liftP psi (identImp P_))))
                get_tc : Deriv (imp topB (imp hit (imp psi (imp P_ (eqF t c)))))
                get_tc = mapUnder4 topB hit psi P_ (eqSymImp c t)
                           (liftP topB
                             (mapUnder1 hit (axK (imp P_ hit) psi) (axK hit P_)))
                lifted : Deriv (imp topB (imp hit (imp psi (imp P_
                           (imp (eqF t a) (imp (eqF t c) Qd))))))
                lifted = liftP topB
                           (liftP hit (liftP psi (liftP P_ (ax_eqTrans t a c))))
                s1 : Deriv (imp topB (imp hit (imp psi (imp P_ (imp (eqF t c) Qd)))))
                s1 = bComb4 lifted get_ta
            in bComb4 s1 get_tc
          diseq_t : Deriv (imp topB (imp hit (imp psi (neg P_))))
          diseq_t = negIntroUnder3 topB hit psi P_ Qd d1 d2
      in mapUnder3 topB hit psi (eqInd_at_neq_imp a t) diseq_t

    P2 : Formula
    P2 = imp topB (imp hit (imp (leq v2 v1)
            (eqF (ap2 (eqSumObj idx) t v2) O)))

    baseReal : Deriv (imp topB (imp hit (imp (leq O v1)
                       (eqF (ap2 (eqSumObj idx) t O) O))))
    baseReal =
      let base_inner : Deriv (imp topB (imp hit (imp (leq O v1)
                                (eqF (eqInd (ap1 idx O) t) O))))
          base_inner = compIUnder2 topB hit
                         (liftP topB (liftP hit (succ_mono_imp O v1)))
                         (summand_zero O)
      in mapUnder3 topB hit (leq O v1)
           (prependEqLeft (ap2 (eqSumObj idx) t O) (eqInd (ap1 idx O) t) O
                          (eqsum_at_O idx t))
           base_inner

    base : Deriv (substF (suc (suc zero)) O P2)
    base = closeCoe clN (suc (suc zero)) O
             (\ X -> imp (leq (ap1 s v1) X)
                       (imp hit (imp (leq O v1)
                         (eqF (ap2 (eqSumObj idx) t O) O))))
             baseReal

    realStep :
      Deriv (imp topB (imp hit (imp (leq (ap1 s v2) v1)
               (imp (eqF (ap2 (eqSumObj idx) t v2) O)
                    (eqF (ap2 (eqSumObj idx) t (ap1 s v2)) O)))))
    realStep =
      let pb' : Formula
          pb' = leq (ap1 s v2) v1
          Q : Formula
          Q = eqF (ap2 (eqSumObj idx) t v2) O
          P_ : Term
          P_ = ap2 (eqSumObj idx) t v2
          S : Term
          S = eqInd (ap1 idx (ap1 s v2)) t
          top : Term
          top = ap2 (eqSumObj idx) t (ap1 s v2)

          S_zero_pb : Deriv (imp topB (imp hit (imp pb' (eqF S O))))
          S_zero_pb = compIUnder2 topB hit
                        (liftP topB (liftP hit (succ_mono_imp (ap1 s v2) v1)))
                        (summand_zero (ap1 s v2))

          E0 : Deriv (imp topB (imp hit (imp pb'
                 (imp Q (eqF top (ap2 sigma P_ S))))))
          E0 = liftP topB (liftP hit (liftP pb' (liftP Q (eqsum_succ idx t v2))))

          E1 : Deriv (imp topB (imp hit (imp pb' (imp Q
                 (eqF (ap2 sigma P_ S) (ap2 sigma O S))))))
          E1 = liftP topB (liftP hit (liftP pb' (ax_eqCongL sigma P_ O S)))

          S_zeroQ : Deriv (imp topB (imp hit (imp pb' (imp Q (eqF S O)))))
          S_zeroQ = mapUnder3 topB hit pb' (axK (eqF S O) Q) S_zero_pb

          E2 : Deriv (imp topB (imp hit (imp pb' (imp Q
                 (eqF (ap2 sigma O S) (ap2 sigma O O))))))
          E2 = mapUnder4 topB hit pb' Q (ax_eqCongR sigma S O O) S_zeroQ

          E3 : Deriv (imp topB (imp hit (imp pb' (imp Q (eqF (ap2 sigma O O) O)))))
          E3 = liftP topB (liftP hit (liftP pb' (liftP Q (T33 O))))

          E01 : Deriv (imp topB (imp hit (imp pb'
                  (imp Q (eqF top (ap2 sigma O S))))))
          E01 = trans4 topB hit pb' Q top (ap2 sigma P_ S) (ap2 sigma O S) E0 E1
          E012 : Deriv (imp topB (imp hit (imp pb'
                   (imp Q (eqF top (ap2 sigma O O))))))
          E012 = trans4 topB hit pb' Q top (ap2 sigma O S) (ap2 sigma O O) E01 E2
      in trans4 topB hit pb' Q top (ap2 sigma O O) O E012 E3

    stepReal :
      Deriv (imp P2 (imp topB (imp hit (imp (leq (ap1 s v2) v1)
               (eqF (ap2 (eqSumObj idx) t (ap1 s v2)) O)))))
    stepReal =
      indBoundStepHB topB hit v2 v1
        (eqF (ap2 (eqSumObj idx) t v2) O)
        (eqF (ap2 (eqSumObj idx) t (ap1 s v2)) O)
        (le_pred_imp v2 v1) realStep

    step : Deriv (imp P2 (substF (suc (suc zero)) (ap1 s v2) P2))
    step = closeCoe clN (suc (suc zero)) (ap1 s v2)
             (\ X -> imp P2 (imp (leq (ap1 s v1) X)
                       (imp hit (imp (leq (ap1 s v2) v1)
                         (eqF (ap2 (eqSumObj idx) t (ap1 s v2)) O)))))
             stepReal

    ind2 : Deriv P2
    ind2 = ruleIndNat (suc (suc zero)) {P = P2} base step

    instRaw : Deriv (substF (suc (suc zero)) v1 P2)
    instRaw = ruleInst (suc (suc zero)) v1 ind2

    instLeq : Deriv (imp topB (imp hit (imp (leq v1 v1)
                      (eqF (ap2 (eqSumObj idx) t v1) O))))
    instLeq =
      eqSubst (\ X -> Deriv (imp (leq (ap1 s v1) X)
                              (imp hit (imp (leq v1 v1)
                                (eqF (ap2 (eqSumObj idx) t v1) O)))))
              (Closed.closedAt clN (suc (suc zero)) v1) instRaw

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 10.  eqsum_le_one_obj (BOUNDED):  under  v1 <= N , the
-- equality-sum is <= 1 (at most one index <= N hits the threshold t).
-- Outer object  ruleIndNat  on the index v1 carrying the codomain bound
-- (via  indBoundStep ), with  byCasesUnder2  on the top hit (carrying
-- [bound, IH]) and the bounded  prefix_zero_obj  in the hit branch (its
-- topB discharged from the carried bound).  Open in t = var 0 and the
-- index var 1.  N abstract closed (coerced under ruleIndNat by closeCoe).

eqsum_le_one_obj :
  (idx : Fun1) (N : Term) -> Closed N -> InjBelowObj idx N ->
  Deriv (imp (leq (var (suc zero)) N)
             (leq (ap2 (eqSumObj idx) (var zero) (var (suc zero))) (ap1 s O)))
eqsum_le_one_obj idx N clN inj = ruleIndNat (suc zero) {P = P1} base step
  where
    t : Term
    t = var zero
    v1 : Term
    v1 = var (suc zero)

    P1 : Formula
    P1 = imp (leq v1 N) (leq (ap2 (eqSumObj idx) t v1) (ap1 s O))

    oldBase : Deriv (leq (ap2 (eqSumObj idx) t O) (ap1 s O))
    oldBase = leq_eqL (ap2 (eqSumObj idx) t O) (eqInd (ap1 idx O) t) (ap1 s O)
                      (eqsum_at_O idx t) (eqInd_le_one (ap1 idx O) t)

    baseReal : Deriv (imp (leq O N) (leq (ap2 (eqSumObj idx) t O) (ap1 s O)))
    baseReal = liftP (leq O N) oldBase

    base : Deriv (substF (suc zero) O P1)
    base = closeCoe clN (suc zero) O
             (\ X -> imp (leq O X) (leq (ap2 (eqSumObj idx) t O) (ap1 s O)))
             baseReal

    step : Deriv (imp P1 (substF (suc zero) (ap1 s v1) P1))
    step =
      let EM : Term
          EM = ap2 (eqSumObj idx) t v1
          top : Term
          top = ap2 (eqSumObj idx) t (ap1 s v1)
          Q : Formula
          Q = leq EM (ap1 s O)
          Qs : Formula
          Qs = leq top (ap1 s O)

          realStep : Deriv (imp (leq (ap1 s v1) N) (imp Q Qs))
          realStep =
            let psi : Formula
                psi = leq (ap1 s v1) N
                newd : Term
                newd = eqInd (ap1 idx (ap1 s v1)) t
                hit : Formula
                hit = eqF (ap1 idx (ap1 s v1)) t

                succEq : Deriv (eqF top (ap2 sigma EM newd))
                succEq = eqsum_succ idx t v1

                -- hit branch.  prefix_zero_obj : imp psi (imp hit (EM = O)) ;
                -- its topB = psi (carried bound).
                prefixZero : Deriv (imp psi (imp hit (eqF EM O)))
                prefixZero = prefix_zero_obj idx N clN inj

                step_b : Deriv (imp psi (imp hit
                           (eqF (ap2 sigma EM newd) (ap2 sigma O newd))))
                step_b = mapUnder2 psi hit (ax_eqCongL sigma EM O newd) prefixZero

                top_eq_newd : Deriv (imp psi (imp hit (eqF top newd)))
                top_eq_newd =
                  trans2 psi hit top (ap2 sigma O newd) newd
                    (trans2 psi hit top (ap2 sigma EM newd) (ap2 sigma O newd)
                       (liftP psi (liftP hit succEq)) step_b)
                    (liftP psi (liftP hit (sigma_O_left newd)))

                top_leOne : Deriv (imp psi (imp hit (leq top (ap1 s O))))
                top_leOne = mapUnder2 psi hit
                             (leq_eqL_imp top newd (ap1 s O)
                                (eqInd_le_one (ap1 idx (ap1 s v1)) t))
                             top_eq_newd

                h1 : Deriv (imp psi (imp Q (imp hit (leq top (ap1 s O)))))
                h1 = mapUnder1 psi
                       (axK (imp hit (leq top (ap1 s O))) Q) top_leOne

                -- miss branch.  newd = 0 , so  top = EM <= 1  [Q = IH].
                newd_zero : Deriv (imp (neg hit) (eqF newd O))
                newd_zero = eqInd_at_neq_imp (ap1 idx (ap1 s v1)) t

                top_eq_EM : Deriv (imp (neg hit) (eqF top EM))
                top_eq_EM =
                  under1_trans
                    (under1_trans (liftP (neg hit) succEq)
                                  (compI newd_zero (ax_eqCongR sigma newd O EM)))
                    (liftP (neg hit) (T33 EM))

                e1 : Deriv (imp psi (imp Q (imp (neg hit)
                       (eqF (ap2 sub top (ap1 s O)) (ap2 sub EM (ap1 s O))))))
                e1 = liftP psi (liftP Q
                       (compI top_eq_EM (ax_eqCongL sub top EM (ap1 s O))))

                e2 : Deriv (imp psi (imp Q
                       (imp (neg hit) (eqF (ap2 sub EM (ap1 s O)) O))))
                e2 = liftP psi (axK Q (neg hit))

                h2 : Deriv (imp psi (imp Q (imp (neg hit) (leq top (ap1 s O)))))
                h2 = trans3 psi Q (neg hit)
                       (ap2 sub top (ap1 s O)) (ap2 sub EM (ap1 s O)) O e1 e2
            in byCasesUnder2 psi Q hit (leq top (ap1 s O)) h1 h2

          stepInst : Deriv (imp (imp (leq v1 N) Q) (imp (leq (ap1 s v1) N) Qs))
          stepInst = indBoundStep v1 N Q Qs (le_pred_imp v1 N) realStep
      in eqSubst
           (\ X -> Deriv (imp (imp (leq v1 N) Q)
                              (imp (leq (ap1 s v1) X) Qs)))
           (eqSym (Closed.closedAt clN (suc zero) (ap1 s v1)))
           stepInst

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 11.  The unit step, the threshold bound, and the pigeonhole.

-- THE UNIT STEP (uniform in the threshold t = var 0):
--   csumObj idx (s t) N  <=  s (csumObj idx t N) .
-- The threshold split (instantiated at the index bound N) + the BOUNDED
-- equality-sum bound (instantiated at v1 := N, its  leq N N  side condition
-- discharged by  leqNN ) + sigma_le_succ.  Needs  Closed N  to coerce the
-- stuck  substT N N  the  ruleInst  of the bounded statement leaves.
unitStep_obj :
  (idx : Fun1) (N : Term) -> Closed N -> InjBelowObj idx N ->
  Deriv (leq (ap2 (csumObj idx) (ap1 s (var zero)) N)
             (ap1 s (ap2 (csumObj idx) (var zero) N)))
unitStep_obj idx N clN inj =
  let Cv0 : Term
      Cv0 = ap2 (csumObj idx) (var zero) N
      ES : Term
      ES = ap2 (eqSumObj idx) (var zero) N

      split_at_N :
        Deriv (eqF (ap2 (csumObj idx) (ap1 s (var zero)) N)
                   (ap2 sigma Cv0 ES))
      split_at_N = ruleInst (suc zero) N (csum_threshold_split_obj idx)

      -- the bounded  eqsum_le_one_obj  at  v1 := N :  imp (leq N N) (ES <= 1) ,
      -- then discharge  leq N N .  ruleInst leaves a stuck  substT N N .
      raw : Deriv (imp (leq N (substT (suc zero) N N)) (leq ES (ap1 s O)))
      raw = ruleInst (suc zero) N (eqsum_le_one_obj idx N clN inj)

      coerced : Deriv (imp (leq N N) (leq ES (ap1 s O)))
      coerced = eqSubst (\ X -> Deriv (imp (leq N X) (leq ES (ap1 s O))))
                        (Closed.closedAt clN (suc zero) N) raw

      eqsum_at_N : Deriv (leq ES (ap1 s O))
      eqsum_at_N = mp coerced (leqNN N)

      sls : Deriv (leq (ap2 sigma Cv0 ES) (ap1 s Cv0))
      sls = sigma_le_succ Cv0 ES eqsum_at_N
  in leq_eqL (ap2 (csumObj idx) (ap1 s (var zero)) N) (ap2 sigma Cv0 ES)
             (ap1 s Cv0) split_at_N sls

-- THE THRESHOLD BOUND:  csumObj idx t N <= t , open in t = var 0, by ONE
-- object  ruleIndNat  on the threshold (mirroring SpikeB.linearBound_obj),
-- consuming the uniform unit step.  Coerces the abstract closed N under
-- ruleIndNat's substF (base + step).
csum_bound_obj :
  (idx : Fun1) (N : Term) -> Closed N -> InjBelowObj idx N ->
  Deriv (leq (ap2 (csumObj idx) (var zero) N) (var zero))
csum_bound_obj idx N clN inj = ruleIndNat zero {P = Pb} base step
  where
    Pb : Formula
    Pb = leq (ap2 (csumObj idx) (var zero) N) (var zero)

    baseReal : Deriv (leq (ap2 (csumObj idx) O N) O)
    baseReal = leq_eqL (ap2 (csumObj idx) O N) O O
                       (ruleInst zero N (c0_obj idx)) (leqNN O)

    base : Deriv (substF zero O Pb)
    base = closeCoe clN zero O
             (\ X -> leq (ap2 (csumObj idx) O X) O) baseReal

    Cv0 : Term
    Cv0 = ap2 (csumObj idx) (var zero) N
    Csv0 : Term
    Csv0 = ap2 (csumObj idx) (ap1 s (var zero)) N

    d_w : Deriv (imp Pb (leq Csv0 (ap1 s Cv0)))
    d_w = liftP Pb (unitStep_obj idx N clN inj)

    d_tr : Deriv (imp (leq Csv0 (ap1 s Cv0))
                      (imp (leq (ap1 s Cv0) (ap1 s (var zero)))
                           (leq Csv0 (ap1 s (var zero)))))
    d_tr = leq_trans_imp Csv0 (ap1 s Cv0) (ap1 s (var zero))

    stpReal : Deriv (imp Pb (leq Csv0 (ap1 s (var zero))))
    stpReal = bComb (bComb (liftP Pb d_tr) d_w) (succ_mono_imp Cv0 (var zero))

    step : Deriv (imp Pb (substF zero (ap1 s (var zero)) Pb))
    step = closeCoe clN zero (ap1 s (var zero))
             (\ X -> imp Pb (leq (ap2 (csumObj idx) (ap1 s (var zero)) X)
                                 (ap1 s (var zero))))
             stpReal

------------------------------------------------------------------------
-- THE OBJECT PIGEONHOLE.  No injection of  {0,...,N}  into  {0,...,N-1}:
-- if  idx  is BOUNDED-injective (InjBelowObj: i<j<=N => idx i /= idx j --
-- the KR-suppliable notion, since con_inj only constrains named numbers
-- <= N) and maps every  j <= N  below  N  (object MapsBelow), we derive
-- falseF .  N is an arbitrary CLOSED Term
-- (a Bin-compressed numeral in the Berry/KR use) -- never  natCode N , and
-- the count is one object  ruleIndNat , so this is feasible for the
-- exponential  N = 2^{c.ell}  the meta  no_injection_into_smaller  cannot
-- reach.  This is the (P2) upgrade / Phase KR-C deliverable.

no_injection_obj :
  (idx : Fun1) (N : Term) -> Closed N ->
  MapsBelowObj idx N -> InjBelowObj idx N ->
  Deriv falseF
no_injection_obj idx N clN mb inj =
  let boundReal : Deriv (leq (ap2 (csumObj idx) N N) N)
      boundReal =
        eqSubst (\ X -> Deriv (leq (ap2 (csumObj idx) N X) N))
                (Closed.closedAt clN zero N)
                (ruleInst zero N (csum_bound_obj idx N clN inj))

      cr : Deriv (eqF (ap2 (csumObj idx) N N) (ap1 s N))
      cr = crange_obj idx N clN mb

      bridge : Deriv (leq (ap1 s N) N)
      bridge = leq_substL (ap2 (csumObj idx) N N) (ap1 s N) N cr boundReal

      irr : Deriv (neg (leq (ap1 s N) N))
      irr = ruleInst zero N notLeqSucSelf

      exF : Deriv (imp (leq (ap1 s N) N)
                       (imp (neg (leq (ap1 s N) N)) falseF))
      exF = axExFalso (leq (ap1 s N) N) falseF
  in mp (mp exF bridge) irr
