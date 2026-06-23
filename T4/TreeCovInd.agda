{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TreeCovInd -- the INTERNAL course-of-values (strong) INDUCTION PRINCIPLE
-- over codes, route 1 (raw-projection style, no surjective pairing).
--
-- The reusable principle is  covFuel : strong induction on the code value,
-- realised by recursion on a fuel bound, with the strong IH delivered in
-- PROJECTION-FRIENDLY form  `e < d`  (= leq (s e) d).  The client's step,
-- to recurse on a child  c  of a node  d , supplies  leq (s c) d  -- which is
-- exactly the strict child-descent bound (Part B = T4.CantorDescent attempts
-- to discharge it for the Cantor projections).  No surjective pairing enters
-- the principle: the step is phrased via the projections of  d , never via a
-- reconstructed  binNode l r .
--
-- The fold's eta-free successor-unfold (T4.BinTreeCovInd.foldStepRaw) is the
-- companion the step uses to compute  F d  from the children for the actual
-- fold-preservation instances.
--
-- WHY THE FUEL FORM (honest scope note): a single object `ruleIndNat` cannot
-- carry a META-quantified property `Q : Term -> Formula` (ruleIndNat needs ONE
-- object Formula with a free var, as in T4.Stability).  The fuel form is the
-- genuinely reusable internal strong-induction eliminator over codes; the
-- UNCONDITIONAL free-variable form (no a-priori bound) must be done per object
-- property in the Stability style (object var = code, induct on a bound var,
-- feed the IH to a child by ruleInst).  covFuel captures all the arithmetic of
-- that descent once.
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.TreeCovInd where

open import T4.Base

open import BRA3.Church        using ( sub )
open import BRA3.ChurchLeq     using ( leq ; T76 )
open import BRA3.ChurchSubSucc using ( T_sub_O ; T57sub )
open import BRA3.ChurchT80     using ( succEqO_to_anything )
open import T4.LeqMono         using ( leq_trans )
open import BRA3.RuleInst2     using ( ruleInst2 )

------------------------------------------------------------------------
-- Arithmetic helpers.

-- Successor cancellation for leq:  s a <= s b  =>  a <= b .
leq_s_s_cancel : (a b : Term) ->
  Deriv (leq (ap1 s a) (ap1 s b)) -> Deriv (leq a b)
leq_s_s_cancel a b lss =
  let t57 : Deriv (eqF (ap2 sub (ap1 s a) (ap1 s b)) (ap2 sub a b))
      t57 = ruleInst2 zero a (suc zero) b refl T57sub
  in ruleTrans (ruleSym t57) lss
  --  leq (s a)(s b) = eqF (sub (s a)(s b)) O ;  rewrite sub(s a)(s b) -> sub a b.

-- From  s e <= O  (impossible) derive anything: leq (s e) O = eqF (sub (s e) O) O
-- and sub (s e) O = s e (T_sub_O), so s e = O, refuted by succEqO_to_anything.
leq_s_O_absurd : (e : Term) (Q : Formula) ->
  Deriv (leq (ap1 s e) O) -> Deriv Q
leq_s_O_absurd e Q lseO =
  let seO : Deriv (eqF (ap1 s e) O)
      seO = ruleTrans (ruleSym (T_sub_O (ap1 s e))) lseO
  in mp (succEqO_to_anything e Q) seO

------------------------------------------------------------------------
-- covFuel : strong (course-of-values) induction on the code value.
--
--   Given a property  Q : Term -> Formula  and a STEP that, for every  d ,
--   derives  Q d  from the strong IH "Q e for every child  e < d "
--   (e < d  expressed as  leq (s e) d ), conclude  Q d  for every  d  bounded
--   by a fuel numeral  natCode n .
--
-- Recursion is on the meta fuel  n  (structural, terminating).  At fuel  O
-- only  d = O  is in range and the step's IH is vacuous (no  e < O ); at fuel
-- s n , a child  e < d <= s n  satisfies  e <= n , so the IH recurses at  n .

covFuel :
  (Q : Term -> Formula) ->
  ( (d : Term) ->
      ( (e : Term) -> Deriv (leq (ap1 s e) d) -> Deriv (Q e) ) ->
      Deriv (Q d) ) ->
  (n : Nat) -> (d : Term) -> Deriv (leq d (natCode n)) -> Deriv (Q d)
covFuel qP stp zero d bnd =
  stp d (\ e lsed ->
            leq_s_O_absurd e (qP e)
              (leq_trans (ap1 s e) d O lsed bnd))
covFuel qP stp (suc n) d bnd =
  stp d (\ e lsed ->
            let lss : Deriv (leq (ap1 s e) (ap1 s (natCode n)))
                lss = leq_trans (ap1 s e) d (ap1 s (natCode n)) lsed bnd
                len : Deriv (leq e (natCode n))
                len = leq_s_s_cancel e (natCode n) lss
            in covFuel qP stp n e len)

------------------------------------------------------------------------
-- Smoke validation: covFuel is well-formed and applicable.  Instantiated on
-- the real (IH-independent) property  Q d = leq O d  (= 0 <= d), proved by the
-- step from  T76  -- confirming the eliminator delivers a genuine object Deriv
-- for every bounded code.  (The full fold-preservation instances, e.g.
-- wf (mirrorF d) = O, plug foldStepRaw + the Part-B descent bound into `step`.)

leqO : Term -> Formula
leqO d = leq O d

covFuel_leqO : (n : Nat) (d : Term) -> Deriv (leq d (natCode n)) -> Deriv (leq O d)
covFuel_leqO = covFuel leqO stp
  where
    stp : (d : Term) ->
          ((e : Term) -> Deriv (leq (ap1 s e) d) -> Deriv (leq O e)) ->
          Deriv (leq O d)
    stp d ih = ruleInst zero d T76
