{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.SbContract -- the Deriv-level contract realised by the
-- substitution functors  sbt , sbf , sub  -- all  Fun2 .
--
-- All three are BRA Fun2 functions:
--   sbt : Fun2   -- substitution on coded TERMS.
--   sbf : Fun2   -- substitution on coded FORMULAS.
--   sub : Fun2   -- top-level: fix var-index 0, num-ify substituent;
--                  derived as  sub z cP = sbf (Pair (natCode 0) (num z)) cP .
--
-- The contract is the system of per-shape closure equations of  sbt
-- and  sbf  on the Pair-encoded code trees.  Each closure equation has
-- a recursive  ap2 sbt / ap2 sbf  call on the RHS for sub-positions --
-- no meta-Agda intermediary, the recursion is at the BRA Deriv level.
--
-- GENERALISED (user directive, learnt.md): the substituent in sbt /
-- sbf's first arg is an ARBITRARY  Term S  -- NOT restricted to
--  codeTerm t  for some Term t.  This is essential for Thm 14
-- ( learnt.md : "each rule is written with a variable.  We can
-- instantiate this variable to something which is not the code of a
-- term").
--
-- ======================================================================
-- CONTRACT FOR  sbt : Fun2  -- substitution on coded terms.
-- ======================================================================
--
--   sbt_at_O :
--     (spec : Term) ->
--     Deriv (eqF (ap2 sbt spec O) O)
--
--   sbt_at_var_match :
--     (k : Nat) (S : Term) ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
--                  (ap2 Pair (natCode tag_var) (natCode k))) S)
--
--   sbt_at_var_nomatch :
--     (k m : Nat) (S : Term) ->  Eq (natEq k m) false ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
--                  (ap2 Pair (natCode tag_var) (natCode m)))
--                 (ap2 Pair (natCode tag_var) (natCode m)))
--
--   sbt_at_ap1 :
--     (k : Nat) (S : Term) (f : Fun1) (t : Term) ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm (ap1 f t)))
--                 (ap2 Pair (natCode tag_ap1)
--                   (ap2 Pair (codeFun1 f)
--                     (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm t)))))
--
--   sbt_at_ap2 :
--     (k : Nat) (S : Term) (g : Fun2) (a b : Term) ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm (ap2 g a b)))
--                 (ap2 Pair (natCode tag_ap2)
--                   (ap2 Pair (codeFun2 g)
--                     (ap2 Pair
--                       (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm a))
--                       (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm b))))))
--
-- ======================================================================
-- CONTRACT FOR  sbf : Fun2  -- substitution on coded formulas.
-- ======================================================================
--
--   sbf_at_atomic :
--     (k : Nat) (S : Term) (a b : Term) ->
--     Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
--                  (codeFormula (atomic (eqn a b))))
--                 (ap2 Pair (natCode tag_eq)
--                   (ap2 Pair
--                     (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm a))
--                     (ap2 sbt (ap2 Pair (natCode k) S) (codeTerm b)))))
--
--   sbf_at_neg :
--     (k : Nat) (S : Term) (P : Formula) ->
--     Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (codeFormula (neg P)))
--                 (ap2 Pair (natCode tag_neg)
--                   (ap2 sbf (ap2 Pair (natCode k) S) (codeFormula P))))
--
--   sbf_at_imp :
--     (k : Nat) (S : Term) (P Q : Formula) ->
--     Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (codeFormula (imp P Q)))
--                 (ap2 Pair (natCode tag_imp)
--                   (ap2 Pair
--                     (ap2 sbf (ap2 Pair (natCode k) S) (codeFormula P))
--                     (ap2 sbf (ap2 Pair (natCode k) S) (codeFormula Q)))))
--
-- ======================================================================
-- DERIVED:  sub : Fun2 .
-- ======================================================================
--
-- Built from  sbf  and  num :
--   sub z cP =Deriv= ap2 sbf (ap2 Pair (natCode 0) (ap1 num z)) cP .
--
-- The diagonal lemma uses  sub  exclusively (var 0 substitution with
-- numeral-encoded substituent).

module BRA4.SbContract where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code

------------------------------------------------------------------------
-- The contract record.
--
-- Combines all per-shape closures of  sbt  and  sbf  into one bundle
-- the downstream code consumes.  Building this is the work of
--  BRA4/SbT.agda  (sbt) +  BRA4/SbF.agda  (sbf) + adapter modules.

record SbContract (sbt sbf : Fun2) : Set where
  field
    sbt_at_O :
      (spec : Term) ->
      Deriv (eqF (ap2 sbt spec O) O)

    sbt_at_var_match :
      (k : Nat) (S : Term) ->
      Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_var) (natCode k))) S)

    sbt_at_var_nomatch :
      (k m : Nat) (S : Term) ->  Eq (natEq k m) false ->
      Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_var) (natCode m)))
                  (ap2 Pair (natCode tag_var) (natCode m)))

    -- ap1 case: universal in  f : Fun1  and the sub-position  ct : Term .
    sbt_at_ap1 :
      (k : Nat) (S : Term) (f : Fun1) (ct : Term) ->
      Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) ct)))
                  (ap2 Pair (natCode tag_ap1)
                    (ap2 Pair (codeFun1 f)
                      (ap2 sbt (ap2 Pair (natCode k) S) ct))))

    -- ap2 case: universal in  g : Fun2  and sub-positions  ca cb : Term .
    sbt_at_ap2 :
      (k : Nat) (S : Term) (g : Fun2) (ca cb : Term) ->
      Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_ap2)
                     (ap2 Pair (codeFun2 g) (ap2 Pair ca cb))))
                  (ap2 Pair (natCode tag_ap2)
                    (ap2 Pair (codeFun2 g)
                      (ap2 Pair
                        (ap2 sbt (ap2 Pair (natCode k) S) ca)
                        (ap2 sbt (ap2 Pair (natCode k) S) cb)))))

    -- atomic case: universal in sub-positions  ca cb : Term .
    sbf_at_atomic :
      (k : Nat) (S : Term) (ca cb : Term) ->
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_eq) (ap2 Pair ca cb)))
                  (ap2 Pair (natCode tag_eq)
                    (ap2 Pair
                      (ap2 sbt (ap2 Pair (natCode k) S) ca)
                      (ap2 sbt (ap2 Pair (natCode k) S) cb))))

    -- neg case: universal in sub-position  cP : Term .
    sbf_at_neg :
      (k : Nat) (S cP : Term) ->
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_neg) cP))
                  (ap2 Pair (natCode tag_neg)
                    (ap2 sbf (ap2 Pair (natCode k) S) cP)))

    -- imp case: universal in sub-positions  cP cQ : Term .
    sbf_at_imp :
      (k : Nat) (S cP cQ : Term) ->
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S)
                   (ap2 Pair (natCode tag_imp) (ap2 Pair cP cQ)))
                  (ap2 Pair (natCode tag_imp)
                    (ap2 Pair
                      (ap2 sbf (ap2 Pair (natCode k) S) cP)
                      (ap2 sbf (ap2 Pair (natCode k) S) cQ))))
