{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.NumInert -- the numeral-inertness lemma, by INTERNAL induction.
--
--   sbt_num_inert :
--     (k : Nat) (S : Term) (x : Term) ->
--     Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (ap1 num x)) (ap1 num x))
--
-- Substituting ANY variable into (the code of) a numeral leaves it
-- unchanged:  Sub(Num(x), k, S) = Num(x) , for an ARBITRARY object term
-- x .  A numeral, viewed as a coded term, contains no occurrence of any
-- variable, so every substitution acts as the identity on it.
--
-- ======================================================================
-- WHY INTERNAL INDUCTION (test1).
-- ======================================================================
--
-- Once  x  is a *variable* (here: an arbitrary object term) inertness is
-- NOT provable by inspection of syntax.  It requires a genuine induction
-- on  x , and "genuine" means the OBJECT theory's own induction rule
--  ruleIndNat  (Guard Rule VI) -- NOT meta-level Agda recursion.  The
-- numeral  num x  is produced by the recursive coding functor  num
-- (BRA4.Num); its inertness is therefore an internal THEOREM.
--
-- CONSTRUCTION.  Schematic in two object variables:
--    var 0  = the numeral argument (the induction variable);
--    var 1  = the substituent slot (instantiated to S at the end).
-- The fixed var-index code  natCode k  is closed, so it survives every
-- substitution (substT_natCode / simSubstT_natCode).
--
--   numInert_obj k : Deriv P(var 0)        via  ruleIndNat 0
--     base   P(O)        :  num O = O ; sbt spec O = O .
--     step   P(var 0) -> P(s (var 0))  :  num_at_S, sbt_at_ap1, IH threaded
--            through congruence-as-implication (ax_eqCongR / impTrans /
--            prependEqLeft / appendEqRight -- the IH is an object
--            HYPOTHESIS discharged via the implication, not a recursion).
--
--   sbt_num_inert k S x = ruleInst2 0 x 1 S ... (numInert_obj k)
--     instantiates  var 0 := x , var 1 := S  SIMULTANEOUSLY (capture-free;
--     x and S are independent and either may mention the other's
--     variable), then  eqSubst  cleans  simSubstT 0 x 1 S (natCode k)  to
--     natCode k .
--
-- ======================================================================
-- SIGNIFICANCE.
-- ======================================================================
--
-- The compound encoded-axiom cases (EqCong1 / EqCongL / EqCongR /
-- EqTrans) only ever substitute into numeral-coded positions.  If every
-- such position is inert (this lemma), the simultaneous multi-variable
-- machinery  sbt2 / sbt3  may not be needed: iterated single-variable
-- sbt plus this lemma should suffice.  (Hypothesis; cf. project memory
-- and  BRA4/NEXT-SESSION-SBT2-SBT3.md .)

module BRA4.NumInert where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Num
open import BRA4.SbT
open import BRA4.SbtAtAp

open import BRA3.Logic     using ( impTrans ; prependEqLeft ; appendEqRight )
open import BRA3.RuleInst2 using ( ruleInst2 ; simSubstT )
open import BRA3.Numerals  using ( substT_natCode )

------------------------------------------------------------------------
-- simSubstT is the identity on numerals (mirror of substT_natCode).

simSubstT_natCode :
  (k1 : Nat) (t1 : Term) (k2 : Nat) (t2 : Term) (n : Nat) ->
  Eq (simSubstT k1 t1 k2 t2 (natCode n)) (natCode n)
simSubstT_natCode k1 t1 k2 t2 zero    = refl
simSubstT_natCode k1 t1 k2 t2 (suc n) =
  eqCong (ap1 s) (simSubstT_natCode k1 t1 k2 t2 n)

------------------------------------------------------------------------
-- Object-level (internal) induction.  Schematic in var 0 (induction
-- variable = the numeral argument) and var 1 (the substituent slot).

numInert_obj :
  (k : Nat) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) (var 1)) (ap1 num (var 0)))
              (ap1 num (var 0)))
numInert_obj k = ruleIndNat 0 {P = P0} base step
  where
  spec : Term
  spec = ap2 Pair (natCode k) (var 1)

  P0 : Formula
  P0 = eqF (ap2 sbt spec (ap1 num (var 0))) (ap1 num (var 0))

  ----------------------------------------------------------------------
  -- Base:  substF 0 O P0  =  (sbt spec (num O) = num O).
  --   sbt spec (num O) = sbt spec O   [congR, num_at_O]
  --                    = O            [sbt_at_O]
  --                    = num O        [sym num_at_O]

  base0 : Deriv (eqF (ap2 sbt spec (ap1 num O)) (ap1 num O))
  base0 = ruleTrans (congR sbt spec num_at_O)
                    (ruleTrans (sbt_at_O spec) (ruleSym num_at_O))

  base : Deriv (substF 0 O P0)
  base = eqSubst
           (\ z -> Deriv (eqF (ap2 sbt (ap2 Pair z (var 1)) (ap1 num O))
                               (ap1 num O)))
           (eqSym (substT_natCode 0 O k))
           base0

  ----------------------------------------------------------------------
  -- Step:  imp P0 (substF 0 (s (var 0)) P0).
  --
  --   sbt spec (num (s v0))
  --     =[pre]  Pair tag_ap1 (Pair tag_s (sbt spec (num v0)))   =: M
  --     -- IH replaces (sbt spec (num v0)) by (num v0):
  --     =       Pair tag_ap1 (Pair tag_s (num v0))              =: N
  --     =[post] num (s v0)
  --
  -- The IH = P0 enters only inside M; we lift the whole chain to an
  -- implication  imp P0 (eqF (sbt spec (num (s v0))) (num (s v0))) .

  -- pre :  sbt spec (num (s v0))  =  M .  (IH-independent.)
  pre :
    Deriv (eqF (ap2 sbt spec (ap1 num (ap1 s (var 0))))
                (ap2 Pair (natCode tag_ap1)
                  (ap2 Pair (natCode tag_s) (ap2 sbt spec (ap1 num (var 0))))))
  pre = ruleTrans (congR sbt spec (num_at_S (var 0)))
                  (sbt_at_ap1 k (var 1) s (ap1 num (var 0)))

  -- post :  N  =  num (s v0) .  (IH-independent.)
  post :
    Deriv (eqF (ap2 Pair (natCode tag_ap1)
                  (ap2 Pair (natCode tag_s) (ap1 num (var 0))))
                (ap1 num (ap1 s (var 0))))
  post = ruleSym (num_at_S (var 0))

  -- ihImp :  imp P0 (eqF M N) , via two ax_eqCongR (Pair) layers.
  ihImp :
    Deriv (imp P0
            (eqF (ap2 Pair (natCode tag_ap1)
                   (ap2 Pair (natCode tag_s) (ap2 sbt spec (ap1 num (var 0)))))
                 (ap2 Pair (natCode tag_ap1)
                   (ap2 Pair (natCode tag_s) (ap1 num (var 0))))))
  ihImp =
    impTrans
      (ax_eqCongR Pair (ap2 sbt spec (ap1 num (var 0))) (ap1 num (var 0))
        (natCode tag_s))
      (ax_eqCongR Pair
        (ap2 Pair (natCode tag_s) (ap2 sbt spec (ap1 num (var 0))))
        (ap2 Pair (natCode tag_s) (ap1 num (var 0)))
        (natCode tag_ap1))

  -- consequentMap :  imp (eqF M N) (eqF (sbt spec (num (s v0))) (num (s v0))) .
  consequentMap :
    Deriv (imp
            (eqF (ap2 Pair (natCode tag_ap1)
                   (ap2 Pair (natCode tag_s) (ap2 sbt spec (ap1 num (var 0)))))
                 (ap2 Pair (natCode tag_ap1)
                   (ap2 Pair (natCode tag_s) (ap1 num (var 0)))))
            (eqF (ap2 sbt spec (ap1 num (ap1 s (var 0))))
                 (ap1 num (ap1 s (var 0)))))
  consequentMap =
    impTrans
      (prependEqLeft
        (ap2 sbt spec (ap1 num (ap1 s (var 0))))
        (ap2 Pair (natCode tag_ap1)
          (ap2 Pair (natCode tag_s) (ap2 sbt spec (ap1 num (var 0)))))
        (ap2 Pair (natCode tag_ap1)
          (ap2 Pair (natCode tag_s) (ap1 num (var 0))))
        pre)
      (appendEqRight
        (ap2 sbt spec (ap1 num (ap1 s (var 0))))
        (ap2 Pair (natCode tag_ap1)
          (ap2 Pair (natCode tag_s) (ap1 num (var 0))))
        (ap1 num (ap1 s (var 0)))
        post)

  step0 :
    Deriv (imp P0 (eqF (ap2 sbt spec (ap1 num (ap1 s (var 0))))
                       (ap1 num (ap1 s (var 0)))))
  step0 = impTrans ihImp consequentMap

  step : Deriv (imp P0 (substF 0 (ap1 s (var 0)) P0))
  step = eqSubst
           (\ z -> Deriv (imp P0
                     (eqF (ap2 sbt (ap2 Pair z (var 1)) (ap1 num (ap1 s (var 0))))
                          (ap1 num (ap1 s (var 0))))))
           (eqSym (substT_natCode 0 (ap1 s (var 0)) k))
           step0

------------------------------------------------------------------------
-- The numeral-inertness lemma for an arbitrary object term  x .
--
-- Instantiate the schematic result at  var 0 := x , var 1 := S
-- simultaneously (ruleInst2: capture-free), then clean
--  simSubstT 0 x 1 S (natCode k)  to  natCode k .

sbt_num_inert :
  (k : Nat) (S : Term) (x : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) (ap1 num x)) (ap1 num x))
sbt_num_inert k S x =
  eqSubst
    (\ z -> Deriv (eqF (ap2 sbt (ap2 Pair z S) (ap1 num x)) (ap1 num x)))
    (simSubstT_natCode 0 x 1 S k)
    (ruleInst2 0 x 1 S refl (numInert_obj k))
