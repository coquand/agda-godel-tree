{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Test_f_eq_I
--
-- Test of the user's proposal for f = I:
--
--    x = k  -->  th(E_I x) = code "x_ = k"   (for k numeral)
--
-- Concretely we want, given a Deriv of  atomic (eqn x k)  with  k  a
-- numeral, to produce a Tree y such that
--
--    thmT(reify y) = reify (codeFormula (atomic (eqn (ap1 cor x) k))) .
--
-- (Note: with f = I, applying axI on the left slot of "I(x_) = k"
-- collapses to "x_ = k" = "cor x = k".)
--
-- The construction reduces to: given pf : Deriv (x = k), produce a
-- Deriv of (cor x = k), then  encode  it.  The bridge needed is
--
--    cor_k_eq_k : Deriv (atomic (eqn (ap1 cor k) k)) ,
--
-- combined with  cong1 cor pf : Deriv (cor x = cor k)  via  ruleTrans .
--
-- So the question is: is  cor k = k  derivable for "k numeral"?

module BRA.Test_f_eq_I where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Thm.ThmT using (thmT)

-- Module parametrised over encode (since encode lives inside ThmT's
-- WithDispatch, parametric over 30 dispatchers).

module Experiment
  (encode : (P : Formula) -> Deriv P ->
            Sigma Tree (\ y ->
              Deriv (atomic (eqn (ap1 thmT (reify y))
                                 (reify (codeFormula P))))))
  where

  ----------------------------------------------------------------------
  -- The construction, given a side-condition  cor_k_eq_k .

  E_I_via_bridge :
    (x k : Term) ->
    Deriv (atomic (eqn (ap1 cor k) k)) ->         -- the side condition
    Deriv (atomic (eqn x k)) ->                    -- hypothesis  x = k
    Sigma Tree (\ y ->
      Deriv (atomic (eqn (ap1 thmT (reify y))
                         (reify (codeFormula (atomic (eqn (ap1 cor x) k)))))))
  E_I_via_bridge x k cor_k_eq_k pf =
    let
      cor_xk : Deriv (atomic (eqn (ap1 cor x) (ap1 cor k)))
      cor_xk = cong1 cor pf

      cor_x_eq_k : Deriv (atomic (eqn (ap1 cor x) k))
      cor_x_eq_k = ruleTrans cor_xk cor_k_eq_k
    in
      encode _ cor_x_eq_k

  ----------------------------------------------------------------------
  -- Case k = O (= numeral zero).
  --
  --  cor O = O   is  axRecLf stepCor , available via the derived
  --  axRecLf lemma in BRA.Deriv .  Bridges trivially.

  test_k_eq_O :
    (x : Term) ->
    Deriv (atomic (eqn x O)) ->
    Sigma Tree (\ y ->
      Deriv (atomic (eqn (ap1 thmT (reify y))
                         (reify (codeFormula (atomic (eqn (ap1 cor x) O)))))))
  test_k_eq_O x pf =
    E_I_via_bridge x O (axRecLf BRA.Cor.stepCor) pf
    where open import BRA.Cor

  ----------------------------------------------------------------------
  -- Case k = ap2 Pair O O (= numeral 1).
  --
  -- cor 1  reduces (via axRecNd + stepCor's Fan structure) to
  --
  --   ap2 stepCor (Pair O (Pair O O)) (Pair (cor O) (cor O))
  --   = Pair (reify tagAp2) (Pair (reify (codeF2 Pair)) (Pair O O)) .
  --
  -- This is NOT  ap2 Pair O O .  So  cor 1 = 1  is NOT BRA-derivable.
  --
  -- HENCE the user's E_I cannot be constructed for k = ap2 Pair O O
  -- via the "encode + bridge" route.  We document this rather than
  -- attempting an unprovable derivation.

  -- (No  test_k_eq_one  function: it would require a Deriv of
  --   cor (ap2 Pair O O) = ap2 Pair O O
  -- which does not hold.)

  ----------------------------------------------------------------------
  -- ASSESSMENT.
  --
  -- The test for f = I with hypothesis  x = k  and conclusion
  --  "x_ = k"  (raw k on the right):
  --
  --   * For k = O : works trivially (cor O = O via axRecLf).
  --
  --   * For k = ap2 Pair O O : FAILS .  cor k reduces to a tree of
  --     shape  ap2 Pair tagAp2T (ap2 Pair pairCodeF2T (...)) , which
  --     is not  ap2 Pair O O .  No BRA derivation of  cor k = k .
  --
  --   * For general k : FAILS for the same reason.  cor pushes
  --     through Pair-structure with tag/codeF2 wrapping at each
  --     node.
  --
  -- Why this confirms Theorem 12 is needed:
  --
  --   Theorem 12's conclusion form is  "f(x_) = (f x)_"  with cor on
  --   BOTH sides.  For f = I, this is  "x_ = x_" , which trivially
  --   holds via axRefl on x_ -- and encode of that derivation gives
  --   a tree witnessing  thmT(D_I x) = code "x_ = x_" .
  --
  --   Replacing the right-hand cor with raw k requires the bridge
  --   cor k = k , which is generally false (only true for k = O).
  --   So the user's "raw k on the right" simplification is NOT
  --   achievable as a general claim -- the right slot must have cor
  --   for k > 0.
  --
  -- CONSEQUENCE for the alternative-Step-1 proposal:
  --
  --   Theorem 12's choice of cor-on-both-sides is the load-bearing
  --   asymmetry.  Eliminating cor on the right (going to "x_ = k"
  --   raw) is not a simplification -- it makes the formula
  --   non-derivable for k > 0.
  --
  --   The earlier AlternativeStep1Experiment (using ruleInst +
  --   thClosed + encode) was tacitly using cor-on-both-sides because
  --   for f := thmT and k := cG, the cG term happens to be reify of
  --   a code, so cor cG = cG (via corOfReify at this specific cG).
  --   That coincidence is specific to "k is a code-of-something"
  --   shape, not a general property of "numerals".
