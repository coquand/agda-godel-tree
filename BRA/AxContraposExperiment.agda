{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.AxContraposExperiment
--
-- Feasibility check for replacing the current
--    axContrapos : (P imp Q) imp ((not Q) imp (not P))
-- (modus-tollens form) with Guard's actual classical axiom from
-- guard15.pdf (Lukasiewicz CCNpNqCqp form):
--    axN-Guard P Q : ((not P) imp (not Q)) imp (Q imp P) .
--
-- Goal: derive  axContrapos_mt : (P imp Q) imp ((not Q) imp (not P))
-- from  {axK, axS, axExFalso, axN-Guard, mp}  alone.
--
-- The hypothetical Guard axiom is provided as a module parameter so we
-- don't need to add it to BRA.Deriv just for the experiment.  The
-- existing  axNeg  and  axContrapos  primitives are NOT used in this
-- module (we work as if neither existed).
--
-- This is a pure feasibility check.  No postulates, no holes.
--
-- Result: see the bottom of this file for what was derivable and where
-- the chain blocks (Frege's law / double-negation lift).

module BRA.AxContraposExperiment where

open import BRA.Base
open import BRA.Formula
open import BRA.Deriv  using ( Deriv ; axK ; axS ; mp ; axExFalso )

module Experiment
  (axNG : (P Q : Formula) ->
          Deriv (((not P) imp (not Q)) imp (Q imp P)))
  where

  ----------------------------------------------------------------------
  -- (1) Carneiro deduction-theorem helpers (cf. ndw2.pdf,
  --     BRA/Thm/EvalHelpers.agda).  Local copies, since EvalHelpers
  --     uses the existing axNeg / axContrapos in some places and we
  --     want a clean isolation.

  identP : (P : Formula) -> Deriv (P imp P)
  identP P = mp (mp (axS P (P imp P) P) (axK P (P imp P))) (axK P P)

  liftP : (R : Formula) {Q : Formula} -> Deriv Q -> Deriv (R imp Q)
  liftP R D = mp (axK _ R) D

  bComb : {P Q R : Formula} ->
          Deriv (P imp (Q imp R)) ->
          Deriv (P imp Q) ->
          Deriv (P imp R)
  bComb {P} {Q} {R} D1 D2 = mp (mp (axS P Q R) D1) D2

  bCombTwo : {P1 P2 Q R : Formula} ->
             Deriv (P1 imp (P2 imp (Q imp R))) ->
             Deriv (P1 imp (P2 imp Q)) ->
             Deriv (P1 imp (P2 imp R))
  bCombTwo {P1} {P2} {Q} {R} D1 D2 =
    bComb (bComb (liftP P1 (axS P2 Q R)) D1) D2

  bCombThree : {P1 P2 P3 Q R : Formula} ->
               Deriv (P1 imp (P2 imp (P3 imp (Q imp R)))) ->
               Deriv (P1 imp (P2 imp (P3 imp Q))) ->
               Deriv (P1 imp (P2 imp (P3 imp R)))
  bCombThree {P1} {P2} {P3} {Q} {R} D1 D2 =
    bCombTwo (bCombTwo (liftP P1 (liftP P2 (axS P3 Q R))) D1) D2

  ----------------------------------------------------------------------
  -- (2) PARTIAL RESULT: (P imp Q) imp ((not Q) imp (P imp (not P)))
  --
  -- Under hypotheses {h : P imp Q, k : not Q, p : P}, we have:
  --   - q := mp h p     : Q          (by mp)
  --   - axExFalso Q (not P) : Q -> not Q -> not P
  --   - mp axEf q k     : not P
  --
  -- This step uses only  axExFalso , does not need  axNG .

  innerLemma : (P Q : Formula) ->
               Deriv ((P imp Q) imp ((not Q) imp (P imp (not P))))
  innerLemma P Q =
    let
      H : Formula
      H = P imp Q

      NQ : Formula
      NQ = not Q

      -- "Hypothesis H is available under {H}":  identP H .
      -- Under {H, NQ}:  axK applied to lift it.
      -- Under {H, NQ, P}:  the value of H, ready to be applied to p.

      -- H_avail : Deriv (H imp (NQ imp (P imp H)))
      --   = "H is available as the body, under three hypotheses"
      -- Construction: bComb the lifted axK to insert NQ between H's
      -- two consequents.
      H_avail : Deriv (H imp (NQ imp (P imp H)))
      H_avail = bComb (liftP H (axK (P imp H) NQ)) (axK H P)

      -- P_avail : Deriv (H imp (NQ imp (P imp P)))
      P_avail : Deriv (H imp (NQ imp (P imp P)))
      P_avail = liftP H (liftP NQ (identP P))

      -- mp at the innermost  P imp Q  level: bCombThree.
      Q_avail : Deriv (H imp (NQ imp (P imp Q)))
      Q_avail = bCombThree H_avail P_avail

      -- "Hypothesis NQ is available":  axK NQ P  lifted under H.
      NQ_avail : Deriv (H imp (NQ imp (P imp NQ)))
      NQ_avail = liftP H (axK NQ P)

      -- axExFalso Q (not P) : Q imp (NQ imp (not P)).
      axEf : Deriv (Q imp (NQ imp (not P)))
      axEf = axExFalso Q (not P)

      -- Lift axEf under {H, NQ, P}.
      axEf_lifted : Deriv (H imp (NQ imp (P imp (Q imp (NQ imp (not P))))))
      axEf_lifted = liftP H (liftP NQ (liftP P axEf))

      -- Feed in Q, then NQ, by bCombThree.
      step_a : Deriv (H imp (NQ imp (P imp (NQ imp (not P)))))
      step_a = bCombThree axEf_lifted Q_avail

      step_b : Deriv (H imp (NQ imp (P imp (not P))))
      step_b = bCombThree step_a NQ_avail
    in
      step_b

  ----------------------------------------------------------------------
  -- (3) BLOCKER: getting from  innerLemma  to  axContrapos_mt .
  --
  -- innerLemma  gives  Deriv ((P imp Q) imp ((not Q) imp (P imp (not P)))) .
  -- We want    Deriv ((P imp Q) imp ((not Q) imp (not P))) .
  -- The difference: discharge the inner  P  -- i.e., from the chain
  -- ending in  (P imp (not P))  produce the conclusion  (not P)  alone.
  --
  -- This is exactly Frege's law:  (P imp (not P)) imp (not P) .
  --
  -- Frege's law from  {axK, axS, axExFalso, axNG, mp}  alone is the
  -- block.  Two attempts and the negation-depth recursion they hit:
  --
  -- Attempt A: axNG (not P) (P imp (not P))
  --                : ((not (not P)) imp (not (P imp (not P)))) imp
  --                  ((P imp (not P)) imp (not P))
  --   gives Frege's law given  (not (not P)) imp (not (P imp (not P))) .
  --   The latter requires:
  --     - from  not (not P)  derive  not (P imp (not P)) , which
  --     - in turn requires  P  AND  not P  under hypothesis  not (not P) ,
  --     - which is exactly DNE  (not (not P) imp P) , unprovable from our
  --       axiom set without bootstrapping.
  --
  -- Attempt B: derive  (P imp (not P)) imp (not (not P) imp not P)
  --   via axNG, but this just produces the contrapositive in the wrong
  --   direction; collapsing it back needs  axN-Guard  applied recursively
  --   at deeper nestings -- doesn't terminate.
  --
  -- The standard textbook derivation of Frege's law in Hilbert calc with
  -- axNG (Lukasiewicz) requires DNE  (not (not P) imp P)  as an
  -- intermediate -- which itself recurses through deeper negations using
  -- axNG and never bottoms out without an additional axiom (Frege's F4 in
  -- the Frege-Lukasiewicz axiomatization, or a direct DNE primitive).
  --
  -- CONCLUSION OF THE EXPERIMENT:
  --
  -- Replacing axContrapos with axN-Guard alone is NOT sufficient.  To
  -- derive the modus-tollens form  (P -> Q) -> ~Q -> ~P  cleanly, we
  -- additionally need either:
  --   (a) DNE  ~~P -> P  as a primitive (Frege's F4 form), OR
  --   (b) Mendelson A3  (~B -> ~A) -> ((~B -> A) -> B)  as a primitive
  --       (which is strictly stronger than axN-Guard), OR
  --   (c) accept that  axContrapos  (modus-tollens) is itself a primitive
  --       even when the system has  axN-Guard  (i.e., have BOTH  axN-Guard
  --       and  axContrapos  as primitives).
  --
  -- Option (c) is what guard15.pdf actually does (separate "negation"
  -- and "contraposition" axioms).  Option (b) is Mendelson's choice.
  -- Option (a) is the cleanest if we want a single classical primitive.
  --
  -- For the BRA refactor: keeping  axContrapos  (in its current modus-
  -- tollens form) and ADDITIONALLY adding  axN-Guard  to match Guard's
  -- presentation more faithfully is the most faithful path -- but it
  -- adds an axiom rather than reducing.  Replacing  axContrapos  with
  -- axN-Guard saves nothing because the dispatcher cost is the same.
