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
-- RESULT: derivation succeeds.  The full chain
--    axK + axS + axNG + mp  =>  axContrapos_mt
-- typechecks (~0.15s).  The breakdown:
--   (3) DNE  ¬¬A -> A , 21-step transcription of the Lukasiewicz proof
--       (https://www.maths.tcd.ie/~stalker/22C00/notes/3.9-the-
--       %C5%82ukasiewicz-system.html).
--   (4) compI : implication composition (1-line helper).
--   (5) Q_to_dNeg :  Q -> ¬¬Q  via axNG and DNE-at-¬Q (1 line).
--   (6) dNeg_lift :  (P -> Q) -> (¬¬P -> ¬¬Q)  via DNE_P + Q_to_dNeg
--       and Carneiro-lifted composition (~12 lines).
--   (7) axContrapos_mt = compI (dNeg_lift P Q) (axNG (¬P) (¬Q))  (1 line).
--
-- Implication for the BRA refactor: the codebase's current curried
-- axNeg `~P -> ~Q -> Q -> P` should be REPLACED by the implicational
-- form  `(~P -> ~Q) -> (Q -> P)`  (matching guard15.pdf).  Then
-- axContrapos becomes a derived lemma (this file proves it), and one
-- of the two classical primitives is eliminated.

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
  -- (3) DNE  ¬¬A → A , transcribed from the Lukasiewicz textbook chain.
  --
  -- Notation:
  --   H = ¬¬A , U = ¬A , V = ¬¬¬A , W = ¬¬¬¬A .
  --
  -- Then  ¬V = W , ¬U = H , ¬H = V , ¬A = U  (definitionally), so axNG
  -- instantiations unfold cleanly.

  DNE : (A : Formula) -> Deriv ((not (not A)) imp A)
  DNE A =
    let
      H : Formula
      H = not (not A)

      U : Formula
      U = not A

      V : Formula
      V = not (not (not A))

      W : Formula
      W = not (not (not (not A)))

      -- Step 1:  axNG V U  :  (¬V → ¬U) → (U → V)  =  (W → H) → (U → V)
      s1 : Deriv ((W imp H) imp (U imp V))
      s1 = axNG V U

      -- Step 2:  axK
      s2 : Deriv (((W imp H) imp (U imp V)) imp (H imp ((W imp H) imp (U imp V))))
      s2 = axK ((W imp H) imp (U imp V)) H

      -- Step 3:  mp 2,1
      s3 : Deriv (H imp ((W imp H) imp (U imp V)))
      s3 = mp s2 s1

      -- Step 4:  axS
      s4 : Deriv ((H imp ((W imp H) imp (U imp V)))
                    imp ((H imp (W imp H)) imp (H imp (U imp V))))
      s4 = axS H (W imp H) (U imp V)

      -- Step 5:  mp 4,3
      s5 : Deriv ((H imp (W imp H)) imp (H imp (U imp V)))
      s5 = mp s4 s3

      -- Step 6:  axK
      s6 : Deriv (H imp (W imp H))
      s6 = axK H W

      -- Step 7:  mp 5,6
      s7 : Deriv (H imp (U imp V))
      s7 = mp s5 s6

      -- Step 8:  axNG A H : (¬A → ¬H) → (H → A) = (U → V) → (H → A)
      s8 : Deriv ((U imp V) imp (H imp A))
      s8 = axNG A H

      -- Step 9:  axK
      s9 : Deriv (((U imp V) imp (H imp A)) imp (H imp ((U imp V) imp (H imp A))))
      s9 = axK ((U imp V) imp (H imp A)) H

      -- Step 10:  mp 9,8
      s10 : Deriv (H imp ((U imp V) imp (H imp A)))
      s10 = mp s9 s8

      -- Step 11:  axS
      s11 : Deriv ((H imp ((U imp V) imp (H imp A)))
                     imp ((H imp (U imp V)) imp (H imp (H imp A))))
      s11 = axS H (U imp V) (H imp A)

      -- Step 12:  mp 11,10
      s12 : Deriv ((H imp (U imp V)) imp (H imp (H imp A)))
      s12 = mp s11 s10

      -- Step 13:  mp 12,7
      s13 : Deriv (H imp (H imp A))
      s13 = mp s12 s7

      -- Step 14:  axK
      s14 : Deriv (H imp ((H imp H) imp H))
      s14 = axK H (H imp H)

      -- Step 15:  axK
      s15 : Deriv (H imp (H imp H))
      s15 = axK H H

      -- Step 16:  axS
      s16 : Deriv ((H imp ((H imp H) imp H)) imp ((H imp (H imp H)) imp (H imp H)))
      s16 = axS H (H imp H) H

      -- Step 17:  mp 16,14
      s17 : Deriv ((H imp (H imp H)) imp (H imp H))
      s17 = mp s16 s14

      -- Step 18:  mp 17,15
      s18 : Deriv (H imp H)
      s18 = mp s17 s15

      -- Step 19:  axS
      s19 : Deriv ((H imp (H imp A)) imp ((H imp H) imp (H imp A)))
      s19 = axS H H A

      -- Step 20:  mp 19,13
      s20 : Deriv ((H imp H) imp (H imp A))
      s20 = mp s19 s13

      -- Step 21:  mp 20,18
      s21 : Deriv (H imp A)
      s21 = mp s20 s18
    in s21

  ----------------------------------------------------------------------
  -- (4) Helper: implication composition
  --     compI : Deriv (X imp Y) -> Deriv (Y imp Z) -> Deriv (X imp Z) .

  compI : {X Y Z : Formula} ->
          Deriv (X imp Y) -> Deriv (Y imp Z) -> Deriv (X imp Z)
  compI {X} {Y} {Z} h1 h2 = bComb (liftP X h2) h1

  ----------------------------------------------------------------------
  -- (5) Q -> ~~Q  (the "unit" of double negation).
  --
  -- axNG (not (not Q)) Q : (¬¬¬Q → ¬Q) → (Q → ¬¬Q) .
  -- The antecedent is exactly DNE applied at ¬Q.

  Q_to_dNeg : (Q : Formula) -> Deriv (Q imp (not (not Q)))
  Q_to_dNeg Q = mp (axNG (not (not Q)) Q) (DNE (not Q))

  ----------------------------------------------------------------------
  -- (6) Double-negation lift:
  --       (P imp Q) imp ((not (not P)) imp (not (not Q))) .
  --
  -- Construction under hypothesis H : P imp Q:
  --   DNE P     : ¬¬P → P
  --   compose with H :  ¬¬P → Q
  --   compose with Q_to_dNeg Q :  ¬¬P → ¬¬Q
  -- All under H using bCombTwo / liftP.

  dNeg_lift : (P Q : Formula) ->
              Deriv ((P imp Q) imp ((not (not P)) imp (not (not Q))))
  dNeg_lift P Q =
    let
      H : Formula
      H = P imp Q

      NNP : Formula
      NNP = not (not P)

      NNQ : Formula
      NNQ = not (not Q)

      -- Under {H, NNP}: derive P via DNE.
      --   D1 : Deriv (H imp (NNP imp (NNP imp P)))    = DNE_P  lifted twice
      --   D2 : Deriv (H imp (NNP imp NNP))            = identP NNP  lifted under H
      --   bCombTwo D1 D2 : Deriv (H imp (NNP imp P))
      D1 : Deriv (H imp (NNP imp (NNP imp P)))
      D1 = liftP H (liftP NNP (DNE P))

      D2 : Deriv (H imp (NNP imp NNP))
      D2 = liftP H (identP NNP)

      P_avail : Deriv (H imp (NNP imp P))
      P_avail = bCombTwo D1 D2

      -- Under {H, NNP}: H is available (= P imp Q under both hypotheses).
      H_avail : Deriv (H imp (NNP imp (P imp Q)))
      H_avail = axK H NNP

      -- Under {H, NNP}: derive Q via mp H_avail P_avail (at the inner level).
      Q_avail : Deriv (H imp (NNP imp Q))
      Q_avail = bCombTwo H_avail P_avail

      -- Under {H, NNP}: Q_to_dNeg Q : Q imp NNQ , available.
      QtoNNQ_avail : Deriv (H imp (NNP imp (Q imp NNQ)))
      QtoNNQ_avail = liftP H (liftP NNP (Q_to_dNeg Q))

      -- bCombTwo to compose: under {H, NNP}, derive NNQ.
      NNQ_avail : Deriv (H imp (NNP imp NNQ))
      NNQ_avail = bCombTwo QtoNNQ_avail Q_avail
    in NNQ_avail

  ----------------------------------------------------------------------
  -- (7) THE GOAL: axContrapos modus-tollens form.
  --
  --   axContrapos_mt P Q : (P imp Q) imp ((not Q) imp (not P)) .
  --
  -- Construction:
  --   dNeg_lift P Q : (P imp Q) imp ((¬¬P) imp (¬¬Q)).
  --   axNG (not P) (not Q)  : ((¬¬P) imp (¬¬Q)) imp ((¬Q) imp (¬P)).
  --   compose them.

  axContrapos_mt : (P Q : Formula) ->
                   Deriv ((P imp Q) imp ((not Q) imp (not P)))
  axContrapos_mt P Q =
    compI (dNeg_lift P Q) (axNG (not P) (not Q))
