{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KSearch -- Phase E3.2/E4 (CHAITIN-G1-STANDARD-DIRECTION.md SS5/SS9): the
-- SEARCH WIRING that discharges T4.KClash.kr_clash's open dNeg from the search
-- firing, and threads the equational halting fact dEval + the size fact dLen,
-- assembling the conditional Chaitin barrier for the standard (evalU) route.
--
-- The standard-route analog of T4.ChaitinG1Witness, re-pointed to the open
-- evalU K-formula  Kgt L x  (T4.KFormula).  Pieces:
--
--   * THE FIRING (the mu-loop).  Instantiate the reusable last-position search
--     T4.LastPosSearch.LP at the CONCRETE recogniser  hitL := hitK L (out_L L)
--     (T4.KRecog / T4.KOut).  A witness  hp0 : hitL p0 = 1  with  p0 <= B
--     forces, via  search_settles , the firing  hitL (lastpos B) = 1  at the
--     settled proof-code  w0 := lastpos B .
--
--   * dNegOpen (the search found the proof).  dNeg_from_hitK turns the firing
--     into  thmT w0 = negKgtCodeOf L (out_L L w0) ; the subject self-reference
--     dSubj : out_L L w0 = num z0  then  negKgtCodeOf_correct  close it to
--     thmT w0 = codeFormula (Kgt L (num z0)) .   (= the open dNeg kr_clash wants.)
--
--   * dEval (the machine halts with z0).  Taken here as the ABSTRACT EQUATIONAL
--     interface  evalU(gLcode, nTerm) = s (num z0) , symbolic fuel  nTerm .  It is
--     DISCHARGED by T4.EvalUMu (the mu-loop simulation, built equationally from
--     the shipped stepU mu-reductions, NEVER traversing thmT) -- plus the out_L
--     C-wrapper that lifts the mu-return position to the subject (E4.x).
--     RETRACTED (was: ev (evalU_correct gL) for an abstract pure Fun1 gL): that
--     is the WRONG object (g_L is the mu-program mcodeMu ..., not mcode1 of a pure
--     Fun1) and its feasibility hinged on Agda NOT forcing the structural fuel
--     (runs1) -- a proof-assistant artifact the mathematics never mentions.  The
--     honest fuel is symbolic/existential (EvalUMu.muEvalU); dEval is its EQUATION.
--
--   * dLen (the description fits L) is the E4 size fact (|gLcode| <= L, L pinned).
--
-- Remaining-for-E4 inputs: dEval (EvalUMu + C-wrapper), dSubj (out_L L w0 = num z0;
-- definitional once concrete), dLen (L pinned), the FIT  leq p0 B , and the
-- witness  hp0  (the conditional antecedent "T proves some K(.)>L").  Same
-- isolated-hypothesis discipline as ChaitinG1Witness.chaitin_G1_closed.

module T4.KSearch where

open import T4.Base
open import T4.Code        using ( codeFormula ; falseF )
open import T4.ThmT        using ( thmT )
open import T4.KFormula    using ( Kgt ; szLeqApp ; negKgtCodeOf ; negKgtCodeOf_correct )
open import T4.KRecog      using ( hitK ; hitK_le_one ; dNeg_from_hitK )
open import T4.KOut        using ( out_L )
open import T4.KClash      using ( kr_clash )
open import T4.ConInj      using ( ConSchema )
open import T4.EvalUEval   using ( evalU )
open import T4.ProgParse   using ( parse )

open import T4.LastPosSearch using ( module LP )

open import BRA3.ChurchLeq   using ( leq )

------------------------------------------------------------------------
-- The assembly, parametric in  Con  and the size threshold  L .

module Build (con : Deriv ConSchema) (L : Term) where

  -- The concrete recogniser  hitL = hitK L (out_L L) : Fun1  (KRecog/KOut),
  -- and its 0/1-ness (KRecog.hitK_le_one).  These instantiate the reusable
  -- last-position search (LastPosSearch.LP).
  hitL : Fun1
  hitL = hitK L (out_L L)

  hitL_le_one : (w : Term) -> Deriv (leq (ap1 hitL w) (ap1 s O))
  hitL_le_one = hitK_le_one L (out_L L)

  open LP hitL hitL_le_one using ( lastpos ; search_settles )

  ----------------------------------------------------------------------
  -- The WIRING, from a firing of  hitL  at  w0 .  dNegOpen is built from the
  -- firing; dEval (the equational halting fact, from EvalUMu) and dLen are
  -- threaded; kr_clash closes.

  kr_godel1_from_firing :
    (gLcode : Term) (z0 : Nat) (w0 nTerm : Term) -> Closed nTerm ->
    Deriv (eqF (ap1 (out_L L) w0) (natCode z0)) ->                 -- dSubj: subject of the found proof is z0
    Deriv (eqF (ap2 evalU (ap1 parse gLcode) nTerm) (ap1 s (natCode z0))) ->  -- dEval: evalU(parse name) halts with z0
    Deriv (eqF (szLeqApp L gLcode) (ap1 s O)) ->                   -- dLen: |name| <= L  (E4, faithful lenR)
    Deriv (eqF (ap1 hitL w0) (ap1 s O)) ->                         -- the search fired at w0
    Deriv falseF
  kr_godel1_from_firing gLcode z0 w0 nTerm clN dSubj dEval dLen fire =
    let dNegOpen : Deriv (eqF (ap1 thmT w0) (codeFormula (Kgt L (natCode z0))))
        dNegOpen = ruleTrans (dNeg_from_hitK L (out_L L) w0 fire)
                     (ruleTrans (cong1 (negKgtCodeOf L) dSubj)
                                (negKgtCodeOf_correct L z0))
    in kr_clash con L gLcode nTerm (natCode z0) w0
         clN (closed_natCode z0)
         dLen dEval dNegOpen

  ----------------------------------------------------------------------
  -- The capstone: the firing is PRODUCED by the mu-loop search from a witness
  -- hp0  in range  (leq p0 B).   w0 := lastpos B .

  kr_godel1_from_witness :
    (gLcode : Term) (z0 : Nat) (B p0 nTerm : Term) ->
    Closed B -> Closed p0 -> Closed nTerm ->
    Deriv (eqF (ap1 (out_L L) (lastpos B)) (natCode z0)) ->        -- dSubj at w0 = lastpos B
    Deriv (eqF (ap2 evalU (ap1 parse gLcode) nTerm) (ap1 s (natCode z0))) ->  -- dEval (EvalUMu + wrapper)
    Deriv (eqF (szLeqApp L gLcode) (ap1 s O)) ->                   -- dLen (E4, faithful lenR)
    Deriv (leq p0 B) ->                                            -- FIT: witness in range
    Deriv (eqF (ap1 hitL p0) (ap1 s O)) ->                         -- a proof exists at code p0
    Deriv falseF
  kr_godel1_from_witness gLcode z0 B p0 nTerm clB clP0 clN dSubj dEval dLen fit hp0 =
    let fire : Deriv (eqF (ap1 hitL (lastpos B)) (ap1 s O))
        fire = mp (search_settles B p0 clB clP0 hp0) fit
    in kr_godel1_from_firing gLcode z0 (lastpos B) nTerm clN dSubj dEval dLen fire
