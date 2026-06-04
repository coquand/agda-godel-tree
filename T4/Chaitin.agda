{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Chaitin -- the standalone Goedel-Chaitin FIRST incompleteness theorem,
-- Con-FREE and witnessed (chaitin-G1-statement.tex Thm 1 /
-- NEXT-SESSION-CHAITIN-G1-FRESH.md).  This ASSEMBLES the f-construction:
--
--   thmT(z) = IncCode_L(x)  AND  (FIT)  ==>  thmT(f z x) = code(0=1) ,
--
-- as  SpikeChaitin.Search.chaitin_inconsistency  (= chaitin_thm MINUS the Con
-- step), instantiated at the CORRECTED computation-naming atom
-- CompressComp.atomComp ell srch  (single- num  coding, decode-compatible),
-- with BOTH Stage-2 legs realised CONCRETELY:
--
--   * dPos  (the compressibility side, KR-A) = CompressComp.dPosComp  -- T
--     proves  Comp_L(x0)  for the search output  x0 = out(lastpos B) , via
--     Thm12/Thm13 (Sigma_1-completeness: "the short program g computes x0");
--   * dExF  (the D1 ex-falso leg)            = DefWit.dExFGen          -- T
--     proves  A -> (neg A -> 0=1)  (necessitated  axExFalso ).
--
-- FIT is a PREMISE, never discharged here:  leq p0 B  (Solovay/exp-total,
-- elements.pdf SS18; exp2 total in BRA => free).  The search position is the
-- proof code (length-lex = numeric order on numbers), so  enum = u  and there
-- is NO enumerator / no  bin2nat  on f's critical path.
--
-- STILL ABSTRACT (the genuine KR-B remainder, a separate sub-project):
--   * hit / out / enum / hit_le_one / bridge  -- the bounded-search recogniser
--     (the bridge's codeFormula-alignment for a SYMBOLIC  out j  needs an
--     internal/decode-based version of NegAtomComp.negAtomCompOf_correct, which
--     is presently numeral-meta-indexed);
--   * B / p0 / FIT (leq p0 B) / hp0           -- the (FIT) witness;
--   * eN / dLen / h                           -- ell a numeral, the name fits L,
--     and  h : srch ell = out(lastpos B)  the self-naming link  g(L) = x0.
--
-- This is the Con-FREE, comp-atom analogue of the shipped DefWitChaitinCheck
-- (which did chaitin_thm + the OLD atom).  Its compiling confirms the f-target
-- assembles with both Stage-2 legs concrete.

module T4.Chaitin where

open import T4.Base
open import T4.ThmT          using ( thmT )
open import T4.Code          using ( codeFormula ; codeFalse ; falseF )
open import T4.Encode        using ( encode )
open import T4.LenR          using ( lenR )
open import T4.IsNat         using ( isNat )
open import T4.ParseRoundtrip using ( linTop )
open import T4.DefWit        using ( dExFGen )
open import T4.CompressComp  using ( atomComp ; cPosComp ; dPosComp )
import T4.SpikeChaitin as SC

open import BRA3.ChurchLeq      using ( leq )
open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- The assembly, parametric in the budget  ell (= L) , the search program
-- srch (= g) , and the bounded-search recogniser (hit / out / enum + the
-- soundness  bridge ) at the comp atom.

module G1
  (ell : Term)                                   -- the length budget  L  (numeral)
  (srch : Fun1)                                  -- the fixed search program  g
  (hit out enum : Fun1)                          -- the bounded-search recogniser
  (hit_le_one : (j : Term) -> Deriv (leq (ap1 hit j) (ap1 s O)))
  (bridge : (j : Term) ->
     Deriv (imp (eqF (ap1 hit j) (ap1 s O))
                (eqF (ap1 thmT (ap1 enum j))
                     (codeFormula (neg (atomComp ell srch (ap1 out j)))))))
  where

  -- instantiate the shipped search at the CORRECTED comp atom.
  open SC.Search hit out enum (atomComp ell srch) hit_le_one bridge

  -- chaitin_G1 :  the Con-FREE f-construction.  Given (FIT) + the match witness
  -- and the self-naming/length data, it returns the constructed proof of  0=1 :
  --   thmT (f z x) = code(0=1) ,   f z x := cmp (cmp cExF cPos) (enum (lastpos B)) ,
  -- with  cPos / cExF / dPos / dExF  all CONCRETE (dPosComp + dExFGen).
  chaitin_G1 :
    (B p0 : Term) -> Closed B -> Closed p0 ->
    Deriv (leq p0 B) ->                                  -- (FIT): the proof sits at p0 <= B
    Deriv (eqF (ap1 hit p0) (ap1 s O)) ->                -- the search finds a match at p0
    (eN : isNat ell) ->                                  -- ell (= L) is a numeral
    (dLen : Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell)) ->  -- the name of g fits L
    (h : Deriv (eqF (ap1 srch ell) (ap1 out (ap2 lastPosRec O B)))) ->  -- self-naming: g(L) = x0
    Deriv (eqF (ap1 thmT
                 (cmp (cmp (encode (axExFalso
                                      (atomComp ell srch (ap1 out (ap2 lastPosRec O B)))
                                      falseF))
                           (cPosComp ell srch (ap1 out (ap2 lastPosRec O B)) eN dLen h))
                      (ap1 enum (ap2 lastPosRec O B))))
               codeFalse)
  chaitin_G1 B p0 clB clP0 leqp0B hp0 eN dLen h =
    let yhat : Term
        yhat = ap1 out (ap2 lastPosRec O B)
    in chaitin_inconsistency B p0 clB clP0 leqp0B hp0
         (cPosComp ell srch yhat eN dLen h)                         -- cPos  (KR-A compress)
         (encode (axExFalso (atomComp ell srch yhat) falseF))       -- cExF
         (dPosComp ell srch yhat eN dLen h)                         -- dPos  (Thm12/13)
         (dExFGen (atomComp ell srch yhat))                         -- dExF  (D1, shipped)
