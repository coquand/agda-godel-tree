{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.ChaitinG1Hit -- the CORRECTED, num-headed, Con-free Goedel-Chaitin G1
-- barrier (T4/CHAITIN-G1-ATOM-CORRECTION.md).
--
-- The compressibility predicate is the BOUNDED EXISTENTIAL
--   Comp_L(x) = exists p, pi [ |p| <= L  AND  thmT(pi) = <| p = num x |> ] ,
-- the program p QUANTIFIED (so neg Comp_L is genuine K(x) > L), realised in
-- quantifier-free BRA by its decidable characteristic function -- the bounded
-- search hit-indicator
--   compHit : Fun1 ,   compHit (num x) = 1  iff  x is L-compressible .
-- The atom is the SINGLE num-headed equation  compHit (num x) = 1  (no pinned
-- program, no length-conjunction: the |p|<=L bound lives INSIDE the search).
--
-- This SUPERSEDES the pinned-atom  T4.ChaitinG1.chaitin_G1  (whose atom
-- atomCompOf pins the single search program g = canonName, making neg(atom)
-- "g doesn't compute x" rather than K(x)>L -- and, since x0 is g's own output,
-- reflexively false, so dNeg was unobtainable and the barrier vacuous).
--
-- The dPos here is the WITNESSED bounded-exists-introduction: the witness
-- (g, Df) makes the bounded search return 1 for x0, an OBJECT fact
--   h : Deriv (compHit z0 = 1)
-- (proved by the search's one-hit lemma -- abstract here, supplied by the
-- search; NOT a necessitation, so no codeFormula on the subject). A SINGLE
-- Sigma_1-completeness step (thm13_singulary at f := compHit) internalises it
-- to  T proves (compHit (num z0) = num 1) , num-headed (codeFXeqY1 keeps num z0
-- verbatim). No  encoded_and , no length conjunct, no necessitation-depth
-- mismatch -- dPos is just  thm13  on  compHit .
--
-- dExF = encoded_exfalso (code-agnostic, shipped); the assembly spine
-- (two encoded_mp, manifest ex-falso N = cNeg P) is T4.ChaitinG1.chaitin_G1_assembly,
-- reused verbatim. Abstract here (the genuinely-unbuilt infrastructure):
-- compHit's concrete definition (bounded search / pairEnum), the object hit
-- fact h, and dNeg's recogniser.

module T4.ChaitinG1Hit where

open import T4.Base
open import T4.ThmT            using ( thmT )
open import T4.Code            using ( codeFalse )
open import T4.DefWit          using ( cImp ; cNeg )
open import T4.ConInj          using ( cmp )
open import T4.ChaitinG1       using ( chaitin_G1_assembly )
open import T4.Thm12.All       using ( thm12 ; fst )
open import T4.Thm12.Thm13     using ( codeFXeqY1 ; thm13_singulary )
open import T4.EncodedProp     using ( exfProof ; encoded_exfalso )

------------------------------------------------------------------------
-- The corrected barrier.
--
--   P    := codeFXeqY1 compHit z0 (s O)            -- <| compHit(num z0) = num 1 |>
--   cPos := ap1 (fst (thm12 compHit)) z0           -- the canonical Sigma_1 proof Df
--   cExF := exfProof P codeFalse                   -- the code-agnostic ex-falso proof
--   f    := cmp (cmp cExF cPos) w0
--
--   dPos : thmT cPos = P                  (thm13_singulary compHit z0 (s O) h)
--   dExF : thmT cExF = cImp P (cImp (cNeg P) codeFalse)   (encoded_exfalso)
--   dNeg : thmT w0   = cNeg P             (recogniser; N = cNeg P, manifest)
--   ===> thmT f = codeFalse               (chaitin_G1_assembly, two encoded_mp)

chaitin_G1_hit :
  (compHit : Fun1) (z0 w0 : Term) ->
  -- h : the bounded search returns 1 for z0 (the witnessed bounded-exists, an
  -- OBJECT fact -- the search's one-hit lemma at the witness (g, Df)).
  Deriv (eqF (ap1 compHit z0) (ap1 s O)) ->
  -- dNeg : T proves the NEGATION of the atom (recogniser output; N = cNeg P).
  Deriv (eqF (ap1 thmT w0) (cNeg (codeFXeqY1 compHit z0 (ap1 s O)))) ->
  -- conclusion : T proves 0=1, via f = cmp (cmp cExF cPos) w0.
  Deriv (eqF (ap1 thmT
               (cmp (cmp (exfProof (codeFXeqY1 compHit z0 (ap1 s O)) codeFalse)
                         (ap1 (fst (thm12 compHit)) z0))
                    w0))
             codeFalse)
chaitin_G1_hit compHit z0 w0 h dNeg =
  let P : Term
      P = codeFXeqY1 compHit z0 (ap1 s O)

      cPos : Term
      cPos = ap1 (fst (thm12 compHit)) z0

      cExF : Term
      cExF = exfProof P codeFalse

      -- dPos: a SINGLE Sigma_1-completeness step on the object hit fact h.
      dPos : Deriv (eqF (ap1 thmT cPos) P)
      dPos = thm13_singulary compHit z0 (ap1 s O) h

      -- dExF: code-agnostic ex-falso necessitation at the codes P, cNeg P.
      dExF : Deriv (eqF (ap1 thmT cExF) (cImp P (cImp (cNeg P) codeFalse)))
      dExF = encoded_exfalso P codeFalse
  in chaitin_G1_assembly P cPos cExF w0 dPos dNeg dExF
