{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KDiag -- Phase E4-concrete (partial): the CONCRETE diagonal program, and
-- the mu-witness <-> firing COHERENCE discharged.
--
-- The standard-route diagonal is  g_L = out_L o (mu n. [ predFlip(n) = 0 ]) ,
-- where the mu-predicate is the CONCRETE  predFlip L = isZero o hitL  (hitL =
-- hitK L (out_L L), T4.KRecog).  Since  isZero  flips 0/1, predFlip(n) = O iff
-- hitL(n) = s O (a hit), so the mu-loop halts at the FIRST hit -- exactly the
-- search.  This makes the mu-loop's witness facts (dHalt/dBelow, needed by
-- T4.EvalUMu via T4.KGodel1) DERIVABLE from the  hitL  recogniser facts:
--   dHalt  (predFlip k0 = O)      <-  hitL k0 = s O      (the proof found at k0)
--   dBelow (predFlip i = s O)     <-  hitL i = O         (no hit strictly below)
-- via  axComp  +  TisZeroSucc / TisZeroZ  (BRA3.Church).  So the mu witness and
-- the dNeg firing are the SAME fact -- the coherence flagged in KGodel1.
--
-- This INSTANTIATES T4.KGodel1.G1 at the concrete  gc = mcode1 predFlip ,
-- gCode = mcode2 (Lift1 out_L) , deriving  dHalt/dBelow/fire  from the search
-- facts in terms of  hitL .  What stays ABSTRACT is the genuine interface +
-- antecedents (per [[feedback_no_eval_strategy_dependence]] -- you cannot compute
-- thmT): the interpreter-correctness black boxes  predReaches / outLReaches , and
-- the search-exists facts  hitAtK0 / noHitBelow (a proof of K(z0)>L is found at
-- the first hit k0) / dSubj (its subject is the numeral z0) / dLen (|g_L| <= L,
-- which pins the canonical L -- the remaining arithmetic).

module T4.KDiag where

open import T4.Base
open import T4.Tags        using ( tag_C )
open import T4.ConInj      using ( ConSchema )
open import T4.KFormula    using ( szLeqApp )
open import T4.KRecog      using ( hitK )
open import T4.KOut        using ( out_L )
open import T4.Code        using ( falseF )
open import T4.EvalU       using ( mcode1 ; mcode2 ; mcodeMu ; cfgEV ; cfgRT )
open import T4.EvalUCorrect using ( Reaches )
open import T4.EvalUMu     using ( Lt )

import T4.KGodel1

open import T4.ProgEnc     using ( enc )
open import T4.ProgParse   using ( parse ; parse_enc ; InAlph ; iaPi )
open import T4.McodeInAlph using
  ( inAlph_natCode ; inAlph_mcode1 ; inAlph_mcode2 ; inAlph_mcodeMu )

open import BRA3.Church      using ( pi ; isZero ; TisZeroZ ; TisZeroSucc )
open import BRA3.Fan         using ( Lift1 ; compose1U )
open import BRA3.PairAlgebra using ( axComp )

------------------------------------------------------------------------
-- The concrete diagonal pieces (functions of the threshold  L ).

-- the mu-predicate:  predFlip L n = isZero (hitL n)  ( = O iff hitL n = s O ).
predFlip : Term -> Fun1
predFlip L = compose1U isZero (hitK L (out_L L))

-- the Fun2 code "apply out_L to the first component" (g of the C-wrapper).
gCodeOf : Term -> Term
gCodeOf L = mcode2 (Lift1 (out_L L))

-- the diagonal program code  ⌜g_L⌝ = C (Lift1 out_L) (mu predFlip) u  (this is
-- KGodel1.G1.gLcode = EvalUMu.Mu.gLCodeOf (gCodeOf L)  definitionally).
gLcode : Term -> Term
gLcode L =
  ap2 pi (natCode tag_C)
    (ap2 pi (gCodeOf L) (ap2 pi (mcodeMu (mcode1 (predFlip L))) (mcode1 u)))

------------------------------------------------------------------------
-- The round-trip  dRT  DISCHARGED (R4):  ⌜g_L⌝  is in the  {O,s,pi} fragment
-- (its C-wrapper over  gCodeOf L = mcode2 (Lift1 ...) , mcodeMu (mcode1 ...) ,
-- mcode1 u ), so  parse (enc ⌜g_L⌝) = ⌜g_L⌝  by  T4.ProgParse.parse_enc .
-- This is poly-size: a small InAlph witness + an INSTANTIATION of the general
-- round-trip (no traversal of the huge code / thmT).

inAlph_gLcode : (L : Term) -> InAlph (gLcode L)
inAlph_gLcode L =
  iaPi (natCode tag_C)
       (ap2 pi (gCodeOf L) (ap2 pi (mcodeMu (mcode1 (predFlip L))) (mcode1 u)))
    (inAlph_natCode tag_C)
    (iaPi (gCodeOf L) (ap2 pi (mcodeMu (mcode1 (predFlip L))) (mcode1 u))
      (inAlph_mcode2 (Lift1 (out_L L)))
      (iaPi (mcodeMu (mcode1 (predFlip L))) (mcode1 u)
        (inAlph_mcodeMu (mcode1 (predFlip L)) (inAlph_mcode1 (predFlip L)))
        (inAlph_mcode1 u)))

dRT_gL : (L : Term) -> Deriv (eqF (ap1 parse (enc (gLcode L))) (gLcode L))
dRT_gL L = parse_enc (gLcode L) (inAlph_gLcode L)

------------------------------------------------------------------------
-- The standalone conditional Chaitin-Goedel-I, with the diagonal CONCRETE and
-- the mu-witness derived from the  hitL  recogniser facts.

chaitin_G1_diag :
  Deriv ConSchema -> (L : Term) (k0 z0 : Nat) ->
  -- interpreter-correctness black boxes (universal instantiation; never compute thmT):
  ((k : Nat) (K : Term) ->
     Reaches (cfgEV (mcode1 (predFlip L)) (natCode k) K)
             (cfgRT (ap1 (predFlip L) (natCode k)) K)) ->
  ((K : Term) ->
     Reaches (cfgEV (gCodeOf L) (ap2 pi (natCode k0) O) K) (cfgRT (natCode z0) K)) ->
  -- search-exists antecedents (the proof of K(z0)>L found at the first hit k0):
  Deriv (eqF (ap1 (hitK L (out_L L)) (natCode k0)) (ap1 s O)) ->          -- hitAtK0 (= fire)
  ((i : Nat) -> Lt i k0 ->
     Deriv (eqF (ap1 (hitK L (out_L L)) (natCode i)) O)) ->               -- noHitBelow (k0 first)
  Deriv (eqF (ap1 (out_L L) (natCode k0)) (natCode z0)) ->                -- dSubj
  Deriv (eqF (szLeqApp L (enc (gLcode L))) (ap1 s O)) ->                  -- dLen (faithful: lenR of the NAME; pins L)
  Deriv falseF
chaitin_G1_diag con L k0 z0 predReaches outLReaches hitAtK0 noHitBelow dSubj dLen =
  let hitL : Fun1
      hitL = hitK L (out_L L)
      -- dHalt:  predFlip k0 = O   from   hitL k0 = s O .
      dHalt : Deriv (eqF (ap1 (predFlip L) (natCode k0)) O)
      dHalt = ruleTrans (axComp isZero hitL (natCode k0))
                (ruleTrans (cong1 isZero hitAtK0)
                           (ruleInst zero O TisZeroSucc))
      -- dBelow:  predFlip i = s O   from   hitL i = O  (i < k0) .
      dBelow : (i : Nat) -> Lt i k0 ->
               Deriv (eqF (ap1 (predFlip L) (natCode i)) (ap1 s O))
      dBelow i lt = ruleTrans (axComp isZero hitL (natCode i))
                      (ruleTrans (cong1 isZero (noHitBelow i lt)) TisZeroZ)
  in T4.KGodel1.G1.chaitin_G1
       con L (mcode1 (predFlip L)) (\ k -> ap1 (predFlip L) (natCode k)) (\ _ -> O)
       predReaches (gCodeOf L) k0 z0 dHalt dBelow outLReaches
       (dRT_gL L) dSubj dLen hitAtK0
