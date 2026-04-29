{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.StrictT12_I
--
-- Strict Theorem 12 at f = I (identity), as a WORKED EXAMPLE of the
-- Fun1-construction technique that  constr5  ultimately needs in
-- BRA.GoedelII.Compose.
--
-- "Strict" Theorem 12 means: build  DI : Fun1  (a primitive-recursive
-- combinator expression in BRA), not just a meta-function on Trees,
-- such that  ap1 DI x  BRA-reduces (at canonical x) to a proof code
-- whose thmT-image is the encoded axI equation at x.
--
-- The construction:
--   DI = Comp2 Pair (KT tagCode_axI) cor
-- gives, by axComp2 + axKT + corOfReify (at canonical input):
--   ap1 DI (reify v) BRA-equals  reify (encAxI (reify v))
-- and then  thmTDispAxI (reify v)  finishes the spec.
--
-- Restricted to CANONICAL inputs (= reify v for v : Tree).  At
-- variable inputs, the construction hits  cor (var v) -- which
-- doesn't BRA-reduce -- and the strict-Theorem-12 spec would need
-- additional ruleIndBT-based machinery for cor at variables.
-- That's outside this file's scope.
--
-- This worked example demonstrates the technique.  Extending to other
-- primitives (Z, Fst, Snd, Comp, etc.) follows the same pattern.
-- The final  constr5  for godelII is a much bigger combinator built
-- the same way, using sub-functors' DI-style witnesses.
--
-- No postulates, no holes.

module BRA.StrictT12_I where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor
open import BRA.Thm.ThmT using (thmT ; thmTDispAxI ; tagCode_axI)
open import BRA.Thm.Parts.AxI using (encAxI ; outAxI)

------------------------------------------------------------------------
-- DI : Fun1.  Built from primitives only.

DI : Fun1
DI = Comp2 Pair (KT tagCode_axI) cor

------------------------------------------------------------------------
-- BRA-reduction of  DI  at canonical input  reify v .

DI_reduce : (v : Tree) ->
  Deriv (atomic (eqn (ap1 DI (reify v)) (reify (encAxI (reify v)))))
DI_reduce v =
  let
    -- Step 1: axComp2 unfolds  ap1 (Comp2 Pair (KT tagCode_axI) cor) (reify v).

    s1 : Deriv (atomic (eqn
            (ap1 DI (reify v))
            (ap2 Pair (ap1 (KT tagCode_axI) (reify v))
                       (ap1 cor (reify v)))))
    s1 = axComp2 Pair (KT tagCode_axI) cor (reify v)

    -- Step 2: axKT (= the derived KT-axiom in BRA.Deriv) reduces
    -- ap1 (KT (reify (natCode tagAxI))) (reify v) = reify (natCode tagAxI)
    -- = tagCode_axI .  Apply via  congL Pair (ap1 cor (reify v)) .

    kt_reduce : Deriv (atomic (eqn (ap1 (KT tagCode_axI) (reify v)) tagCode_axI))
    kt_reduce = axKT (natCode (suc zero)) (reify v)
      -- tagAxI = suc zero, so natCode tagAxI = natCode (suc zero).

    s2 : Deriv (atomic (eqn
            (ap2 Pair (ap1 (KT tagCode_axI) (reify v)) (ap1 cor (reify v)))
            (ap2 Pair tagCode_axI (ap1 cor (reify v)))))
    s2 = congL Pair (ap1 cor (reify v)) kt_reduce

    -- Step 3: corOfReify gives  ap1 cor (reify v) = reify (code (reify v)) .
    -- Apply via  congR Pair tagCode_axI .

    cor_reduce : Deriv (atomic (eqn (ap1 cor (reify v)) (reify (code (reify v)))))
    cor_reduce = corOfReify v

    s3 : Deriv (atomic (eqn
            (ap2 Pair tagCode_axI (ap1 cor (reify v)))
            (ap2 Pair tagCode_axI (reify (code (reify v))))))
    s3 = congR Pair tagCode_axI cor_reduce

    -- The RHS is definitionally equal to  reify (encAxI (reify v))
    -- since  encAxI t = nd (natCode tagAxI) (code t)
    -- and reify of that = ap2 Pair (reify (natCode tagAxI)) (reify (code t))
    --                    = ap2 Pair tagCode_axI (reify (code t)) .

  in ruleTrans s1 (ruleTrans s2 s3)

------------------------------------------------------------------------
-- Strict Theorem 12 at f = I, at canonical input  reify v .
--
-- Final chain:
--   ap1 DI (reify v)             [start]
--    = reify (encAxI (reify v))   [DI_reduce, via axComp2/axKT/corOfReify]
-- Then  thmT  applied:
--   thmT (ap1 DI (reify v))  =  thmT (reify (encAxI (reify v)))
--                            =  reify (outAxI (reify v))
--                            =  reify (codeFormula (atomic (eqn (ap1 I (reify v)) (reify v)))).

DI_strict_T12 : (v : Tree) ->
  Deriv (atomic (eqn (ap1 thmT (ap1 DI (reify v)))
                     (reify (codeFormula
                       (atomic (eqn (ap1 I (reify v)) (reify v)))))))
DI_strict_T12 v =
  let
    -- Step A: cong1 thmT applied to DI_reduce.

    sA : Deriv (atomic (eqn (ap1 thmT (ap1 DI (reify v)))
                            (ap1 thmT (reify (encAxI (reify v))))))
    sA = cong1 thmT (DI_reduce v)

    -- Step B: thmTDispAxI at (reify v) gives the encoded form.

    sB : Deriv (atomic (eqn (ap1 thmT (reify (encAxI (reify v))))
                            (reify (outAxI (reify v)))))
    sB = thmTDispAxI (reify v)

    -- outAxI (reify v) = codeFormula (atomic (eqn (ap1 I (reify v)) (reify v)))
    -- by definition.

  in ruleTrans sA sB
