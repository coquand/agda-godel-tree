{-# OPTIONS --safe --without-K --exact-split #-}

-- Schematic proof: double substitution on substTFor gives closedSubstTFor.
-- This corresponds to Rose's observation that substituting the parameters
-- into the open form yields the closed form — no computation on specific values.

module Guard.SubstTForClose where

open import Guard.Base
open import Guard.Term
open import Guard.SubstTFor
open import Guard.SubstTForCorrect using (closedSubstTFor)
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.SubstReify

private
  v11 : Nat
  v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat
  v12 = suc v11

------------------------------------------------------------------------
-- substTForClose: double substitution on substTFor gives closedSubstTFor.
-- Order: v12 first (inner), then v11 (outer).
-- This order ensures substReify is only needed on tgtT (small),
-- never on replT (which can be large, e.g. crTC ~400K nodes).

substTForClose : (replT tgtT : Tree) ->
  Eq (substF1 v11 (reify replT) (substF1 v12 (reify tgtT) substTFor))
     (closedSubstTFor (reify replT) (reify tgtT))
substTForClose replT tgtT = eqCong (Rec O) stepEq
  where
  repl : Term ; repl = reify replT
  tgt  : Term ; tgt  = reify tgtT

  stepEq : Eq (substF2 v11 repl (substF2 v12 tgt stepSubst))
              (cStepOf repl tgt)
  stepEq = eqCong (\t -> Fan (Fan (Lift Fst) (Lift (KT (reify tagVar))) TreeEq)
                            (Fan (Fan (Fan (Lift Snd) (Lift (KT t)) TreeEq)
                                      (Fan (Lift (KT repl)) Const Pair) IfLf)
                                 (Post Snd Pair) Pair) IfLf)
                   (substReify v11 repl tgtT)

