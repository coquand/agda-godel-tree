{-# OPTIONS --safe --without-K --exact-split #-}

-- instFormGen: schematic bridge lemma for Godel II.
-- After ruleInst v12 then v11 on an equation containing thFunTFor
-- and substTFor, both get their embedded substTFor closed.
-- No computation on replT (can be abstract/huge like crTC).

module Guard.Nelson.InstForm where

open import Guard.Base
open import Guard.Term
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstTForCorrect using (closedSubstTFor)
open import Guard.Nelson.SubstReify
open import Guard.Nelson.SubstTForClose
open import Guard.ThFunTFor using (thFunTFor)
open import Guard.Nelson.ThFunTForSubst

private
  v11 : Nat
  v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat
  v12 = suc v11

------------------------------------------------------------------------
-- instFormGen: the general bridge for Godel II's ruleInst step.

instFormGen : (replT tgtT : Tree) (pa pb tc : Tree) ->
  Eq (substEq v11 (reify replT) (substEq v12 (reify tgtT)
      (eqn (ap2 TreeEq (ap1 thFunTFor (ap2 Pair (reify pa) (reify pb)))
                        (ap1 substTFor (reify tc)))
           (ap2 Pair O O))))
     (eqn (ap2 TreeEq (ap1 (thFunTForClosed replT tgtT)
                            (ap2 Pair (reify pa) (reify pb)))
                       (ap1 (closedSubstTFor (reify replT) (reify tgtT)) (reify tc)))
          (ap2 Pair O O))
instFormGen replT tgtT pa pb tc =
  eqCong2 eqn
    (eqCong2 (ap2 TreeEq)
      (eqCong2 ap1 (thFunTForSubstEq replT tgtT)
        (eqTrans (eqCong (subst v11 (reify replT))
                         (eqCong2 (ap2 Pair) (substReify v12 (reify tgtT) pa)
                                             (substReify v12 (reify tgtT) pb)))
                 (eqCong2 (ap2 Pair) (substReify v11 (reify replT) pa)
                                     (substReify v11 (reify replT) pb))))
      (eqCong2 ap1 (substTForClose replT tgtT)
        (eqTrans (eqCong (subst v11 (reify replT)) (substReify v12 (reify tgtT) tc))
                 (substReify v11 (reify replT) tc))))
    refl
