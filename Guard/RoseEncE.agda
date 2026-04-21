{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.RoseEncE -- Rose's  e(t)  encoder: code of "A = B" -> code of "A != B".
--
-- Rose (1967) p.381: "if t is the number of the equation A = B then
-- e(t) is the number of A != B".
--
-- In our tree setting, "A != B" is internally represented as the
-- equation  eqn (ap2 TreeEq A B) falseT  (characteristic TreeEq value
-- is poo, not O).  So  e  is a simple structural map at the code
-- level:
--
--   e (codeEqn (eqn A B)) = codeEqn (eqn (ap2 TreeEq A B) falseT)
--                         = nd (code (ap2 TreeEq A B))
--                              (code falseT)
--                         = nd (nd tagAp2 (nd (codeF2 TreeEq)
--                                             (nd (code A) (code B))))
--                              (code falseT)
--
-- So if  t = nd aC bC  (where aC = code A, bC = code B), then
--   e(t) = nd (nd tagAp2 (nd (codeF2 TreeEq) (nd aC bC))) (code falseT).
--
-- At the Term level with  t = reify (nd aC bC)  (= ap2 Pair (reify aC)
-- (reify bC)), the output is:
--   ap2 Pair (reify (nd tagAp2 (nd (codeF2 TreeEq) (nd aC bC))))
--            (reify codeFalse)
-- which we expose both as a Tree->Tree function and as the Term-level
-- meta-function accepting a Pair-shaped Term input.

module Guard.RoseEncE where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun using (codeEqn)

------------------------------------------------------------------------
-- The "codeFalse" tree: code of the Term  falseT = ap2 Pair O O .

codeFalse : Tree
codeFalse = code (ap2 Pair O O)

-- Sanity (definitional): codeFalse unfolds to nd tagAp2 (nd (codeF2
-- Pair) (nd (nd tagO lf) (nd tagO lf))).

codeFalseForm : Eq codeFalse (nd tagAp2 (nd (codeF2 Pair)
                                          (nd (nd tagO lf) (nd tagO lf))))
codeFalseForm = refl

------------------------------------------------------------------------
-- eTree : Tree -> Tree.  Applied to a code of  eqn A B , yields the
-- code of  eqn (ap2 TreeEq A B) falseT .

eTree : Tree -> Tree
eTree lf       = lf  -- nonsense input; don't care
eTree (nd aC bC) =
  nd (nd tagAp2 (nd (codeF2 TreeEq) (nd aC bC)))
     codeFalse

-- Correctness at the meta-level: eTree (codeEqn (eqn A B)) = codeEqn
-- (eqn (ap2 TreeEq A B) falseT).

eTreeCorrect : (a b : Term) ->
  Eq (eTree (codeEqn (eqn a b)))
     (codeEqn (eqn (ap2 TreeEq a b) (ap2 Pair O O)))
eTreeCorrect a b = refl

------------------------------------------------------------------------
-- Term-level version.  Given a Term representing  reify (codeEqn (eqn
-- A B))  in the canonical form  ap2 Pair (reify aC) (reify bC) , we
-- build the output Term directly.

eTerm : (aC bC : Term) -> Term
eTerm aC bC =
  ap2 Pair
    (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 TreeEq))
                        (ap2 Pair aC bC)))
    (reify codeFalse)

-- Bridge: eTerm (reify aC) (reify bC) = reify (eTree (nd aC bC)).

eTermIsReifyETree : (aC bC : Tree) ->
  Eq (eTerm (reify aC) (reify bC))
     (reify (eTree (nd aC bC)))
eTermIsReifyETree aC bC = refl
