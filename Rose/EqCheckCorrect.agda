{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.EqCheckCorrect where

open import Rose.Base
  using (Nat; zero; suc; add; add-suc; add-zero;
         Eq; refl; eqSym; eqTrans; eqCong; eqCong2; eqSubst)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.TreeEq using (trueT; falseT; andT; eqTree)
open import Rose.TreeEqInt
  using (linearize; appendR; process; runNiter; extractFlagMeta;
         runNiter-false; runNiter-append)

------------------------------------------------------------------------
-- Tree size.

treeSize : Tree -> Nat
treeSize lf = zero
treeSize (nd a b) = suc (add (treeSize a) (treeSize b))

------------------------------------------------------------------------
-- processN: iterate process n times.

processN : Nat -> Tree -> Tree
processN zero state = state
processN (suc n) state = processN n (process state)

processN-false : (n : Nat) -> (stack : Tree) ->
  Eq (processN n (nd falseT stack)) (nd falseT stack)
processN-false zero stack = refl
processN-false (suc n) stack = processN-false n stack

processN-add : (m n : Nat) -> (state : Tree) ->
  Eq (processN (add m n) state) (processN n (processN m state))
processN-add zero n state = refl
processN-add (suc m) n state = processN-add m n (process state)

------------------------------------------------------------------------
-- Right-spine and linearize properties.

rightSpine : Tree -> Nat
rightSpine lf = zero
rightSpine (nd a k) = suc (rightSpine k)

runNiter-processN : (clock state : Tree) ->
  Eq (runNiter clock state) (processN (rightSpine clock) state)
runNiter-processN lf state = refl
runNiter-processN (nd a k) state = runNiter-processN k (process state)

rightSpine-appendR : (xs ys : Tree) ->
  Eq (rightSpine (appendR xs ys)) (add (rightSpine xs) (rightSpine ys))
rightSpine-appendR lf ys = refl
rightSpine-appendR (nd a xs) ys = eqCong suc (rightSpine-appendR xs ys)

rightSpine-linearize : (t : Tree) ->
  Eq (rightSpine (linearize t)) (treeSize t)
rightSpine-linearize lf = refl
rightSpine-linearize (nd a b) =
  eqCong suc
    (eqTrans (rightSpine-appendR (linearize a) (linearize b))
             (eqCong2 add (rightSpine-linearize a) (rightSpine-linearize b)))

------------------------------------------------------------------------
-- Arithmetic.

add-comm : (m n : Nat) -> Eq (add m n) (add n m)
add-comm zero n = eqSym (add-zero n)
add-comm (suc m) n = eqTrans (eqCong suc (add-comm m n)) (eqSym (add-suc n m))

add-assoc : (a b c : Nat) -> Eq (add (add a b) c) (add a (add b c))
add-assoc zero b c = refl
add-assoc (suc a) b c = eqCong suc (add-assoc a b c)

add-swap-inner : (a b c : Nat) ->
  Eq (add a (add b c)) (add b (add a c))
add-swap-inner a b c =
  eqTrans (eqSym (add-assoc a b c))
    (eqTrans (eqCong (\ x -> add x c) (add-comm a b))
             (add-assoc b a c))

fuel-split : (sa sb sc sd : Nat) ->
  Eq (add (add sa sb) (add sc sd)) (add (add sa sc) (add sb sd))
fuel-split sa sb sc sd =
  eqTrans (add-assoc sa sb (add sc sd))
    (eqTrans (eqCong (add sa) (add-swap-inner sb sc sd))
             (eqSym (add-assoc sa sc (add sb sd))))

-- add (suc x) (suc y) = suc (suc (add x y))
add-suc-suc : (x y : Nat) -> Eq (add (suc x) (suc y)) (suc (suc (add x y)))
add-suc-suc x y = eqCong suc (add-suc x y)

-- The fuel-split lifted to suc:
-- add (suc (add a b)) (suc (add c d)) = add (suc (add a c)) (suc (add b d))
fuel-split-suc : (a b c d : Nat) ->
  Eq (add (suc (add a b)) (suc (add c d)))
     (add (suc (add a c)) (suc (add b d)))
fuel-split-suc a b c d =
  eqTrans (add-suc-suc (add a b) (add c d))
    (eqTrans (eqCong (\ x -> suc (suc x)) (fuel-split a b c d))
             (eqSym (add-suc-suc (add a c) (add b d))))

------------------------------------------------------------------------
-- Flag propagation: if flag is not lf, processN keeps it as falseT.

-- process on state with nd-flag gives falseT flag.
process-nd-flag : (x y : Tree) -> (stack : Tree) ->
  Eq (process (nd (nd x y) stack)) (nd falseT stack)
process-nd-flag x y stack = refl

-- If extractFlagMeta state = falseT, then after processN, flag is still falseT.
-- We prove: for any state = nd (nd x y) stack,
--   processN n (nd (nd x y) stack) = nd falseT stack.
-- (since process (nd (nd x y) stack) = nd falseT stack,
-- and processN-false handles the rest)

-- After one process step, any nd-flag becomes falseT and stays.
processN-suc-nd-flag : (n : Nat) -> (x y : Tree) -> (stack : Tree) ->
  Eq (processN (suc n) (nd (nd x y) stack)) (nd falseT stack)
processN-suc-nd-flag n x y stack = processN-false n stack

------------------------------------------------------------------------
-- andT when first arg is not lf.

andT-nd : (x y z : Tree) -> Eq (andT (nd x y) z) falseT
andT-nd x y z = refl

------------------------------------------------------------------------
-- eqTree only returns lf or nd lf lf: if result is nd x y, then x=lf, y=lf.

eqTree-nd-falseT : (a b x y : Tree) -> Eq (nd x y) (eqTree a b) ->
  Eq (nd x y) falseT
eqTree-nd-falseT lf lf x y ()
eqTree-nd-falseT lf (nd b1 b2) x y p = p
eqTree-nd-falseT (nd a1 a2) lf x y p = p
eqTree-nd-falseT (nd a1 a2) (nd b1 b2) x y p =
  eqTree-nd-byE1 (eqTree a1 b1) a2 b2 x y p
  where
    eqTree-nd-byE1 : (e1 : Tree) -> (a2' b2' x' y' : Tree) ->
      Eq (nd x' y') (andT e1 (eqTree a2' b2')) -> Eq (nd x' y') falseT
    eqTree-nd-byE1 lf a2' b2' x' y' q = eqTree-nd-falseT a2' b2' x' y' q
    eqTree-nd-byE1 (nd c d) a2' b2' x' y' q = q

------------------------------------------------------------------------
-- Main lemma: eqPN and eqPN-eq (mutual).
--
-- eqPN: extractFlagMeta of the result = eqTree a b.
-- eqPN-eq: when eqTree a b = lf, the full state is nd lf rest.

mutual

  eqPN : (a b rest : Tree) ->
    Eq (extractFlagMeta
         (processN (suc (add (treeSize a) (treeSize b)))
                   (nd lf (nd (nd a b) rest))))
       (eqTree a b)
  eqPN lf lf rest = refl
  eqPN lf (nd b1 b2) rest =
    eqCong extractFlagMeta
      (processN-false (add (treeSize lf) (treeSize (nd b1 b2))) rest)
  eqPN (nd a1 a2) lf rest =
    eqCong extractFlagMeta
      (processN-false (add (treeSize (nd a1 a2)) (treeSize lf)) rest)
  eqPN (nd a1 a2) (nd b1 b2) rest =
      -- After first step (definitional): state = nd lf [(a1,b1), (a2,b2), rest]
      -- Fuel = add (suc (add sa1 sa2)) (suc (add sb1 sb2))
      -- Rewrite fuel, split, and combine.
      eqSubst
        (\ n -> Eq (extractFlagMeta (processN n
                     (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest)))))
                   (andT (eqTree a1 b1) (eqTree a2 b2)))
        (eqSym (fuel-split-suc (treeSize a1) (treeSize a2)
                                (treeSize b1) (treeSize b2)))
        (eqTrans
          (eqCong extractFlagMeta
            (processN-add (suc (add (treeSize a1) (treeSize b1)))
                          (suc (add (treeSize a2) (treeSize b2)))
                          (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest)))))
          (eqPN-combine a1 a2 b1 b2 rest))

    -- After splitting: processN S2 (processN S1 state).
    -- Case-split on eqTree a1 b1 to handle both branches.
  eqPN-combine : (a1 a2 b1 b2 rest : Tree) ->
      Eq (extractFlagMeta
            (processN (suc (add (treeSize a2) (treeSize b2)))
              (processN (suc (add (treeSize a1) (treeSize b1)))
                (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest))))))
         (andT (eqTree a1 b1) (eqTree a2 b2))
  eqPN-combine a1 a2 b1 b2 rest =
      eqPN-combine-help a1 a2 b1 b2 rest (eqTree a1 b1) refl

  eqPN-combine-help : (a1 a2 b1 b2 rest : Tree) ->
      (flag1 : Tree) -> Eq flag1 (eqTree a1 b1) ->
      Eq (extractFlagMeta
            (processN (suc (add (treeSize a2) (treeSize b2)))
              (processN (suc (add (treeSize a1) (treeSize b1)))
                (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest))))))
         (andT flag1 (eqTree a2 b2))
  eqPN-combine-help a1 a2 b1 b2 rest lf p =
      -- eqTree a1 b1 = lf (match)
      -- By eqPN-eq: processN S1 state = nd lf (nd (nd a2 b2) rest)
      eqSubst
        (\ x -> Eq (extractFlagMeta
                      (processN (suc (add (treeSize a2) (treeSize b2))) x))
                   (eqTree a2 b2))
        (eqSym (eqPN-eq a1 b1 (nd (nd a2 b2) rest) p))
        (eqPN a2 b2 rest)
  eqPN-combine-help a1 a2 b1 b2 rest (nd x y) p =
      -- eqTree a1 b1 = nd x y (mismatch)
      -- By eqPN: extractFlagMeta (processN S1 state) = nd x y
      -- The state has flag = nd x y. processN S2 propagates falseT.
      eqPN-false-propagate a1 b1 a2 b2 rest x y p

    -- When eqTree a1 b1 = nd x y, the whole thing gives falseT.
  eqPN-false-propagate : (a1 b1 a2 b2 rest : Tree) ->
      (x y : Tree) -> Eq (nd x y) (eqTree a1 b1) ->
      Eq (extractFlagMeta
            (processN (suc (add (treeSize a2) (treeSize b2)))
              (processN (suc (add (treeSize a1) (treeSize b1)))
                (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest))))))
         falseT
  eqPN-false-propagate a1 b1 a2 b2 rest x y p =
      -- eqPN gives: extractFlagMeta (processN S1 state) = eqTree a1 b1
      -- eqSym p: eqTree a1 b1 = nd x y
      -- eqTree-nd-falseT: nd x y = falseT
      -- So extractFlagMeta (processN S1 state) = falseT.
      -- Then extractFlagStable propagates through S2 more steps.
      extractFlagStable
        (processN (suc (add (treeSize a1) (treeSize b1)))
          (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest))))
        (suc (add (treeSize a2) (treeSize b2)))
        (eqTrans (eqPN a1 b1 (nd (nd a2 b2) rest))
                 (eqTrans (eqSym p)
                          (eqTree-nd-falseT a1 b1 x y p)))

    -- If extractFlagMeta state = nd x y, then processN keeps flag as falseT.
  extractFlagStable : (state : Tree) -> (n : Nat) ->
      Eq (extractFlagMeta state) falseT ->
      Eq (extractFlagMeta (processN n state)) falseT
  extractFlagStable lf n ()
  extractFlagStable (nd flag stack) zero p = p
  extractFlagStable (nd flag stack) (suc n) p =
      eqSubst
        (\ f -> Eq (extractFlagMeta (processN (suc n) (nd f stack))) falseT)
        (eqSym p)
        (eqCong extractFlagMeta (processN-suc-nd-flag n lf lf stack))

    -- When eqTree a b = lf, processN gives nd lf rest (state fully processed).
  eqPN-eq : (a b rest : Tree) -> Eq lf (eqTree a b) ->
      Eq (processN (suc (add (treeSize a) (treeSize b)))
            (nd lf (nd (nd a b) rest)))
         (nd lf rest)
  eqPN-eq lf lf rest p = refl
  eqPN-eq lf (nd b1 b2) rest ()
  eqPN-eq (nd a1 a2) lf rest ()
  eqPN-eq (nd a1 a2) (nd b1 b2) rest p =
      -- eqTree (nd a1 a2) (nd b1 b2) = andT (eqTree a1 b1) (eqTree a2 b2) = lf
      -- So eqTree a1 b1 = lf and eqTree a2 b2 = lf.
      eqPN-eq-nd a1 a2 b1 b2 rest (eqTree a1 b1) (eqTree a2 b2) refl refl p

  eqPN-eq-nd : (a1 a2 b1 b2 rest : Tree) ->
      (e1 e2 : Tree) -> Eq e1 (eqTree a1 b1) -> Eq e2 (eqTree a2 b2) ->
      Eq lf (andT e1 e2) ->
      Eq (processN (suc (add (suc (add (treeSize a1) (treeSize a2)))
                              (suc (add (treeSize b1) (treeSize b2)))))
            (nd lf (nd (nd (nd a1 a2) (nd b1 b2)) rest)))
         (nd lf rest)
  eqPN-eq-nd a1 a2 b1 b2 rest lf lf p1 p2 q =
      -- Both eqTree = lf. Fuel split + IH.
      -- The goal after normalization should reduce the first processN step.
      eqSubst (\ n -> Eq (processN n
                 (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest))))
               (nd lf rest))
        (eqSym (fuel-split-suc (treeSize a1) (treeSize a2)
                                (treeSize b1) (treeSize b2)))
        (eqTrans
          (processN-add (suc (add (treeSize a1) (treeSize b1)))
                        (suc (add (treeSize a2) (treeSize b2)))
                        (nd lf (nd (nd a1 b1) (nd (nd a2 b2) rest))))
          (eqTrans
            (eqCong (processN (suc (add (treeSize a2) (treeSize b2))))
              (eqPN-eq a1 b1 (nd (nd a2 b2) rest) p1))
            (eqPN-eq a2 b2 rest p2)))
  eqPN-eq-nd a1 a2 b1 b2 rest lf (nd x y) p1 p2 ()
  eqPN-eq-nd a1 a2 b1 b2 rest (nd x y) e2 p1 p2 ()

------------------------------------------------------------------------
-- Corollary: eqCheck-main.

-- Convert runNiter to processN: runNiter clock state = processN (rightSpine clock) state.
-- rightSpine (linearize (nd a b)) = suc (add (rightSpine (linearize a)) (rightSpine (linearize b)))
-- = suc (add (treeSize a) (treeSize b))  by rightSpine-linearize.

rsLin : (a b : Tree) ->
  Eq (rightSpine (linearize (nd a b))) (suc (add (treeSize a) (treeSize b)))
rsLin a b = eqCong suc (eqTrans
  (rightSpine-appendR (linearize a) (linearize b))
  (eqCong2 add (rightSpine-linearize a) (rightSpine-linearize b)))

eqCheck-main : (a b : Tree) ->
  Eq (extractFlagMeta (runNiter (linearize (nd a b)) (nd lf (nd (nd a b) lf))))
     (eqTree a b)
eqCheck-main a b =
  eqTrans
    (eqCong extractFlagMeta
      (eqTrans
        (runNiter-processN (linearize (nd a b)) (nd lf (nd (nd a b) lf)))
        (eqSubst (\ n -> Eq (processN (rightSpine (linearize (nd a b)))
                                       (nd lf (nd (nd a b) lf)))
                             (processN n (nd lf (nd (nd a b) lf))))
          (rsLin a b) refl)))
    (eqPN a b lf)

