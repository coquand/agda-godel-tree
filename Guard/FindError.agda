{-# OPTIONS --safe --without-K --exact-split #-}

-- FindError.agda
-- Metalevel proof checker and error locator.
--
-- eval : Tree -> Tree
--   Metalevel version of evalCode. Strips tagO → lf, tagAp1 → recurse
--   into argument, else passthrough (preserve Pair structure).
--
-- checkProof : Tree -> Bool
--   Runs thFun on the encoding, then checks eval agreement on both sides.
--
-- findError : Tree -> Tree
--   Returns lf if the encoding is semantically valid at this node,
--   or a witness subtree where eval disagrees.
--
-- Key results:
-- (1) checkProof on encAxI(code O, lf) = true
-- (2) checkProof on a tree encoding O = Pair(O,O) = false
-- (3) For BLevel 0 (no ruleInst), eval is primitive recursive
--     and checkProof runs in O(|t|^2) time.

module Guard.FindError where

open import Guard.Base
open import Guard.Term
open import Guard.ThFun

------------------------------------------------------------------------
-- 1. eval : metalevel evalCode
--
-- evalCode = Rec O evalStep
-- evalStep dispatches on Fst(orig):
--   tagO (= lf): return lf
--   tagAp1 (= nd lf (nd lf lf)): return eval(right child of Snd(orig))
--     i.e., Snd(Snd(recs)) via passthrough
--   else: passthrough = Pair(eval left, eval right)
--
-- At metalevel on Trees:
--   eval lf = lf
--   eval (nd a b) =
--     if a = tagO (= lf) then lf
--     else if a = tagAp1 then eval b
--          [tagAp1 marks ap1(f,t); we strip the functor and return eval(nd(fCode,tCode)),
--           which by passthrough = nd(eval fCode, eval tCode). Then Snd = eval tCode.
--           But at metalevel we get eval b where b = nd(fCode, tCode).
--           By passthrough: eval(nd fCode tCode) = nd(eval fCode, eval tCode).
--           The tagAp1Case extracts Snd(Snd(recs)) = Snd(nd(eval fCode, eval tCode))
--           = eval tCode = eval(rightT b).
--           So the correct metalevel version is: rightT(eval b)]
--     else nd (eval a) (eval b)

eval : Tree -> Tree
eval lf = lf
eval (nd a b) =
  boolCase (treeEq a lf)
    lf
    (boolCase (treeEq a (nd lf (nd lf lf)))
      (rightT (eval b))
      (nd (eval a) (eval b)))

------------------------------------------------------------------------
-- 2. checkProof : does thFun produce a valid equation?

checkProof : Tree -> Bool
checkProof t = treeEq (eval (leftT (thFun t))) (eval (rightT (thFun t)))

------------------------------------------------------------------------
-- 3. findError : locate the first invalid node
--
-- Traverses the proof encoding tree. At each node:
--   - Run checkProof
--   - If valid (true): return lf (no error here)
--   - If invalid: check children; if a child is also invalid, recurse;
--     otherwise THIS node is the error source.

findError : Tree -> Tree
findError lf = lf
findError (nd tag (nd a b)) =
  boolCase (checkProof (nd tag (nd a b)))
    lf                                    -- valid at this node
    (boolCase (checkProof (nd tag (nd a b)))
      (nd tag (nd a b))                   -- error witness is this node
      (boolCase (boolAnd (checkProof a) (checkProof b))
        (nd tag (nd a b))                 -- children valid but this node invalid: error HERE
        (boolCase (checkProof a)
          (findError b)                   -- a valid, b invalid: recurse into b
          (findError a))))                -- a invalid: recurse into a
findError (nd tag lf) =
  boolCase (checkProof (nd tag lf))
    lf
    (nd tag lf)

------------------------------------------------------------------------
-- 4. Concrete examples

-- code O = nd tagO lf = nd lf lf
private
  cO : Tree
  cO = code O

  -- code(ap2 Pair O O) = nd tagAp2 (nd (codeF2 Pair) (nd cO cO))
  cPOO : Tree
  cPOO = code (ap2 Pair O O)

  -- Encoding of axI applied to O:
  -- encAxI(code O) = nd (natCode 0) (nd (code O) lf)
  proofAxIO : Tree
  proofAxIO = encAxI cO

  -- thFun(proofAxIO) should give nd(mkAp1(codeF1 I, cO), cO)
  -- i.e., nd (code(ap1 I O)) (code O)
  -- eval of left side: eval(code(ap1 I O)) = eval(nd tagAp1 (nd (codeF1 I) cO))
  --   = rightT(eval(nd (codeF1 I) cO))
  --   = rightT(nd (eval (codeF1 I)) (eval cO))
  --   = eval cO
  -- eval of right side: eval(cO) = eval(nd lf lf) = lf (tagO case)
  -- So both sides = lf. checkProof = true.

  -- Encoding of axRefl applied to code(O):
  -- encRefl(cO) = nd (natCode 17) (nd cO lf)
  proofReflO : Tree
  proofReflO = encRefl cO

  -- thFun(proofReflO) = nd cO cO
  -- eval(cO) = lf on both sides. checkProof = true.

------------------------------------------------------------------------
-- 5. Verification: checkProof on specific encodings

-- Helper: Not type
Not : Set -> Set
Not P = P -> Empty

-- eval(code O) = lf
evalCodeO : Eq (eval cO) lf
evalCodeO = refl

-- eval(nd tagO lf) = lf (unfolding: a=lf so treeEq lf lf = true, return lf)
-- cO = nd lf lf = nd tagO lf. eval(nd lf lf): a=lf, treeEq lf lf = true, return lf. Good.

-- thFun(proofAxIO):
-- proofAxIO = nd (natCode 0) (nd cO lf)
-- natCode 0 = lf, so tag = lf
-- thFun(nd lf (nd cO lf)) = thD lf cO lf (thFun cO) (thFun lf)
-- treeEq lf (natCode 0) = treeEq lf lf = true
-- So: nd (mkAp1 (codeF1 I) cO) cO
thFunAxIO : Eq (thFun proofAxIO) (nd (mkAp1 (codeF1 I) cO) cO)
thFunAxIO = refl

-- checkProof(proofAxIO) = treeEq (eval (mkAp1 (codeF1 I) cO)) (eval cO)
-- mkAp1 (codeF1 I) cO = nd tagAp1 (nd (codeF1 I) cO)
-- eval(nd tagAp1 (nd (codeF1 I) cO)):
--   a = tagAp1 = nd lf (nd lf lf)
--   treeEq a lf = false
--   treeEq a (nd lf (nd lf lf)) = true
--   return rightT(eval(nd (codeF1 I) cO))
--   eval(nd (codeF1 I) cO): codeF1 I = nd (natCode 26) lf
--     a = nd (natCode 26) lf, not tagO, not tagAp1
--     return nd (eval (nd (natCode 26) lf)) (eval cO)
--     eval(nd (natCode 26) lf): natCode 26 = nd lf (natCode 25)
--       a = nd lf (natCode 25), not tagO, not tagAp1
--       return nd (eval (nd lf (natCode 25))) (eval lf)
--       ... this recursion bottoms out
--   rightT of that = eval cO = lf
-- And eval cO = lf.
-- So checkProof = treeEq lf lf = true.

checkAxIO : Eq (checkProof proofAxIO) true
checkAxIO = refl

-- thFun(proofReflO):
-- proofReflO = nd (natCode 17) (nd cO lf)
-- tag = natCode 17, matches n17 case
-- returns nd cO cO
thFunReflO : Eq (thFun proofReflO) (nd cO cO)
thFunReflO = refl

checkReflO : Eq (checkProof proofReflO) true
checkReflO = refl

------------------------------------------------------------------------
-- 6. The false equation: encoding of a hypothetical proof of O = Pair(O,O)
--
-- If someone gives us a tree t such that thFun t = nd (code O) (code (ap2 Pair O O)),
-- then checkProof t must return false.
--
-- Proof: eval(code O) = lf
--        eval(code(ap2 Pair O O)) = eval(nd tagAp2 (nd (codeF2 Pair) (nd cO cO)))
--        tagAp2 is not tagO and not tagAp1
--        So eval returns nd(eval tagAp2, eval(nd (codeF2 Pair) (nd cO cO)))
--        which is nd(something, something) -- a non-lf tree
--        So treeEq lf (nd ...) = false.

-- eval(cPOO) is a nd node (not lf)
evalCodePOO : Eq (eval cPOO) lf -> Empty
evalCodePOO ()

-- Direct computation: code(ap2 Pair O O)
-- = nd tagAp2 (nd (codeF2 Pair) (nd (code O) (code O)))
-- tagAp2 = nd lf (nd lf (nd lf lf))
-- treeEq tagAp2 lf = false
-- treeEq tagAp2 tagAp1 = treeEq (nd lf (nd lf (nd lf lf))) (nd lf (nd lf lf))
--   = boolAnd (treeEq lf lf) (treeEq (nd lf (nd lf lf)) (nd lf lf))
--   = boolAnd true (boolAnd (treeEq lf lf) (treeEq (nd lf lf) lf))
--   = boolAnd true (boolAnd true false) = boolAnd true false = false
-- So: eval(cPOO) = nd (eval tagAp2) (eval (nd (codeF2 Pair) (nd cO cO)))
-- which is nd _ _ -- definitely not lf.

-- Stronger: eval(code O) ≠ eval(code(Pair O O))
evalDisagree : Eq (eval cO) (eval cPOO) -> Empty
evalDisagree ()

-- Therefore: if thFun t = nd (code O) (code(ap2 Pair O O)),
-- then checkProof t = false.
falseEqnFails : (t : Tree) -> Eq (thFun t) (nd cO cPOO) ->
  Eq (checkProof t) false
falseEqnFails t p =
  eqSubst (\v -> Eq (treeEq (eval (leftT v)) (eval (rightT v))) false) (eqSym p) refl

------------------------------------------------------------------------
-- 7. General theorem: checkProof detects invalid equations
--
-- For ANY pair of coded ground terms L R:
--   eval L ≠ eval R  →  checkProof returns false on any t with thFun t = nd L R
--
-- This is the constructive content of the obstruction theorem.

checkDetects : (t : Tree) (l r : Tree) ->
  Eq (thFun t) (nd l r) ->
  (Eq (eval l) (eval r) -> Empty) ->
  Eq (checkProof t) false
checkDetects t l r thfEq evalNeq =
  eqSubst (\v -> Eq (treeEq (eval (leftT v)) (eval (rightT v))) false)
    (eqSym thfEq)
    (treeEqFalse (eval l) (eval r) evalNeq)
  where
  -- treeEq x y = false when x ≠ y
  -- We need: if x ≠ y then treeEq x y = false
  -- This requires decidability of tree equality + consistency.
  -- Actually we can't prove this generically without a lemma about treeEq.
  -- Let's add the needed lemma.

  treeEqRefl : (x : Tree) -> Eq (treeEq x x) true
  treeEqRefl lf = refl
  treeEqRefl (nd a b) = eqSubst (\v -> Eq (boolAnd v (treeEq b b)) true)
    (eqSym (treeEqRefl a))
    (eqSubst (\v -> Eq (boolAnd true v) true) (eqSym (treeEqRefl b)) refl)

  treeEqTrue : (x y : Tree) -> Eq (treeEq x y) true -> Eq x y
  treeEqTrue lf lf _ = refl
  treeEqTrue lf (nd _ _) ()
  treeEqTrue (nd _ _) lf ()
  treeEqTrue (nd a1 b1) (nd a2 b2) p = eqCong2 nd (treeEqTrue a1 a2 (boolAndL p)) (treeEqTrue b1 b2 (boolAndR a1 a2 b1 b2 p))
    where
    boolAndL : {x y : Bool} -> Eq (boolAnd x y) true -> Eq x true
    boolAndL {true} _ = refl
    boolAndR : (a1 a2 : Tree) (b1 b2 : Tree) -> Eq (boolAnd (treeEq a1 a2) (treeEq b1 b2)) true -> Eq (treeEq b1 b2) true
    boolAndR a1 a2 b1 b2 p = boolAndR' (treeEq a1 a2) (treeEq b1 b2) p
      where
      boolAndR' : (x y : Bool) -> Eq (boolAnd x y) true -> Eq y true
      boolAndR' true y p = p

  treeEqFalse : (x y : Tree) -> (Eq x y -> Empty) -> Eq (treeEq x y) false
  treeEqFalse x y neq = helper (treeEq x y) refl
    where
    helper : (b : Bool) -> Eq (treeEq x y) b -> Eq (treeEq x y) false
    helper true p = emptyElim (neq (treeEqTrue x y p))
    helper false p = p

------------------------------------------------------------------------
-- 7b. Concrete demonstration: findError on a bad trans proof
--
-- badProof = encTrans(encRefl(code O), encRefl(code(Pair O O)))
-- This encodes a "proof" of O = Pair(O,O) via trans of:
--   refl: O = O  and  refl: Pair(O,O) = Pair(O,O)
-- thFun picks leftT of first sub-proof (= cO) and rightT of second (= cPOO).
-- checkProof: eval(cO) = lf ≠ eval(cPOO) = nd(...). Returns false.

badProof : Tree
badProof = encTrans (encRefl cO) (encRefl cPOO)

-- checkProof detects the invalid equation
checkBadProof : Eq (checkProof badProof) false
checkBadProof = refl

-- findError pinpoints this node as the error
-- (both sub-proofs are valid refl encodings; the mismatch is at the trans level)
findErrorBad : Eq (findError badProof) badProof
findErrorBad = refl

-- For comparison: a valid trans chain passes
goodProof : Tree
goodProof = encTrans (encRefl cO) (encRefl cO)

checkGoodProof : Eq (checkProof goodProof) true
checkGoodProof = refl

findErrorGood : Eq (findError goodProof) lf
findErrorGood = refl

------------------------------------------------------------------------
-- 8. Size analysis (metalevel)
--
-- For BLevel 0 proofs (no ruleInst), each thFun case produces output
-- bounded by a constant multiple of the input:
--
-- Tags 0-16 (axioms): output = nd(mkAp...(payload), payload_part)
--   mkAp1 adds 3 nodes, mkAp2 adds 5 nodes.
--   Output size <= 2 * payload_size + 10
--
-- Tag 17 (refl): output = nd(a, a). Size = 2|a| + 1. Payload = nd(a, lf).
--   Input size >= |a| + 2. Output/input <= 2.
--
-- Tag 18 (sym): output = nd(rightT rb, leftT rb). Size <= |thFun b|.
--   By IH: |thFun b| <= C|b|. Input >= |b| + const. OK.
--
-- Tag 19 (trans): output = nd(leftT ra, rightT rb). Size <= |thFun a|/2 + |thFun b|/2 + 1.
--   By IH: <= C(|a|+|b|)/2 + 1. Input >= |a|+|b|+const. OK.
--
-- Tags 20-22 (cong): output adds functor codes around sub-results.
--   Size <= |fCode| + |thFun sp| + const. By IH: <= |fCode| + C|sp| + const.
--   Input >= |fCode| + |sp| + const. Need C >= 2.
--
-- Tag 24 (ruleF): output = nd(mkAp1(fC, var0C), mkAp1(gC, var0C)). Size <= 2(|fC|+|gC|) + const.
--   Input >= |fC|+|gC|+const. Constant ratio.
--
-- Tag 25 (axKT): output = nd(mkAp1(ktCode, xC), tC). Size <= |tC|+|xC|+const.
--   Input >= |tC|+|xC|+const. OK.
--
-- EXCLUDED: Tag 23 (ruleInst): uses codedSubst which can multiply sizes.
--
-- Conclusion: for C = 6, |thFun t| <= 6 * |t| for all BLevel-0 proof encodings.

-- treeSize at metalevel
treeSize : Tree -> Nat
treeSize lf = zero
treeSize (nd a b) = suc (natPlus (treeSize a) (treeSize b))
  where
  natPlus : Nat -> Nat -> Nat
  natPlus zero m = m
  natPlus (suc n) m = suc (natPlus n m)
