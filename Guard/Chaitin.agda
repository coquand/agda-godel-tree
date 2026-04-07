{-# OPTIONS --safe --without-K --exact-split #-}

-- Chaitin.agda
-- The Chaitin search machine for the Kritchman-Raz argument.
--
-- Key result: for each l, there is a program C_l of code-size FIXED + O(log l)
-- that, if the system is consistent, outputs an incompressible string xi
-- with K(xi) > l.  For large l, |C_l| < l, giving the contradiction.
--
-- Structure:
--   1. Binary encoding of naturals (O(log n) tree-size)
--   2. Tree enumeration (metalevel bijection Nat <-> Tree)
--   3. The Chaitin search step (FIXED Fun1)
--   4. Code-size bound
--   5. KR contradiction

module Guard.Chaitin where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.Machine using (iterate ; iterStep ; iterBase ; iterNd ;
                                  prepend0 ; prepend1 ; tailSafe ; headSafe ;
                                  Leq ; leqZ ; leqS ; Lt ; ltBase ; ltStep ;
                                  List ; nil ; cons ; listLen ; append ;
                                  natAdd ; treeSize ; progSize)
open import Guard.ThFun
open import Guard.GroundEval
open import Guard.KR using (NoSmallProg ; treeEqDec ; Dec ; yes ; no ; natLeqB)

------------------------------------------------------------------------
-- 1. Binary encoding of naturals
--
-- binCode n encodes n in binary using nd/lf:
--   binCode 0 = lf
--   binCode (2k+1) = nd lf (binCode k)      -- bit 0 prefix
--   binCode (2k+2) = nd (nd lf lf) (binCode k)  -- bit 1 prefix
--
-- treeSize(binCode n) = floor(log2(n+1)) for n > 0
-- This is O(log n), much better than natCode's O(n).

-- Binary encoding with explicit fuel (= n itself suffices as fuel)
private
  half : Nat -> Nat
  half zero = zero
  half (suc zero) = zero
  half (suc (suc n)) = suc (half n)

  isEven : Nat -> Bool
  isEven zero = true
  isEven (suc zero) = false
  isEven (suc (suc n)) = isEven n

  binCodeF : Nat -> Nat -> Tree
  binCodeF zero _ = lf
  binCodeF (suc _) zero = lf
  binCodeF (suc f) (suc n) =
    boolCase (isEven n)
      (nd lf (binCodeF f (half n)))
      (nd (nd lf lf) (binCodeF f (half n)))

binCode : Nat -> Tree
binCode n = binCodeF n n

-- Tests
private
  bc0 : Eq (binCode zero) lf ; bc0 = refl
  bc1 : Eq (binCode (suc zero)) (nd lf lf) ; bc1 = refl
  bc2 : Eq (binCode (suc (suc zero))) (nd (nd lf lf) lf) ; bc2 = refl
  bc3 : Eq (binCode (suc (suc (suc zero)))) (nd lf (nd lf lf)) ; bc3 = refl

------------------------------------------------------------------------
-- 2. Tree enumeration (metalevel)
--
-- Bijection Nat <-> Tree via Cantor pairing.
-- Every tree is reachable: enum is surjective.

-- Cantor pairing function: Nat x Nat -> Nat
-- pair(i, j) = (i + j)(i + j + 1)/2 + i
private
  triangle : Nat -> Nat
  triangle zero = zero
  triangle (suc n) = suc (natAdd n (triangle n))

cantorPair : Nat -> Nat -> Nat
cantorPair i j = natAdd i (triangle (natAdd i j))

-- Cantor unpairing (inverse)
-- Finds the unique (i, j) with cantorPair i j = n
cantorUnpair : Nat -> Sigma Nat (\_ -> Nat)
cantorUnpair = go zero zero
  where
  go : Nat -> Nat -> Nat -> Sigma Nat (\_ -> Nat)
  go i zero zero = mkSigma i zero          -- exhausted this diagonal, found it
  go i zero (suc n) = go zero (suc i) n    -- next diagonal
  go i (suc j) zero = mkSigma i (suc j)    -- found it
  go i (suc j) (suc n) = go (suc i) j n    -- advance along diagonal

-- Tree enumeration: Nat -> Tree (fuel-based)
treeEnumF : Nat -> Nat -> Tree
treeEnumF zero _ = lf
treeEnumF (suc _) zero = lf
treeEnumF (suc f) (suc n) =
  let ij = cantorUnpair n
  in nd (treeEnumF f (fst ij)) (treeEnumF f (snd ij))

treeEnum : Nat -> Tree
treeEnum n = treeEnumF n n

-- Surjectivity: every tree t has some index n with treeEnum n = t
-- (metalevel proof by induction on t)
-- For lf: n = 0.
-- For nd(a, b): if a = treeEnum(i) and b = treeEnum(j),
--   then nd(a,b) = treeEnum(suc(cantorPair i j)).

treeEnumLf : Eq (treeEnum zero) lf
treeEnumLf = refl

------------------------------------------------------------------------
-- 3. Metalevel proof checking + pattern matching
--
-- For the Chaitin search, we need:
-- (a) Check if a tree encodes a valid proof (thFun + geval agreement)
-- (b) Check if the proved equation says "p(t) ≠ xi" for programs of bounded size
-- (c) Extract xi from the proof
--
-- The "K(xi) > l" statement in our system:
--   For EACH program p with progSize(p) <= l,
--   for each clock c,
--   there is a proof that ap1 p (reify(natCode c)) ≠ reify(xi).
--
-- But the Chaitin search finds a SINGLE proof.
-- The actual statement the search looks for:
--   A proof of "TreeEq(ap1 p (reify(natCode c)), reify(xi)) = Pair(O,O)"
--   for some specific p, c, xi.
--
-- The COLLECTION of such proofs (one per program) constitutes "K(xi) > l".
--
-- For the machine: the search state tracks which (program, clock) pairs
-- have been verified. When all pairs for programs of size <= l are checked,
-- the xi is confirmed incompressible.

-- Check a single "nonequality" proof at metalevel:
-- Does the tree t encode a proof that "ap1 p (natCode c) ≠ xi" for some p, c, xi?
-- Pattern: checkProof2(t) = true AND the proved equation has the form
--   TreeEq(ap1 p clock, xiCode) = Pair(O, O)
-- where xiCode and p are extractable.

-- Extract the "target" from a proof encoding:
-- If thFun(t) = nd(lhsC, rhsC), and rhsC evaluates to Pair(O,O),
-- then lhsC should be TreeEq(something, xiCode).
-- We extract xiCode.

extractTarget : Tree -> Tree
extractTarget t =
  let eq = thFun t
      lhsC = leftT eq
  in boolCase (treeEq (geval fuel (rightT eq)) (nd lf lf))
    -- RHS evaluates to Pair(O,O): possible nonequality proof
    -- LHS should be mkAp2(treeeqC, programOutput, xiCode)
    -- = nd tagAp2 (nd treeeqC (nd programOutput xiCode))
    (boolCase (treeEq (leftT lhsC) tagAp2)
      (boolCase (treeEq (leftT (rightT lhsC)) (codeF2 TreeEq))
        -- Extract xiCode = rightT(rightT(rightT lhsC))
        (rightT (rightT (rightT lhsC)))
        lf)
      lf)
    lf

-- Extract the program code from a nonequality proof
extractProgCode : Tree -> Tree
extractProgCode t =
  let eq = thFun t
      lhsC = leftT eq
  in boolCase (treeEq (leftT lhsC) tagAp2)
    (boolCase (treeEq (leftT (rightT lhsC)) (codeF2 TreeEq))
      -- programOutput is leftT(rightT(rightT lhsC))
      -- It should be mkAp1(fCode, clockCode)
      (let progOut = leftT (rightT (rightT lhsC))
       in boolCase (treeEq (leftT progOut) tagAp1)
            (leftT (rightT progOut))   -- fCode
            lf)
      lf)
    lf

------------------------------------------------------------------------
-- 4. The Chaitin search as a Fun1
--
-- State = Pair(config, Pair(index, result))
--   config = binary encoding of l (the complexity bound)
--   index  = current candidate (natCode of the enumeration index)
--   result = O if not found, xi (as coded tree) if found
--
-- Step function: FIXED Fun1 (does not depend on l)
--   1. If result ≠ O: return state unchanged (halt)
--   2. Generate candidate proof tree from index (tree enumeration)
--   3. Run proof check:
--      a. Apply thFun to candidate
--      b. Check both sides agree under geval
--      c. Check equation has "nonequality" form
--      d. Check extracted program has code-size <= l (compare with config)
--   4. If all checks pass: extract xi, update result
--   5. Advance index: Pair(config, Pair(suc(index), result'))

-- The step function decomposed into components:

-- Component: check if result is found (result ≠ O means halt)
-- isFound: if x = O return O, else return Pair(O,O) (truthy)
isFound : Fun1
isFound = Comp2 IfLf I (Comp2 Pair (KT (ap2 Pair O O)) (KT O))

-- Component: advance natCode index
-- natSuc(nd(lf, rest)) = nd(lf, nd(lf, rest))
-- natSuc(lf) = nd(lf, lf)
-- This is: prepend0
advanceIdx : Fun1
advanceIdx = Comp2 Pair (KT O) I

-- The full Chaitin step (schematic — actual Fun1 definition)
-- This is a FIXED Fun1: its code does not mention l.
--
-- chaitinStep : Fun1
-- chaitinStep state =
--   let config = Fst(state)
--       idx    = Fst(Snd(state))
--       result = Snd(Snd(state))
--   in IfLf(result,
--        -- result = O: not found yet, do search step
--        Pair(O,           -- placeholder: should be Pair(config, Pair(advIdx, newResult))
--             Pair(advanceIdx(idx), checkAndExtract(config, idx))),
--        -- result ≠ O: halt, keep state
--        Pair(state, state))
--
-- The actual implementation requires:
-- (1) Tree enumeration as Fun1 (Rec-based: maps natCode(n) to treeEnum(n))
-- (2) thFun as Fun1 (already exists as thFunTFor in the object level)
-- (3) geval as Fun1 (requires internalizing the ground evaluator)
-- (4) Size comparison as Fun1 (treeSize <= binDecode(config))
--
-- Components (1)-(4) each require Rec internally.
-- The TOTAL code size is the sum of these fixed components.

-- For now, define the machine using metalevel helpers and compute the code-size bound.

------------------------------------------------------------------------
-- 5. The search (metalevel simulation)

-- Metalevel search: enumerate trees, check each one
chaitinSearch : Nat ->   -- l: complexity bound
                Nat ->   -- clock: enumeration steps remaining
                Tree     -- result: lf if not found, xi code if found
chaitinSearch l zero = lf
chaitinSearch l (suc c) =
  let candidate = treeEnum (suc c)
      isValid = checkProof2 candidate
  in boolCase isValid
    (let target = extractTarget candidate
         progC = extractProgCode candidate
     in boolCase (natLeqB (treeSize progC) l)
       target    -- found: program small enough, return xi code
       (chaitinSearch l c))   -- program too large, continue
    (chaitinSearch l c)       -- not a valid proof, continue

------------------------------------------------------------------------
-- 6. Code-size analysis
--
-- The Chaitin machine C_l is:
--   iterate chaitinStep (ap2 Pair (reify (binCode l)) (ap2 Pair O O))
--
-- Code-size decomposition:
--   progSize(C_l) = treeSize(codeF1(Rec init (iterStep chaitinStep)))
--                 = 1 + treeSize(code init) + treeSize(codeF2(iterStep chaitinStep))
--                 = treeSize(code init) + FIXED
--
-- where FIXED = treeSize(codeF2(iterStep chaitinStep)) + overhead
--
-- code(init) = code(ap2 Pair (reify (binCode l)) (ap2 Pair O O))
--            = nd tagAp2 (nd (codeF2 Pair) (nd (code(reify(binCode l))) (code(ap2 Pair O O))))
--
-- code(reify(binCode l)):
--   binCode l has treeSize O(log l)
--   reify maps nd(a,b) to ap2 Pair (reify a) (reify b)
--   code(reify t) has treeSize O(treeSize t) (linear in tree size)
--   So code(reify(binCode l)) has treeSize O(log l)
--
-- Total: progSize(C_l) = FIXED + O(log l)
--
-- For l > FIXED + c * log(l), we get progSize(C_l) < l.
-- Since log(l) grows much slower than l, this holds for all sufficiently large l.

-- The fixed part: treeSize of the step function code
-- (This would be a concrete Nat once chaitinStep is fully defined as Fun1)

-- Reify-code size lemma: treeSize(code(reify t)) is bounded by a linear function of treeSize(t)
reifyCodeSize : Tree -> Nat
reifyCodeSize lf = treeSize (code O)
reifyCodeSize (nd a b) = treeSize (code (ap2 Pair (reify a) (reify b)))

------------------------------------------------------------------------
-- 7. The KR contradiction
--
-- Theorem: If the system is consistent, then for sufficiently large l,
-- the Chaitin machine C_l has code-size < l but outputs xi with K(xi) > l.
-- This is impossible, so the system cannot prove its own consistency.

-- The formal structure (parameters are the assumptions):

-- A program outputs a tree if for some clock, evaluation gives that tree
GOutputsAt : Fun1 -> Nat -> Tree -> Set
GOutputsAt f c x = Eq (geval fuel (mkAp1 (codeF1 f) (code (reify (natCode c))))) x

-- The KR argument operates ENTIRELY at the metalevel (geval-based outputs).
-- No mixing of metalevel/object-level notions.

------------------------------------------------------------------------
-- 8. The cleaner abstract version
--
-- Strip away the implementation details and state the KR theorem cleanly.

-- "A program ground-outputs tree x" (metalevel, via geval)
GOutputs : Fun1 -> Tree -> Set
GOutputs f x = Sigma Nat (\c -> GOutputsAt f c x)

-- Metalevel Kolmogorov complexity
-- K(x) > n means: no Fun1 of progSize <= n ground-outputs x
MNoSmallProg : Nat -> Tree -> Set
MNoSmallProg n x =
  (p : Fun1) -> Leq (progSize p) n -> GOutputs p x -> Empty

-- Helper
leqRefl : (n : Nat) -> Leq n n
leqRefl zero = leqZ zero
leqRefl (suc n) = leqS (leqRefl n)

-- The KR theorem (metalevel, clean):
-- Given a Chaitin machine family with bounded code-size that,
-- when run, produces an incompressible output, derive contradiction.
--
-- Search result type: xi, a clock c, proof cm(l) outputs xi at c,
-- and proof that xi is incompressible.
SearchResult : (cm : Nat -> Fun1) -> Nat -> Set
SearchResult cm l =
  Sigma Tree (\xi ->
    Sigma Nat (\c ->
      Sigma (GOutputsAt (cm l) c xi)
            (\_ -> MNoSmallProg l xi)))

krClean :
  (cm : Nat -> Fun1) ->
  -- Code-size bound: exists threshold T, for l >= T, |C_l| <= l
  (threshold : Nat) ->
  ((l : Nat) -> Leq threshold l -> Leq (progSize (cm l)) l) ->
  -- Search produces incompressible xi for l >= T:
  ((l : Nat) -> Leq threshold l -> SearchResult cm l) ->
  -- Contradiction
  Empty
krClean cm thr sizeLE search =
  let result = search thr (leqRefl thr)
      xi = fst result
      c  = fst (snd result)
      outputPf = fst (snd (snd result))
      incomp   = snd (snd (snd result))
      -- cm(thr) outputs xi at clock c, and has progSize <= thr.
      -- But incomp says no program of size <= thr outputs xi. Contradiction.
  in incomp (cm thr) (sizeLE thr (leqRefl thr)) (mkSigma c outputPf)

------------------------------------------------------------------------
-- 9. What remains to close the gap
--
-- (a) Define chaitinStep as a concrete Fun1:
--     Requires tree enumeration, thFun, geval, size comparison as Fun1s.
--     Each uses Rec internally. Total code-size is FIXED.
--
-- (b) Compute FIXED = progSize(chaitinStep) explicitly.
--     This gives the threshold T: the smallest l with FIXED + ceil(log2(l)) <= l.
--
-- (c) Prove the search termination:
--     If consistent (no Deriv of O = Pair(O,O)), then for each l >= T,
--     the pigeonhole gives xi, and all per-program proofs exist
--     (by the R/Q lemma technique from MicroNelson).
--     These proofs have bounded size (BLevel 0, O(1) each).
--     So the search finds one within bounded clock.
--
-- (d) Bridge geval to Deriv:
--     For ground terms, geval agrees with the equational system.
--     This is the geval soundness theorem (partially verified in GroundEval tests).
--
-- The structural insight: (a)-(b) are engineering (tedious but mechanical).
-- (c) connects to the existing R/Q infrastructure.
-- (d) is the remaining mathematical content: geval soundness.
--
-- Key difference from diagonal (GodelII.agda):
-- - No substTFor, no codedSubst, no variable-capture issues
-- - No templateCode, no cGS, no diagFTarget
-- - The self-reference is via CODE-SIZE (pigeonhole) not DIAGONALIZATION
-- - The obstruction is computation-bounded: "does the search terminate?"
--   not "can we evaluate terms with free variables?"
