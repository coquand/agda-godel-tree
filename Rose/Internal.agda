{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Internal where

open import Rose.Base
  using (Nat; zero; suc; add; add-zero; add-suc; Fin; fz; fs;
         Eq; refl; eqCong; eqSym; eqTrans; eqSubst;
         Maybe; nothing; just; maybeMap)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term; var; leaf; pair; cas; niter)
open import Rose.Eval using (Env; evalEnv; evalCas; evalNiter; extEnv2)
open import Rose.Code using (natCode; tagVar)
open import Rose.CodedSubst using (thickNatCode; thickVarResult; codedSubstVar)

------------------------------------------------------------------------
-- Peel step: strip one nd-layer from the niter state.
--
-- In niter binding convention:
--   var 0 = remaining tail of iteration tree
--   var 1 = current state
--
-- peelStep examines var 1 (the state) via cas:
--   state = lf       -->  lf    (already exhausted, stay lf)
--   state = nd a b   -->  b     (right subtree = one layer peeled)
--
-- The cas nd-branch binds var 0 = right, var 1 = left of the state.
-- We return var 0 (right subtree = the peeled tail).

peelStep : {n : Nat} -> Term (suc (suc n))
peelStep = cas (var (fs fz)) leaf (var fz)

------------------------------------------------------------------------
-- peelNat: specification of what niter with peelStep computes.
--
-- peelNat k m computes the monus (truncated subtraction) of natCodes:
--   peelNat k m = natCode (m - k)   when m >= k
--               = lf                when m < k
--
-- Since natCode 0 = lf, this means peelNat k m = lf iff k >= m.
-- And peelNat k m = nd _ _ iff m > k.

peelNat : Nat -> Nat -> Tree
peelNat zero    m       = natCode m
peelNat (suc k) zero    = lf
peelNat (suc k) (suc m) = peelNat k m

------------------------------------------------------------------------
-- peel-lf: peeling lf through any number of niter steps stays lf.
--
-- When the state starts as lf, peelStep always returns lf (cas lf
-- takes the lf branch), so the state remains lf at every step.
--
-- Proof by induction on k: at each step, natCode (suc k) = nd lf ...,
-- so evalNiter takes one step, step computes cas lf leaf ... = lf,
-- and we recurse with k and state still lf.

peel-lf : {n : Nat} (env : Env n) (k : Nat) ->
  Eq (evalNiter env (natCode k) lf peelStep) lf
peel-lf env zero    = refl
peel-lf env (suc k) = peel-lf env k

------------------------------------------------------------------------
-- peel-lemma: niter with peelStep computes peelNat.
--
-- Key lemma: iterating peelStep along natCode k, starting from
-- state natCode m, yields peelNat k m.
--
-- Proof by induction on k, case-splitting m:
--   k = 0:     niter lf state _ = state = natCode m = peelNat 0 m.
--   k+1, m=0:  after one step, state lf -> lf, then peel-lf.
--   k+1, m+1:  after one step, state (nd lf (natCode m)) -> natCode m,
--              then recurse with k, m.  peelNat (k+1) (m+1) = peelNat k m.

peel-lemma : {n : Nat} (env : Env n) (k m : Nat) ->
  Eq (evalNiter env (natCode k) (natCode m) peelStep) (peelNat k m)
peel-lemma env zero    m       = refl
peel-lemma env (suc k) zero    = peel-lf env k
peel-lemma env (suc k) (suc m) = peel-lemma env k m

------------------------------------------------------------------------
-- Internal coded variable substitution.
--
-- internalCodSubstVar : Term 3
--   var 0 = index   (natCode k, the target variable to substitute)
--   var 1 = varcode (natCode m, the variable code being examined)
--   var 2 = repl    (the replacement tree)
--
-- Algorithm (two-pass forward-peel):
--
-- Pass 1: niter index varcode peelStep --> peelNat k m
--   Result nd (m > k): variable is ABOVE target. Shift down.
--     Return nd tagVar (tail varcode) = nd (nd lf lf) (natCode (m-1)).
--     The tail is extracted by cas on the original varcode (a free var).
--   Result lf (m <= k): can't distinguish hit from below yet.
--
-- Pass 2 (only when m <= k): niter varcode index peelStep --> peelNat m k
--   Result lf (k <= m, combined with m <= k: k = m): HIT.
--     Return repl (the replacement tree).
--   Result nd (k > m): variable is BELOW target. Unchanged.
--     Return nd tagVar varcode = nd (nd lf lf) (natCode m).
--
-- De Bruijn index notes for the term:
--   Outer scope (Term 3): var 0=index, var 1=varcode, var 2=repl
--   Outer cas nd-branch (Term 5): var 0,1 = subtrees of peel result,
--     var 2=index, var 3=varcode, var 4=repl
--   Inner cas nd-branch adds 2 more binders similarly.

internalCodSubstVar : Term (suc (suc (suc zero)))
internalCodSubstVar =
  cas (niter (var fz) (var (fs fz)) peelStep)
      -- lf branch (m <= k): do reverse peel to distinguish hit/below.
      (cas (niter (var (fs fz)) (var fz) peelStep)
           -- lf (k = m): variable hit. Return replacement.
           (var (fs (fs fz)))
           -- nd (k > m): below target. Return nd tagVar varcode.
           (pair (pair leaf leaf) (var (fs (fs (fs fz))))))
      -- nd branch (m > k): above target.
      -- Return nd tagVar (tail varcode) = nd tagVar (natCode (m-1)).
      -- tail varcode is obtained by cas on varcode (var 3 in scope 5).
      (pair (pair leaf leaf)
            (cas (var (fs (fs (fs fz)))) leaf (var fz)))

------------------------------------------------------------------------
-- Helper: environment with 3 bindings for testing.

mkEnv3 : Tree -> Tree -> Tree -> Env (suc (suc (suc zero)))
mkEnv3 a b c fz               = a
mkEnv3 a b c (fs fz)          = b
mkEnv3 a b c (fs (fs fz))     = c

------------------------------------------------------------------------
-- Unit tests: eval of internalCodSubstVar agrees with codedSubstVar.
--
-- Each test verifies:
--   evalEnv (mkEnv3 (natCode k) (natCode m) repl) internalCodSubstVar
--   = codedSubstVar repl k (natCode m)
--
-- All proofs are refl: both sides reduce to the same tree.
-- We use repl = nd lf lf throughout (an arbitrary non-trivial tree).

-- k=0, m=0: hit -> repl
test-00 : Eq (evalEnv (mkEnv3 lf lf (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) zero lf)
test-00 = refl

-- k=0, m=1: above -> nd tagVar (natCode 0)
test-01 : Eq (evalEnv (mkEnv3 lf (nd lf lf) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) zero (nd lf lf))
test-01 = refl

-- k=0, m=2: above -> nd tagVar (natCode 1)
test-02 : Eq (evalEnv (mkEnv3 lf (nd lf (nd lf lf)) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) zero (nd lf (nd lf lf)))
test-02 = refl

-- k=1, m=0: below -> nd tagVar (natCode 0)
test-10 : Eq (evalEnv (mkEnv3 (nd lf lf) lf (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc zero) lf)
test-10 = refl

-- k=1, m=1: hit -> repl
test-11 : Eq (evalEnv (mkEnv3 (nd lf lf) (nd lf lf) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc zero) (nd lf lf))
test-11 = refl

-- k=1, m=2: above -> nd tagVar (natCode 1)
test-12 : Eq (evalEnv (mkEnv3 (nd lf lf) (nd lf (nd lf lf)) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc zero) (nd lf (nd lf lf)))
test-12 = refl

-- k=2, m=0: below -> nd tagVar (natCode 0)
test-20 : Eq (evalEnv (mkEnv3 (nd lf (nd lf lf)) lf (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc (suc zero)) lf)
test-20 = refl

-- k=2, m=1: below -> nd tagVar (natCode 1)
test-21 : Eq (evalEnv (mkEnv3 (nd lf (nd lf lf)) (nd lf lf) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc (suc zero)) (nd lf lf))
test-21 = refl

-- k=2, m=2: hit -> repl
test-22 : Eq (evalEnv (mkEnv3 (nd lf (nd lf lf)) (nd lf (nd lf lf)) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc (suc zero)) (nd lf (nd lf lf)))
test-22 = refl

-- k=2, m=3: above -> nd tagVar (natCode 2)
test-23 : Eq (evalEnv (mkEnv3 (nd lf (nd lf lf)) (nd lf (nd lf (nd lf lf))) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc (suc zero)) (nd lf (nd lf (nd lf lf))))
test-23 = refl

-- k=3, m=1: below -> nd tagVar (natCode 1)
test-31 : Eq (evalEnv (mkEnv3 (nd lf (nd lf (nd lf lf))) (nd lf lf) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc (suc (suc zero))) (nd lf lf))
test-31 = refl

-- k=3, m=3: hit -> repl
test-33 : Eq (evalEnv (mkEnv3 (nd lf (nd lf (nd lf lf))) (nd lf (nd lf (nd lf lf))) (nd lf lf)) internalCodSubstVar)
             (codedSubstVar (nd lf lf) (suc (suc (suc zero))) (nd lf (nd lf (nd lf lf))))
test-33 = refl

------------------------------------------------------------------------
-- thickNatCode-diag: thickNatCode k (natCode k) = nothing.
--
-- The "hit" case: when the variable index equals the target,
-- thick returns nothing, signalling substitution.
--
-- Proof by induction on k:
--   k = 0: thickNatCode 0 lf = nothing.
--   k+1:   thickNatCode (k+1) (nd lf (natCode k))
--          = maybeMap (nd lf) (thickNatCode k (natCode k))
--          = maybeMap (nd lf) nothing   [by IH]
--          = nothing.

thickNatCode-diag : (k : Nat) -> Eq (thickNatCode k (natCode k)) nothing
thickNatCode-diag zero    = refl
thickNatCode-diag (suc k) = eqCong (maybeMap (nd lf)) (thickNatCode-diag k)

------------------------------------------------------------------------
-- thickNatCode-above: variable above target, shift down.
--
-- When m > k (parametrized as m = suc (add d k)):
--   thickNatCode k (natCode (suc (add d k))) = just (natCode (add d k))
--
-- Proof by induction on k:
--   k = 0: thickNatCode 0 (nd lf (natCode d)) = just (natCode d).
--   k+1:   thickNatCode (k+1) (nd lf (natCode (suc (add d k))))
--          = maybeMap (nd lf) (thickNatCode k (natCode (suc (add d k))))
--          = maybeMap (nd lf) (just (natCode (add d k)))  [by IH]
--          = just (nd lf (natCode (add d k)))
--          = just (natCode (suc (add d k))).

thickNatCode-above : (d k : Nat) ->
  Eq (thickNatCode k (natCode (suc (add d k)))) (just (natCode (add d k)))
thickNatCode-above d zero    = refl
thickNatCode-above d (suc k) =
  -- Goal: thickNatCode (suc k) (natCode (suc (add d (suc k)))) = just (natCode (add d (suc k)))
  -- add d (suc k) = suc (add d k) by add-suc, so rewrite to use IH.
  eqSubst
    (\ x -> Eq (thickNatCode (suc k) (natCode (suc x))) (just (natCode x)))
    (eqSym (add-suc d k))
    (eqCong (maybeMap (nd lf)) (thickNatCode-above d k))

------------------------------------------------------------------------
-- thickNatCode-below: variable below target, unchanged.
--
-- When k > m (parametrized as k = suc (add d m)):
--   thickNatCode (suc (add d m)) (natCode m) = just (natCode m)
--
-- Proof by induction on m:
--   m = 0: thickNatCode (suc (add d 0)) lf = just lf = just (natCode 0).
--   m+1:   thickNatCode (suc (add d (m+1))) (nd lf (natCode m))
--          = thickNatCode (suc (suc (add d m))) (nd lf (natCode m))
--          = maybeMap (nd lf) (thickNatCode (suc (add d m)) (natCode m))
--          = maybeMap (nd lf) (just (natCode m))  [by IH]
--          = just (nd lf (natCode m))
--          = just (natCode (suc m)).

thickNatCode-below : (d m : Nat) ->
  Eq (thickNatCode (suc (add d m)) (natCode m)) (just (natCode m))
thickNatCode-below d zero    = refl
thickNatCode-below d (suc m) =
  -- Goal: thickNatCode (suc (add d (suc m))) (natCode (suc m)) = just (natCode (suc m))
  -- Rewrite add d (suc m) to suc (add d m) to expose the suc-suc case.
  eqSubst
    (\ x -> Eq (thickNatCode (suc x) (natCode (suc m))) (just (natCode (suc m))))
    (eqSym (add-suc d m))
    (eqCong (maybeMap (nd lf)) (thickNatCode-below d m))

------------------------------------------------------------------------
-- Correctness of internalCodSubstVar.
--
-- Strategy: define a "dispatch" function that takes both peel results
-- as concrete trees (not evalNiter calls), then:
-- (A) show eval = dispatch (peelNat k m) (peelNat m k) via eqSubst
-- (B) show dispatch (peelNat k m) (peelNat m k) = codedSubstVar by induction

-- dispatch: given both peel results and the original varcode/repl,
-- compute the final answer. This mirrors what the eval produces
-- after both niters are resolved.
dispatch : Tree -> Tree -> Tree -> Tree -> Tree
dispatch lf       lf       varcode repl = repl
dispatch lf       (nd a b) varcode repl = nd tagVar varcode
dispatch (nd a b) sp       varcode repl = ndTail varcode
  where
  ndTail : Tree -> Tree
  ndTail lf       = nd tagVar lf
  ndTail (nd c d) = nd tagVar d

-- Trichotomy on Nat: for any k, m, either k = m, or m = suc (add d k),
-- or k = suc (add d m) for some d.
data Trichotomy (k m : Nat) : Set where
  tri-eq    : Eq k m -> Trichotomy k m
  tri-above : (d : Nat) -> Eq m (suc (add d k)) -> Trichotomy k m
  tri-below : (d : Nat) -> Eq k (suc (add d m)) -> Trichotomy k m

trichotomy : (k m : Nat) -> Trichotomy k m
trichotomy zero    zero    = tri-eq refl
trichotomy zero    (suc m) = tri-above m (eqCong suc (eqSym (add-zero m)))
trichotomy (suc k) zero    = tri-below k (eqCong suc (eqSym (add-zero k)))
trichotomy (suc k) (suc m) = go (trichotomy k m)
  where
  go : Trichotomy k m -> Trichotomy (suc k) (suc m)
  go (tri-eq eq)      = tri-eq (eqCong suc eq)
  go (tri-above d eq) = tri-above d (eqTrans (eqCong suc eq) (eqCong suc (eqSym (add-suc d k))))
  go (tri-below d eq) = tri-below d (eqTrans (eqCong suc eq) (eqCong suc (eqSym (add-suc d m))))

-- Part B: dispatch of peelNat results = codedSubstVar.
-- Uses trichotomy to case-split, then thickNatCode lemmas.

-- Helper: peelNat for equal args gives lf
peelNat-diag : (k : Nat) -> Eq (peelNat k k) lf
peelNat-diag zero    = refl
peelNat-diag (suc k) = peelNat-diag k

-- Helper: peelNat when m > k (m = suc (add d k)) gives nd
peelNat-above : (d k : Nat) -> Eq (peelNat k (suc (add d k))) (natCode (suc d))
peelNat-above d zero    = eqCong (\ x -> natCode (suc x)) (add-zero d)
peelNat-above d (suc k) =
  eqSubst (\ x -> Eq (peelNat k x) (natCode (suc d))) (eqSym (add-suc d k))
          (peelNat-above d k)

-- Helper: peelNat when k > m (k = suc (add d m)) gives lf
peelNat-below : (d m : Nat) -> Eq (peelNat (suc (add d m)) m) lf
peelNat-below d zero    = eqSubst (\ x -> Eq (peelNat (suc x) zero) lf) (eqSym (add-zero d)) refl
peelNat-below d (suc m) =
  eqSubst (\ x -> Eq (peelNat x m) lf) (eqSym (add-suc d m))
          (peelNat-below d m)

-- Part A: eval of internalCodSubstVar = dispatch of niter results.
-- The outer dispatch wraps evalCas around the first niter.
-- We use eqSubst to rewrite the stuck evalNiter.
--
-- outerF env t = evalCas env t handleLf handleNd
-- innerF env t = evalCas env t (var 2) innerHandleNd
--
-- Proof chain:
--   evalEnv env iCSV
--   = outerF env (evalNiter1)         -- by eval normalization
--   = outerF env (peelNat k m)        -- by eqCong outerF (peel-lemma)
--   = dispatch (peelNat k m) (peelNat m k) (natCode m) repl
--     -- for the lf case, one more rewrite for the second niter

-- The outer continuation: evalCas with the handleLf and handleNd branches.
outerF : Env (suc (suc (suc zero))) -> Tree -> Tree
outerF env t = evalCas env t
  (cas (niter (var (fs fz)) (var fz) peelStep)
       (var (fs (fs fz)))
       (pair (pair leaf leaf) (var (fs (fs (fs fz))))))
  (pair (pair leaf leaf) (cas (var (fs (fs (fs fz)))) leaf (var fz)))

-- The inner continuation (inside the lf branch): evalCas for the second peel.
innerF : Env (suc (suc (suc zero))) -> Tree -> Tree
innerF env t = evalCas env t
  (var (fs (fs fz)))
  (pair (pair leaf leaf) (var (fs (fs (fs fz)))))

-- Lemma: outerF env lf = innerF env (evalNiter env (natCode m) (natCode k) peelStep)
-- This is definitional: evalCas env lf handleLf handleNd = evalEnv env handleLf,
-- and handleLf contains the second niter.

-- Lemma: innerF env lf = repl
-- innerF env lf = evalCas env lf (var 2) ... = evalEnv env (var 2) = repl. Definitional.

-- Lemma: innerF env (nd a b) = nd tagVar varcode
-- Definitional when varcode is concrete.

-- eval-dispatch: eval of internalCodSubstVar = dispatch of peel results.
eval-dispatch : (k m : Nat) (repl : Tree) ->
  Eq (evalEnv (mkEnv3 (natCode k) (natCode m) repl) internalCodSubstVar)
     (dispatch (peelNat k m) (peelNat m k) (natCode m) repl)
eval-dispatch k m repl =
  let env = mkEnv3 (natCode k) (natCode m) repl in
  -- Step 1: eval = outerF env (evalNiter env (natCode k) (natCode m) peelStep)
  -- This is definitional (Agda normalizes evalEnv on cas).
  -- Step 2: rewrite first niter via peel-lemma
  eqTrans
    (eqCong (outerF env) (peel-lemma env k m))
    -- Now have: outerF env (peelNat k m) = dispatch (peelNat k m) (peelNat m k) (natCode m) repl
    -- Step 3: case-split on peelNat k m to resolve outerF
    (outerF-dispatch k m repl)
  where
  outerF-dispatch : (k m : Nat) (repl : Tree) ->
    Eq (outerF (mkEnv3 (natCode k) (natCode m) repl) (peelNat k m))
       (dispatch (peelNat k m) (peelNat m k) (natCode m) repl)
  outerF-dispatch k m repl = go-outer (trichotomy k m)
    where
    env = mkEnv3 (natCode k) (natCode m) repl

    -- When k = m: peelNat k k = lf. outerF env lf evaluates handleLf,
    -- which does the second niter: evalNiter env (natCode m) (natCode m) peelStep.
    -- By peel-diag, this is lf. Then innerF env lf = repl. And dispatch lf lf = repl.
    -- We use eqSubst to rewrite both peelNat to lf, and the second niter to lf.
    go-outer : Trichotomy k m ->
      Eq (outerF env (peelNat k m))
         (dispatch (peelNat k m) (peelNat m k) (natCode m) repl)
    go-outer (tri-eq refl) =
      -- peelNat m m -> lf, need to rewrite
      eqSubst (\ p -> Eq (outerF env p) (dispatch p p (natCode m) repl))
              (eqSym (peelNat-diag m))
              -- Now: outerF env lf = dispatch lf lf (natCode m) repl = repl
              -- outerF env lf = evalCas env lf handleLf handleNd = evalEnv env handleLf
              -- handleLf does second niter: evalNiter env (natCode m) (natCode m) peelStep
              -- Need to rewrite this to lf too.
              (eqCong (innerF env) (eqTrans (peel-lemma env m m) (peelNat-diag m)))
    go-outer (tri-above d refl) =
      -- m = suc (add d k). peelNat k m = natCode (suc d) = nd lf (natCode d).
      -- outerF env (nd ..) goes to handleNd, giving ndTail varcode.
      eqSubst (\ p -> Eq (outerF env p) (dispatch p (peelNat (suc (add d k)) k) (natCode (suc (add d k))) repl))
              (eqSym (peelNat-above d k))
              -- Now: outerF env (natCode (suc d)) = dispatch (natCode (suc d)) ... (natCode m) repl
              -- natCode (suc d) = nd lf (natCode d), so outerF goes to nd branch.
              refl
    go-outer (tri-below d refl) =
      -- k = suc (add d m). peelNat k m = lf.
      -- outerF env lf = handleLf = second niter.
      -- peelNat m k = natCode (suc d) = nd ...
      eqSubst (\ p -> Eq (outerF env p) (dispatch p (peelNat m (suc (add d m))) (natCode m) repl))
              (eqSym (peelNat-below d m))
              -- Now: outerF env lf = dispatch lf (peelNat m (suc (add d m))) (natCode m) repl
              -- outerF env lf = innerF env (evalNiter env (natCode m) (natCode (suc (add d m))) peelStep)
              -- peelNat m (suc (add d m)) = natCode (suc d) = nd ...
              -- Need: innerF env (evalNiter ...) = dispatch lf (peelNat m (suc (add d m))) (natCode m) repl
              --      = nd tagVar (natCode m) [since peelNat m (suc (add d m)) = nd ...]
              (eqTrans
                (eqCong (innerF env) (eqTrans (peel-lemma env m (suc (add d m))) (peelNat-above d m)))
                -- innerF env (natCode (suc d)) = nd tagVar (natCode m)
                -- natCode (suc d) = nd lf (natCode d), innerF goes to nd branch
                -- extEnv2 env lf (natCode d), var 3 = env (fs fz) = natCode m
                -- result: nd tagVar (natCode m)
                (eqSubst (\ p2 -> Eq (nd tagVar (natCode m)) (dispatch lf p2 (natCode m) repl))
                         (eqSym (peelNat-above d m))
                         refl))

dispatch-correct : (k m : Nat) (repl : Tree) ->
  Eq (dispatch (peelNat k m) (peelNat m k) (natCode m) repl)
     (codedSubstVar repl k (natCode m))
dispatch-correct k m repl = go (trichotomy k m)
  where
  go : Trichotomy k m ->
    Eq (dispatch (peelNat k m) (peelNat m k) (natCode m) repl)
       (codedSubstVar repl k (natCode m))
  go (tri-eq refl) =
    -- k = m. peelNat k k = lf, peelNat k k = lf.
    -- dispatch lf lf (natCode k) repl = repl
    -- codedSubstVar repl k (natCode k) = thickVarResult repl nothing = repl
    eqSubst (\ p1 -> Eq (dispatch p1 p1 (natCode m) repl) (codedSubstVar repl m (natCode m)))
            (eqSym (peelNat-diag m))
            (eqSubst (\ r -> Eq (dispatch lf lf (natCode m) repl) r)
                     (eqSym (eqCong (thickVarResult repl) (thickNatCode-diag m)))
                     refl)
  go (tri-above d refl) =
    -- m = suc (add d k). peelNat k m = nd... (above).
    -- dispatch (nd..) _ (natCode m) repl = ndTail (natCode m)
    -- = nd tagVar (natCode (add d k))
    -- codedSubstVar repl k (natCode m) = nd tagVar (natCode (add d k))
    eqSubst (\ p1 -> Eq (dispatch p1 (peelNat (suc (add d k)) k) (natCode (suc (add d k))) repl)
                        (codedSubstVar repl k (natCode (suc (add d k)))))
            (eqSym (peelNat-above d k))
            (eqSubst (\ r -> Eq (dispatch (natCode (suc d)) (peelNat (suc (add d k)) k) (natCode (suc (add d k))) repl) r)
                     (eqSym (eqCong (thickVarResult repl) (thickNatCode-above d k)))
                     refl)
  go (tri-below d refl) =
    -- k = suc (add d m). peelNat k m = lf, peelNat m k = nd...
    eqSubst (\ p1 -> Eq (dispatch p1 (peelNat m (suc (add d m))) (natCode m) repl)
                        (codedSubstVar repl (suc (add d m)) (natCode m)))
            (eqSym (peelNat-below d m))
            (eqSubst (\ p2 -> Eq (dispatch lf p2 (natCode m) repl)
                                 (codedSubstVar repl (suc (add d m)) (natCode m)))
                     (eqSym (peelNat-above d m))
                     (eqSubst (\ r -> Eq (dispatch lf (natCode (suc d)) (natCode m) repl) r)
                              (eqSym (eqCong (thickVarResult repl) (thickNatCode-below d m)))
                              refl))

------------------------------------------------------------------------
-- Full correctness theorem.

codedSubstVar-correct : (k m : Nat) (repl : Tree) ->
  Eq (evalEnv (mkEnv3 (natCode k) (natCode m) repl) internalCodSubstVar)
     (codedSubstVar repl k (natCode m))
codedSubstVar-correct k m repl =
  eqTrans (eval-dispatch k m repl) (dispatch-correct k m repl)
