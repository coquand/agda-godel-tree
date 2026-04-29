# Thm 11 — gap between `Thm11Abstract.agda` and the real theorem

Status: **open, queued for next session**.

Companion to `BRA/Thm11Abstract.agda` (0.13s typecheck).  This note
records what that file proves, what it does *not* prove, and the
concrete programme for closing the gap.  Read this first before
touching `BRA/Thm11Abstract.agda` or opening a new `Thm11` file.

## Framing principle (non-negotiable)

**A specification is a set of symbolic lemmas.  The proof uses only
the lemmas.  Nothing in the proof should ever touch the concrete
shape of `reify j`, `codeFormula F_pre`, or any other large closed
term.**

Operational test: typechecking is fast by construction, not by
luck.  Every step of Thm 11's proof names a lemma.  No step relies
on Agda normalising a spine of hundreds of `ap2 Pair / O` nodes.
If a proof step depends on the *size* of `reify j` or `j`, the
formulation is wrong — not Agda.

This overrides an earlier wrong attitude in this document (now
corrected) that treated "`reify j` is a long closed term but Agda
handles it in milliseconds" as a non-problem.  That framing leaks
the internal structure of `reify j` into the proof.  Replace it
with a lemma.

## What `Thm11Abstract.agda` actually contains

A nested module `Godel` parameterised by:

- `th : Fun1`
- `G : Formula`  -- the Gödel sentence (abstract)
- `encode : (P : Formula) -> Deriv P -> Sigma Tree (\ y -> Deriv (ap1 th (reify y) = reify (codeFormula P)))`  -- forward direction, internalised
- `diagonal : (y : Tree) -> Deriv G -> Deriv (not (ap1 th (reify y) = reify (codeFormula G)))`  -- the fixed-point property, already ruleInst-ed

Under these parameters, `thm11 : Deriv G -> Deriv (atomic (eqn trueT falseT))` is proved in six lines: `encode G pf` produces `(y_d, E1)`; `diagonal y_d pf` produces `NEG`; `axExFalso + mp + mp` collapse `E1 + NEG` into `Deriv bot`.

The reverse direction of the encoding spec is not consumed anywhere.

## What it does NOT contain — the actual content of Gödel I

The two parameters `G` and `diagonal` are doing the real work.  A complete proof of Gödel I has to *construct* both from the spec plus BRA's primitives; the current file just assumes them.

Concretely, the missing layer is:

```
F_pre : Formula
F_pre = not (atomic (eqn (ap1 th (var (suc zero)))
                         (ap2 sub (var zero) (var zero))))

j : Tree
j = codeFormula F_pre

G : Formula
G = substF zero (reify j) F_pre

-- Diagonal, constructed rather than assumed.
diagonal : (y : Tree) -> Deriv G ->
           Deriv (not (atomic (eqn (ap1 th (reify y))
                                   (reify (codeFormula G)))))
```

With `diagonal` in place, `thm11` itself is unchanged — the six-line
skeleton in `Thm11Abstract.agda` is correct.  The work is producing
`G` and `diagonal` honestly, *through named spec lemmas only*.

## Spec surface: four named lemmas the proof composes

Each is proved once by a short induction in its own file.  None of
them has any connection to the size of `F_pre`, `j`, or `reify j`.

1. **`reifyClosed`** — `subst` is identity on `reify T`.
   ```
   reifyClosed : (T : Tree) (x : Nat) (r : Term) ->
                 Eq (subst x r (reify T)) (reify T)
   ```
   One induction on `T`.  The Thm 11 proof uses this wherever a
   closed `reify j`, `reify (code (var 0))`, etc. appears under a
   substitution — it never walks the `ap2 Pair` spine.

2. **`thClosed`** — `th` is closed under substitution.
   ```
   thClosed  : (x : Nat) (r : Term) -> Eq (substF1 x r th)   th
   -- and, for the sub that appears in F_pre:
   subClosed : (x : Nat) (r : Term) -> Eq (substF2 x r sub)  sub
   ```
   `thClosed` is declared **as part of the specification of `th`**,
   not as an auxiliary obstacle.  "Primitive recursive functors are
   closed under substitution" is a standard property; it sits next
   to `encode` as part of what "`th` is a BRA functor" means.
   `subClosed` is provable from `sub`'s concrete definition, but
   same shape.

3. **`codeCommutes`** — coding commutes with substitution.
   ```
   codeCommutes : (x : Nat) (t : Term) (F : Formula) ->
                  Eq (codeFormula (substF x t F))
                     (codedSubst (code t) (code (var x)) (codeFormula F))
   ```
   Structural induction on `F`, piggy-backed on the `Term` version
   (induction on `u`).  Depends on a no-`code (var x)`-subtree
   invariant for tags / `natCode n` / `codeF1 f` / `codeF2 g`; each
   is a small sub-induction.  The `codeF1 th` case either (i) uses
   an additional spec parameter asserting this invariant, or (ii)
   is resolved by instantiating `th` to a concrete `Fun1`.  Decide
   at the top of the session.

4. **`subDef`** — defining equation of the Ex 24 [8] substitution
   functor.  Already proved in `BRA/Sub.agda`.  Consumed at
   arguments `(j, j)` in the diagonal.

## Thm 11's proof as a composition of the four lemmas

Sketch (every named step is O(1) in the size of `F_pre`, so
typechecking is fast by construction):

```
-- pf : Deriv G.
-- Step 1: ruleInst on pf.
NEG_raw : Deriv (substF 1 (reify y_d) G)
NEG_raw = ruleInst 1 (reify y_d) pf

-- Step 2: normalise the substituted formula SYMBOLICALLY via
-- thClosed + subClosed + reifyClosed + the simple subst rules on
-- var / Pair.  NOT by Agda unfolding reify j.
step_A : Eq (substF 1 (reify y_d) G)
            (not (atomic (eqn (ap1 th (reify y_d)) (ap2 sub (reify j) (reify j)))))
step_A = <<a few eqCong / eqTrans steps, each invoking one named lemma>>

NEG_sub : Deriv (not (atomic (eqn (ap1 th (reify y_d)) (ap2 sub (reify j) (reify j)))))
NEG_sub = eqSubst Deriv step_A NEG_raw

-- Step 3: reduce ap2 sub (reify j) (reify j) to reify (codeFormula G).
sub_red : Deriv (atomic (eqn (ap2 sub (reify j) (reify j))
                             (reify (codedSubst (code (reify j)) (code (var 0)) j))))
sub_red = subDef j j

cc : Eq (codedSubst (code (reify j)) (code (var 0)) j)
         (codeFormula G)
cc = eqSym (codeCommutes zero (reify j) F_pre)

sub_to_G : Deriv (atomic (eqn (ap2 sub (reify j) (reify j)) (reify (codeFormula G))))
sub_to_G = eqSubst ... cc sub_red

-- Step 4: transport NEG_sub along sub_to_G to land on codeFormula G.
NEG : Deriv (not (atomic (eqn (ap1 th (reify y_d)) (reify (codeFormula G)))))
NEG = <<ruleSym / congR / eqSubst using sub_to_G>>
```

No step in this pipeline knows how big `reify j` is.  Each step
names a lemma and moves on.  That is the specification-level
framing the proof must obey.

## Concrete plan for the next session

Order matters — (A) and (B) can go in parallel; both unblock (C),
which unblocks (D):

A. **`BRA/ReifyClosed.agda`** — `reifyClosed`.  ~20 lines, one
   induction on `Tree`.

B. **`BRA/CodeCommutes.agda`** — `codeCommutes` plus the supporting
   no-`code (var x)`-subtree invariant for tags, `natCode`,
   `codeF1`, `codeF2`.  ~100-150 lines, purely structural.

C. **`BRA/Thm11Diagonal.agda`** — under module parameters `th`,
   `encode`, `thClosed` (and any additional invariants decided
   above), define `F_pre`, `j`, `G`, and prove `diagonal` using A,
   B, and `subDef` from `BRA/Sub.agda`.  No concrete tree
   unfolding.

D. **`BRA/Thm11.agda`** — import `Godel` from `Thm11Abstract`,
   supply `G` and `diagonal` from `Thm11Diagonal`, re-export
   `thm11 : Deriv G -> Deriv bot`.

Estimate: 300-500 lines total across four files.  Every file < 10s
typecheck (the hard constraint).  Zero postulates.

## Hard checks before writing code

Settle these at the top of the session; the Agda below is mostly
bookkeeping once they are settled.

- [ ] **Reading of Thm 11**: just `Deriv G -> Deriv bot`, not also
  `Not (Deriv (not G))`.  (Settled earlier: yes, just the first
  half.  Reverse direction not used.)

- [ ] **Handling `th`'s closedness + the `codeF1 th` sub-invariant.**
  Two options:
  (a) Keep `th` abstract; declare `thClosed` and a `codeF1Th_noVar`
      invariant as part of the spec.  Four named lemmas become five
      or six, but the abstraction is preserved.
  (b) Instantiate `th` to a concrete `Fun1` in `Thm11Diagonal.agda`
      (a composition realising Ex 24 `th`'s dispatch).  `thClosed`
      and the `codeF1 th` invariant both become structural, derived
      from the concrete definition.  Loses abstraction; gains one
      fewer spec parameter.
  Choose before writing `Thm11Diagonal.agda`.

- [ ] **What the spec of `th` *is*.**  The current `encode`
  parameter is one clause.  The full spec likely bundles:
  `th : Fun1`, `encode`, `thClosed`, and (if option (a) above) a
  `codeF1 th` no-var-subtree assertion.  Write this down as a
  record or parameter block at the top of `Thm11Diagonal.agda` —
  one place, reused by everything downstream.

## What is NOT a problem (corrected)

- The size of `reify j` is irrelevant: use `reifyClosed` rather
  than Agda normalisation.  The proof never walks the `ap2 Pair`
  spine of `reify j`.
- The size of `codeFormula G` / `j` is irrelevant: use
  `codeCommutes` as a named equation; never normalise the tree.
- The size of `F_pre` is irrelevant: every lemma is quantified over
  arbitrary formulas, and Thm 11 invokes each lemma at `F_pre`
  opaquely.

Fast typechecking is therefore not a performance hope — it is a
consequence of the proof being right-sized against the spec.
