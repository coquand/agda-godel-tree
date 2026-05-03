# treeRec migration status (Phase 1+2 done; Phase 3 pending)

## What was done in this session

### Phase 1: axTreeRecLf / axTreeRecNd as Deriv constructors

`BRA/Deriv.agda` gained two new primitive axioms:

```
axTreeRecLf : (f : Fun1) (s : Fun2) (p : Term) ->
              Deriv (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p)))
axTreeRecNd : (f : Fun1) (s : Fun2) (p a b : Term) ->
              Deriv (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a b))
                                  (ap2 s (ap2 Pair p (ap2 Pair a b))
                                         (ap2 Pair (ap2 (treeRec f s) p a)
                                                   (ap2 (treeRec f s) p b)))))
```

These match Guard's Rfgh from guard15.pdf p.10 axioms 9-10.

### Phase 2: cascade plumbing in ThmT

* `BRA/Thm/Tag.agda` — added `tagAxTreeRecLf` (= 46) and `tagAxTreeRecNd` (= 47).
* `BRA/Thm/TagCodes.agda` — added `tagCode_axTreeRecLf`, `tagCode_axTreeRecNd`,
  `tagCode_treeRecFunc`.
* `BRA/Thm/Parts/AxTreeRecLf.agda` — new (~150 LoC).  enc/out/body/body_eval
  for the leaf axiom.
* `BRA/Thm/Parts/AxTreeRecNd.agda` — new (~420 LoC).  enc/out/body/body_eval
  for the step axiom.
* `BRA/Thm/ThmT.agda`:
  - opens the two new Parts modules
  - `checkTag_axTreeRecLf`, `checkTag_axTreeRecNd` cascade entries
  - `branch_axTreeRecLf`, `branch_axTreeRecNd`, `next_axTreeRecLf`,
    `next_axTreeRecNd`, `next_ruleInst2` linking the cascade
  - `branch_ruleInst2` updated to chain to `next_ruleInst2` (was `fbBody`)
  - `thmTDispRuleInst2`'s `hh` updated to use `next_ruleInst2` (was `fbBody`)
  - `thmTDispAxTreeRecLf` (44-step skip chain) and `thmTDispAxTreeRecNd`
    (45-step skip chain) added
  - `encodeRich` clauses for `axTreeRecLf` and `axTreeRecNd`

### Build status (end of session)

* `BRA/Deriv.agda` — green
* `BRA/Thm/ThmT.agda` — green, **11,900 lines** (up ~270 from 11,634 before
  Phase 1+2; the cascade-plumbing additions outweighed nothing; could be
  reclaimed in Phase 3 by deleting the Rec/RecP cascade slots)
* `BRA/Thm12.agda` — green
* `BRA/GoedelII.agda` — green

ThmT cold typecheck: ~7s (unchanged).  Warm: 0.5s.

## Phase 3 (NOT done): remove Rec/RecP as Fun1/Fun2 constructors

### Goal

Demote `Rec : Term -> Fun2 -> Fun1` (currently a Fun1 constructor) and
`RecP : Fun2 -> Fun2` (currently a Fun2 constructor) to **Agda
definitions** in terms of `treeRec`:

```
RecP s = treeRec Z s                         -- exact match (since ap1 Z p = O)
Rec z s = ?                                  -- needs care for open z (see below)
```

### What this entails

Removing a constructor from `Fun1`/`Fun2` and adding a function of the same
name causes a flag-day refactor.  20+ files pattern-match on `Rec` or
`RecP` and need their clauses removed (since the function is no longer
pattern-matchable):

* `BRA/Term.agda` — the `RecP` / `Rec` clauses in `codeF1`, `codeF2`,
  `substF1`, `substF2`, `KT`
* `BRA/Deriv.agda` — `axRecLf`/`axRecNd`/`axRecPLf`/`axRecPNd` types
  (their `RecP s` / `Rec z s` becomes a function call, but if the
  constructors stay, Agda's elaboration sees `treeRec Z s` in the type
  and may re-trigger `SplitError.UnificationStuck` in `encodeRich`)
* `BRA/CorF.agda`, `BRA/CodeCommutes.agda`, `BRA/Sb2.agda`, `BRA/SbParam.agda`,
  `BRA/StepT12.agda`, `BRA/StepT12Universal.agda`, `BRA/SubT.agda` —
  each has a `(Rec _ _)` / `(RecP _)` clause to delete or rewrite
* `BRA/Th12RecPCloseS*.agda`, `BRA/Th12RecP.agda`, `BRA/Th12RecPUniv.agda`,
  `BRA/Th12I.agda`, `BRA/Thm12.agda` — Theorem 12 RecP cases; either
  delete (if treeRec replaces them) or rewrite to use treeRec
* `BRA/Thm/ThmT.agda`, `BRA/Thm/Parts/AxRecPNd.agda`,
  `BRA/Thm/TagCodes.agda` — RecP-related cascade material

### Subtlety: Rec for open z

`Rec z s` for arbitrary `z : Term` (including `var n`) cannot be
expressed as a treeRec form using the current `KT`, because `KT (var n)
= Z` returns `O` regardless of input — it doesn't preserve open `z`.
Defining `Rec z s = Comp2 (treeRec (KT z) s') Z I` would make the
derived axRecLf for `z = var n` assert `O = var n`, which is unsound.

Mitigations:
1. The architecture doc notes Rec is used in BRA only as `Rec O stepCor`
   and `Rec O stepProto` — i.e. only with `z = O`.  A specialised
   `Rec_O : Fun2 -> Fun1` with `Rec_O s = Comp2 (treeRec Z s) Z I`
   covers all current uses.
2. Alternatively, redefine `KT` to actually preserve open `z` (would
   require `KT (var n) = ?` returning a Fun1 that, applied to any
   input, gives `var n`; not expressible without a dedicated
   "constant-var" Fun1 primitive).
3. Or accept the limitation: keep `Rec` as a Fun1 constructor for now,
   only convert `RecP` (which works cleanly).

### Recommended next-session order

1. **Convert RecP only** (cleanest — `RecP s = treeRec Z s`
   definitionally).  Estimated 10-15 file updates.
2. After RecP done and verified, decide on Rec strategy from the three
   options above.

## Naming note

The user referred to the new primitive as `RecTree`; the codebase has
`treeRec` (Fun2 constructor existing since before this session).  The
mathematics is identical; if the user prefers `RecTree`, a global
rename is a separate small task.
