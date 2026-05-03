# BRA/Thm/ThmT.agda monolith split — progress + methodology

## Why — three governing principles

The split is required to enforce the three principles this codebase
runs on:

1. **No fancy pattern matching / advanced Agda features.**  No dot
   patterns, no `with` abstractions, no dependent index unification,
   no instance arguments, no REWRITE pragmas.  When pattern-matching
   gets stuck, the formulation drifted from the underlying mathematics
   — fix the formulation, not the Agda surface.
2. **Small files** (~250 LoC budget per file).  When a file outgrows
   that budget, the proof shape is wrong, not the patience required.
3. **Fast typecheck** (<2s cold per file).  Slowness signals
   mathematical mismatch, not "be patient".

`BRA/Thm/ThmT.agda` was 16,758 lines (66x over budget) and took ~30s
warm to typecheck.  Per-axiom proof material (`body_axX`,
`body_axX_eval`, dispatcher entries, `thmTDispAxX`) all lived in a
single abstract block alongside the cascade itself.  Adding a new
axiom (e.g. `axRLf`/`axRNd` for the unified `treeRec` primitive)
required a 600-1000 LoC edit to the monolith with high risk.

The right structure: each axiom in its own self-contained
`BRA/Thm/Parts/AxX.agda` file (~250-700 LoC) holding `encX`, `outX`,
`body_axX`, `body_axX_eval`.  `ThmT.agda` keeps only the cross-cutting
cascade (`checkTag_X`, `branch_X`, `next_X` chain) and the
`thmTDispAxX` dispatch lemmas (which inherently reference all sibling
`body_Y`/`next_Y`).  After Phase 3, ThmT lands at ~800 LoC.

## Done in this session

### Phase 1 — extracted shared helpers

* `BRA/Thm/EvalHelpers.agda` (502 LoC) — `pairOfFan_eval`,
  `pairOfConst_eval`, `liftCompFstSnd_evalPair` &c, `sndOf_dN`,
  `liftFstSndSnd_evalPair3` &c (depths 3-5), plus the
  level-1 / level-2 lifted helpers (`liftAxiom`, `B_combinator`,
  `liftedRuleTrans`, `liftedCongL`/`R`, `*Two` siblings).  Public; the
  deeper position-extractors are inside an `abstract` block.
* `BRA/Thm/TagCodes.agda` (143 LoC) — all `tagCode_axX` and
  `tagCode_*Func` constants moved out of the `abstract` block in
  `ThmT.agda`.

### Phase 2 — pilot axiom splits

| File | Body LoC | Eval LoC | Total |
|---|---|---|---|
| `BRA/Thm/Parts/AxRecLf.agda` | 17 | ~50 | 96 |
| `BRA/Thm/Parts/AxRecNd.agda` | ~70 | ~330 | 443 |
| `BRA/Thm/Parts/AxRecPLf.agda` | 14 | ~50 | 114 |
| `BRA/Thm/Parts/AxRecPNd.agda` | ~75 | ~390 | 511 |

`ThmT.agda` reduced from **16,758** to **15,198** lines (-1,560).
Whole chain (`Term` -> `Deriv` -> `EvalHelpers` -> `TagCodes` ->
`Parts/Ax*` -> `ThmT` -> `Thm12` -> `GoedelII`) typechecks cleanly.

## Established methodology — for each remaining axiom X

1. **Read the existing `BRA/Thm/Parts/AxX.agda`** (already exists for
   all 44 axioms, currently holds only `encAxX` and `outAxX`).
2. **Read `body_axX` from `BRA/Thm/ThmT.agda`** (locate via
   `grep -n "^  body_axX\b" BRA/Thm/ThmT.agda`).  Body is a `Fun2`
   expression of a few dozen lines.
3. **Read `body_axX_eval`** (separate from body_axX in the file;
   often hundreds of lines for depth-4/5 payloads).
4. **Write the new `BRA/Thm/Parts/AxX.agda`** with:
   * Imports: `BRA.Base`, `BRA.Term`, `BRA.Formula`, `BRA.Deriv`,
     `BRA.Thm.Tag using (tagAxX)`, `BRA.Thm.TagCodes`, `BRA.Thm.EvalHelpers`.
   * Existing `encAxX`, `outAxX` (preserve verbatim).
   * `body_axX` at top level (NOT abstract — `thClosed` in `ThmT.agda`
     needs `substF2` to reduce through it).
   * `body_axX_eval` inside an `abstract` block (keeps heavy
     normalisation localised).
5. **Verify** `~/.cabal/bin/agda-2.9.0 BRA/Thm/Parts/AxX.agda`.
6. **Edit `ThmT.agda`** — replace the body_axX block with
   `-- body_axX and body_axX_eval moved to BRA.Thm.Parts.AxX .` and
   delete the body_axX_eval block (use `sed -i '' '<start>,<end>d'`).
7. **Verify** `~/.cabal/bin/agda-2.9.0 BRA/Thm/ThmT.agda`.

## Important constraints

* Each Parts file's `body_axX` MUST be at top level (non-abstract).
  ThmT's `thClosed : (x : Nat) (r : Term) -> Eq (substF1 x r thmT) thmT`
  uses `refl`, requiring `substF2` to reduce through `body_axX`.
  Putting `body_axX` inside an `abstract` block in the Parts file
  breaks `thClosed`.  Confirmed empirically during the pilot.
* `body_axX_eval` inside `abstract` is fine: the proof is opaque,
  but the type signature still names `body_axX` and `outAxX`, both
  visible outside.  ThmT just chains `ruleTrans hh be` opaquely.
* `_param` variants (`body_axX_eval_param`, `thmTDispAxX_param`),
  `_lifted` variants, and `thmTDispAxX` itself stay in `ThmT.agda`
  for now: they use the cascade-traversal helpers (`skipAtTag`,
  `hitAtTag`, `dispatchOpens`) which live in `ThmT.agda`'s abstract
  block, plus they reference all sibling `body_Y` / `next_Y` cascade
  entries.  A second-phase split would extract the cascade itself
  into a `BRA/Thm/Cascade.agda` module so per-axiom files could also
  hold their `thmTDispAxX`.

## Remaining axioms (40 still to split)

Group I (10, all small ~50-100 LoC each): `axI`, `axFst`, `axSnd`,
`axConst`, `axComp` (220), `axComp2` (370), `axLift` (190),
`axPost` (330), `axFan` (460), `axZ` (130).

Group II (8): `axIfLfL` (100), `axIfLfN` (180), `axTreeEqLL` (60),
`axTreeEqLN` (110), `axTreeEqNL` (110), `axTreeEqNN` (440),
`axGoodstein` (225).

Group III (recursive, 8): `ruleSym`, `ruleTrans`, `cong1`, `congL`,
`congR`, `mp`, `ruleInst`, `ruleIndBT`.

Group IV (struct, 4): `axEqTrans`, `axEqCong1`, `axEqCongL`, `axEqCongR`.

Group V (prop, 5): `axK`, `axS`, `axNeg`, `axExFalso`, `axContrapos`.

Group VI (safe defaults + sub2, 5): `axRefl`, `axFstLf`, `axSndLf`,
`axIfLfLL`, `axIfLfNL`, `ruleInst2`.

Estimate: ~3,500-5,000 LoC remaining to extract from `ThmT.agda`.
After full split, `ThmT.agda` should be ~10,000 lines (encodeRich +
cascade + dispatchers + thmT itself + thm11 export).

## Use this in the next session for `axRLf` / `axRNd`

Once the split lands, adding `axRLf` and `axRNd` for the unified
`treeRec` primitive becomes:

1. Create `BRA/Thm/Parts/AxRLf.agda` (~250 LoC, self-contained).
2. Create `BRA/Thm/Parts/AxRNd.agda` (~600 LoC, self-contained).
3. In `ThmT.agda`: add `tagAxRLf`/`tagAxRNd` cascade entries
   (~10 LoC), `thmTDispAxRLf`/`thmTDispAxRNd` skip chains (~100 LoC),
   2 `encodeRich` clauses.

No 16k-line file edit needed.
