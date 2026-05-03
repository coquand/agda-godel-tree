# Next session — finish ThmT split + Thm 12 for treeRec + finish Thm 12

## Inputs to read first

1. `BRA/MONOLITH-SPLIT-PROGRESS.md` — methodology + axiom inventory.
2. `BRA/NEXT-SESSION-R-UNIFICATION.md` — context on `treeRec` and the
   `axRLf` / `axRNd` work that's blocked on the refactor.
3. `BRA/ARCHITECTURE-FINDINGS.md` — Findings 1 (parDispCongL depth-3)
   and 2 (Rec/RecP misdesign) that motivated the refactor + axRLf/axRNd.

## State at end of previous session

* `BRA/Thm/EvalHelpers.agda` (502 LoC) — done.
* `BRA/Thm/TagCodes.agda` (143 LoC) — done.
* 4 of 44 axiom Parts files split (Rec/RecP family): `AxRecLf.agda`,
  `AxRecNd.agda`, `AxRecPLf.agda`, `AxRecPNd.agda`.
* `ThmT.agda` 16,758 -> 15,198 LoC (-1,560).
* `treeRec : Fun1 -> Fun2 -> Fun2` constructor exists in `BRA/Term.agda`;
  full consumer cascade green; `encodeRich` did NOT trigger
  `SplitError.UnificationStuck` after the dot-pattern cleanup.
* `axRLf` / `axRNd` axioms NOT yet in `BRA/Deriv.agda` (intentionally
  reverted: they require the cascade material which is easier to add
  after the split).
* `Thm12.FromBridges` has a parametric `D_treeRec_complete` placeholder.

## Goals for this session (in priority order)

### Goal 1 — finish the ThmT monolith split (Phase 2)

Move `body_axX` and `body_axX_eval` for the remaining 40 axioms into
their `BRA/Thm/Parts/AxX.agda` files.  Pattern is established and
validated; this is mechanical mirror work.

Order (largest first to maximize ThmT shrinkage):
* `axTreeEqNN` (~440), `axFan` (~460), `axComp2` (~370),
  `axPost` (~330), `axGoodstein` (~225), `axComp` (~220),
  `axLift` (~190), `axIfLfN` (~180), `axZ` (~130),
  `axTreeEqLN` (~110), `axTreeEqNL` (~110), `axIfLfL` (~100),
  `axConst` (~100), `axTreeEqLL` (~60).
* Group V (10 small): `axI`, `axFst`, `axSnd`, plus 7 propositional /
  equality / structural rules with simple short bodies.
* Group VI (4 safe-defaults): `axFstLf`, `axSndLf`, `axIfLfLL`,
  `axIfLfNL`.
* Group III (8 recursive): `ruleSym`, `ruleTrans`, `cong1`, `congL`,
  `congR`, `mp`, `ruleInst`, `ruleIndBT`, `ruleInst2`.

Methodology for each axiom (verified pattern from previous session,
documented in `BRA/MONOLITH-SPLIT-PROGRESS.md`):

```
1. grep -n '^  body_axX\b\|^  body_axX_eval\b' BRA/Thm/ThmT.agda
2. Read body_axX and body_axX_eval from ThmT.
3. Write BRA/Thm/Parts/AxX.agda:
     imports BRA.Base, BRA.Term, BRA.Formula, BRA.Deriv,
              BRA.Thm.Tag, BRA.Thm.TagCodes, BRA.Thm.EvalHelpers
     existing encAxX, outAxX (preserve)
     body_axX (NOT abstract — thClosed needs substF2 to reduce)
     abstract block:
       body_axX_eval = ... (verbatim from ThmT)
4. ~/.cabal/bin/agda-2.9.0 BRA/Thm/Parts/AxX.agda  -- verify
5. Edit ThmT: replace body_axX block with comment, sed-delete eval block.
6. ~/.cabal/bin/agda-2.9.0 BRA/Thm/ThmT.agda  -- verify
```

Expected ThmT.agda end size: ~6,000-7,000 LoC (Phase 2 only — see
`BRA/MONOLITH-SPLIT-PROGRESS.md` for full breakdown).  If time permits,
also do Phase 3: move `thmTDispAxX` lemmas into Parts files (each
imports a shared `BRA/Thm/Cascade.agda`).  Phase 3 brings ThmT down
to ~800 LoC.

### Goal 2 — add `axRLf` and `axRNd` as clean Parts files

After Goal 1, this is small:

1. `BRA/Deriv.agda` — add the two primitive axioms (already drafted in
   prior-session memory, just paste back).
2. `BRA/Thm/Tag.agda` — `tagAxRLf = suc tagRuleIndBT2`,
   `tagAxRNd = suc tagAxRLf`.
3. `BRA/Thm/TagCodes.agda` — add `tagCode_axRLf`, `tagCode_axRNd`,
   `tagCode_treeRecFunc`.
4. `BRA/Thm/Parts/AxRLf.agda` — new file, ~250 LoC self-contained
   (depth-3 payload, RHS = `ap1 f p`).  See prior-session draft.
5. `BRA/Thm/Parts/AxRNd.agda` — new file, ~600 LoC (depth-5 payload).
6. `BRA/Thm/ThmT.agda` — add cascade entries (4 lines), 2 encodeRich
   clauses, 2 `thmTDispAxRLf`/`Nd` skip chains (~50 LoC each, OR move
   into Parts files if Phase 3 lands).

### Goal 3 — prove `thm12_F2 (treeRec f s)` (= Step 7 of NEXT-SESSION-R-UNIFICATION.md)

With `axRLf, axRNd` available, replicate the structure of
`BRA/Thm12/Parts/RecP.agda` (the `RecP` Construction module) but
with the leaf case `ap1 f p` instead of `O`.  Cleaner than RecP
because no `corOfReify` bridge / `z_corLemma` needed (`f : Fun1`
reduces by its own axioms, not via a corOfReify bridge).

Once delivered, discharge the `D_treeRec_complete` parameter in
`BRA/Thm12.agda`'s `FromBridges` module.

### Goal 4 — finish Thm 12

After Goal 3, audit `BRA/Thm12.agda` for remaining
`FromBridges`-parameters that haven't been discharged.  See the
"Generic Fst-shape" parameters (`Df_shape`, `D2g_shape`) and any
`D_correct_*_univ` universal closures that are still abstract.

This is the path to fully-derived (no parameter) Thm 12.  Then
`BRA/GoedelII.agda` becomes parameter-free.

## Out of scope this session

* Pruning admissible axioms (axRefl / ruleSym / cong1 etc.) -- short
  proofs, but a separate refactor.
* `parDispCongL` depth-3 re-encoding (Finding 1 of
  ARCHITECTURE-FINDINGS).
* Goedel II downstream layers beyond Thm 12.

## Reminders

* `body_axX` MUST stay non-abstract in Parts files (`thClosed` requires).
* Each Parts file uses an `abstract` block for `body_axX_eval` to
  keep the proof opaque externally.
* No new dot patterns, `with`-abstractions, REWRITE pragmas, or
  postulates.
* Verify each Parts file individually + verify ThmT after each
  deletion; don't batch deletions across multiple axioms without
  intervening typecheck.
