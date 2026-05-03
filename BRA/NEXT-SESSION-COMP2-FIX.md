# Next session — fix Comp2 (and Fan) so `Comp2Case` matches `CompCase`

## One-line goal

Make `BRA/Thm12/Parts/Comp2.agda`'s `Comp2Case` parameter list match
`BRA/Thm12/Parts/Comp.agda`'s `CompCase` shape — i.e. **drop
`Df'_shape` and `Dg_shape`**.  Same fix for `Fan.agda` (drop
`D2_h1_shape` / `D2_h2_shape`).  Drop the corresponding
`Df_shape` / `D2g_shape` parameters from `BRA/Thm12.agda`'s
`FromBridges`.

The end-of-session deliverable is **Comp2Case's final parameter list,
side-by-side with CompCase's**, plus a green build through
`BRA/GoedelII.agda` and `BRA/Thm14.agda`.

## Why the current shape params exist (the diagnosis)

`BRA/ARCHITECTURE-FINDINGS.md` Finding 1, full text.  TL;DR:

The current `parEncCongL` (in `BRA/Thm12/Param/CongL.agda`) is

```agda
parEncCongL g y_h_T xT =
  ap2 Pair tagCode_congL
    (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT))     -- depth 3
```

The open IH subterm `y_h_T` sits **nested** inside an inner Pair.
When `thmT` distributes through this Pair, the `Fst`-walk has to cross
`y_h_T`, which forces the caller to supply a Pair-shape proof on
`Fst y_h_T`.  Hence the `Df'_shape` / `Dg_shape` parameters.

The unary congruence does NOT have this problem:

```agda
parEncCong1 f' y_h_T =
  ap2 Pair tagCode_cong1
    (ap2 Pair (reify (codeF1 f')) y_h_T)                  -- depth 2, y_h_T at outer Snd
```

`y_h_T` sits at the outer Snd; the Fst-walk only crosses
`reify (codeF1 f')` (closed, Pair-shape via `fstReifyCodeF1`).

## The fix

Reorder `parEncCongL` (and `parEncCongR`) to put `y_h_T` at the outer
Snd — mimicking `parEncCong1`:

```agda
parEncCongL g y_h_T xT =
  ap2 Pair tagCode_congL
    (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)
                  -- inner Fst is closed Pair; y_h_T at outer Snd
```

`parOutCongL` stays the same shape (it's the encoded conclusion of
the congruence, not affected by payload reordering).

`parDispCongL` signature **drops** the shape hypothesis
`Deriv (atomic (eqn (ap1 Fst y_h_T) (ap2 Pair x' y')))` and the two
`y_h'`, `x'` parameters that supplied it.  New signature:

```agda
parDispCongL : (g : Fun2) (y_h_T xT : Term) (u1 u2 : Term) ->
  Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
  Deriv (atomic (eqn (ap1 thmT (parEncCongL g y_h_T xT))
                     (parOutCongL g xT u1 u2)))
```

`thmTDispCongL_param` (in `BRA/Thm/ThmT.agda`) similarly drops
the shape input.  Mirror everything for `parEncCongR` /
`parDispCongR` / `thmTDispCongR_param`.

## The hard part: rewriting `body_congL` / `body_congR`

These are Fun2 dispatchers in `BRA/Thm/ThmT.agda` (search for
`body_congL`).  They navigate the encoded payload of the congruence
proof tree.  With the new payload `Pair (Pair codeF2g xT) y_h`,
the Fun2 navigation changes:

| What to extract | Old (depth 3) | New (depth 3, reordered) |
|---|---|---|
| `codeF2g` | `Lift (Comp Fst Snd)` | `Lift (Comp Fst (Comp Fst Snd))` |
| `xT`      | `Lift (Comp Snd (Comp Snd Snd))` | `Lift (Comp Snd (Comp Fst Snd))` |
| `y_h_T`   | `Lift (Comp Fst (Comp Snd Snd))` | `Lift (Comp Snd Snd)` |

(The above uses the conventional payload indexing `Snd a = payT`,
`Fst payT, Snd payT, …` — verify by looking at the existing
`body_congL` for the input convention.  Read what `parOutCongL g xT u1 u2`
looks like and trace back.)

Then `body_congL_eval` (and `body_congL_eval_param`, plus any
`_lifted` / `_doublelifted` versions if they exist — search the
file) need to be re-authored to prove that the new dispatcher
computes `parOutCongL g xT u1 u2`.  These proofs are 50–150 lines
each, structured as `pairOfFan_eval` / `pairOfConst_eval` chains.

**Get the type annotations right by tracing from `parOutCongL`'s
output structure backwards through the dispatcher.**  Easy to be
off-by-one.

## Then drop the shape params from consumers

1. `BRA/Thm12/Parts/Comp2.agda`: drop `Df'_shape` and `Dg_shape`
   from `Comp2Case`.  Remove any line in the body that referenced
   `Df'_shape x` or similar.

2. `BRA/Thm12/Parts/Fan.agda`: drop `D2_h1_shape` and
   `D2_h2_shape` from `FanCase`.  Same internal cleanup.

3. `BRA/Thm12.agda`'s `FromBridges`: drop `Df_shape` and
   `D2g_shape` parameters.  Update `thm12_F1 (Comp2 ...)` and
   `thm12_F2 (Fan ...)` dispatch clauses to no longer pass shape
   args.

## Verification targets

- `~/.cabal/bin/agda-2.9.0 BRA/Thm/ThmT.agda` — green
- `~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/Comp2.agda` — green; verify
  parameter list matches `CompCase` shape (no `_shape` params)
- `~/.cabal/bin/agda-2.9.0 BRA/Thm12/Parts/Fan.agda` — green; same
- `~/.cabal/bin/agda-2.9.0 BRA/Thm12.agda` — green
- `~/.cabal/bin/agda-2.9.0 BRA/GoedelII.agda` — green (full chain)
- `~/.cabal/bin/agda-2.9.0 BRA/Thm14.agda` — green

Acceptable to break: `BRA/Thm12/Parts/RecV2.agda`, `BRA/StepT12.agda`,
`BRA/Thm12RecCheck.agda` — exploratory side files per the architecture
doc.  Don't touch them.

## Trick inspiration

`/Users/coquand/CHWISTEK/ndw2.pdf` solved the Carneiro insight for
the `Rec/RecP basePair_param` problem in a previous session via a
clever encoding rearrangement.  Worth a 15-minute read at the start
in case there's a related shortcut that simplifies `body_congL`'s
rewriting.  The current plan (mimic `parEncCong1` literally) is
sound regardless, so this is an optional optimization.

## Constraints

- ASCII only; `--safe --without-K --exact-split`
- No postulates, no holes, no `with`-abstraction, no dot patterns
- **No new "shape field" added to `Thm12_FX_Result` records** — the
  shape obligation should disappear, not be relocated.
- Don't touch unrelated files.  Goal is a focused fix.

## What success looks like

The end of the session, you can paste the final `Comp2Case`
parameter list next to `CompCase`'s and the only difference is the
extra arity (Comp2 has one more sub-IH, the Fun2 `D2_h`).  No
`_shape` lines anywhere.  And the GoedelII chain is green.

## Headline output

After the work, run:

```
echo "=== CompCase ==="
sed -n '/^module CompCase/,/^  where/p' BRA/Thm12/Parts/Comp.agda
echo
echo "=== Comp2Case ==="
sed -n '/^module Comp2Case/,/^  where/p' BRA/Thm12/Parts/Comp2.agda
```

and present the output.  That's the deliverable.
