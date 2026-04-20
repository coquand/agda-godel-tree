# Next Session: Complete the V3 Redesign (Phases D6–D8)

## Setup

```
cd /Users/coquand/CHWISTEK
~/.cabal/bin/agda-2.9.0 <file>    # use THIS binary (not /opt/homebrew/bin/agda)
```

Last commit: `9fbca6f [redesign/phase-D5] Complete V3 theorem 14: thm14EV3 total dispatcher`.

## State of play

**D1–D5 done.** Summary:

- **D1:** `RecP : Fun2 -> Fun2` added to `Guard/Term.agda`, with `axRecPLf`/`axRecPNd` axioms in `Guard/Step.agda`. All downstream substitution / code-of / passthrough predicates extended.
- **D2:** `Guard/SubstOp.agda` — `substOp = RecP stepSubstP`. Correctness: `substOpEquiv` (= `closedSubstTFor tC xC` on reified trees) and `substOpCorrect` (Term→code→subst full picture). No postulates.
- **D3:** `case23V3 = Fan (Fan origA recsBL substOp) (Fan origA recsBR substOp) Pair` defined in `Guard/ThFunTForV3.agda`. `case23V3Match` proved in `ThFunTForV3Defs.agda`.
- **D4:** `thm14EV3Inst` fully proved in `Guard/Thm14EV3.agda`. Uses `case23V3Match` + `substOpCorrect` per equation side. Includes `aRPassV3` helper for `ndDispatchV3` passthrough at the `aR = Pair tCt xCt` tag.
- **D5:** Full V3 dispatch chain extended with `n27` (`case27` for `axRecPLf`) and `n28` (`case28` for `axRecPNd`). `thm14EV3 : {H eq : Equation} -> Deriv H eq -> ProofE3 H eq` covers all 29 Deriv constructors recursively.

The full file set — `Guard/*.agda` — typechecks under `--safe --without-K --exact-split` with the Cabal Agda 2.9.0 binary.

## What's left (D6–D8)

### D6 — Gödel I on V3 (the hard part)

**Goal:** `godelIDeriv : Deriv godelSentence_V3 (eqn trueT falseT)`.

**THE REAL obstacle, uncovered while attempting this session.**  V2's `godelSentence` (in `Guard/SubstTForPrecomp.agda`) works because `thFunTFor` is *hCode-agnostic* — a single closed `Fun1`.  V3's `thmT` is *hCode-specific* — the case26 check inside `thmT hCode` on an `encHyp(body)` encoding returns `hCode` only when `body = hCode`, else sentinel `O`.

The V2 diagonal trick (substitute `var v1 ↦ reify templateCode`) gives a sentence whose `thmT`'s `hCode` becomes `reify templateCode_V3`.  But `thm14EV3Hyp H` produces a proof-encoding `enc = encHyp (reify (codeEqn H)) = encHyp (reify cGS_V3)`.  Its `corr` witness is

```
corr pe : thmT (reify cGS_V3) enc = reify cGS_V3
```

with `hCode = reify cGS_V3`, NOT `reify templateCode_V3`.  Since `cGS_V3 ≠ templateCode_V3` (they differ by the diagonal substitution), these two `thmT` applications *disagree* on `enc`:

```
thmT (reify cGS_V3)        enc = reify cGS_V3      -- case26 matches
thmT (reify templateCode_V3) enc = O               -- case26 mismatches → sentinel
```

So the sentence's instantiated form can't be directly rewritten via `corr pe` — there is no bridge.

**Resolution (discovered after deeper analysis).**  Use two *separate* free variables in the template — `var v1` for the `substOp` target (to be substituted with `reify templateCode_V3'`), and `var v2` for the `thmT` hCode (to remain free until ruleInst on it fires).  Then `corr pe` and the sentence's hCode both become `reify cGS_V3'` at the right moment.

**V3 template with two free variables:**

```agda
template_V3' = eqn (ap2 TreeEq (ap1 (thmT (var v2)) (var zero))
                              (ap2 substOp (ap2 Pair (var v11) (var v12)) (var v1)))
                  poo
-- free: 0, 1, 2, 11, 12

godelSentence_V3' = substEq v1 (reify templateCode_V3') template_V3'
-- After: thmT still uses  var v2  (free); substOp target becomes reify templateCode_V3'.
```

Under ambient hyp = `godelSentence_V3'`, derive:

```
dG  = ruleHyp : Deriv gs gs
pe  = thm14EV3 dG                       -- ProofE3 gs gs (hCode = reify cGS_V3')
enc = encT pe
corr pe : thmT (reify cGS_V3') enc = reify cGS_V3'

d1 = ruleInst v2  (reify cGS_V3')      dG   -- thmT's hCode → reify cGS_V3'
d2 = ruleInst v11 (reify crTC_V3')     d1   -- substOp's 1st Pair arg → reify crTC_V3'
d3 = ruleInst v12 (reify (natCode v1)) d2   -- substOp's 2nd Pair arg
d4 = ruleInst 0   enc                  d3   -- proof slot → enc

-- d4's conclusion is:
--   TreeEq(thmT(reify cGS_V3') enc, substOp(Pair (reify crTC_V3')(reify(natCode v1)))(reify templateCode_V3')) = poo

-- By corr pe (LHS) and diagFTargetV3 (RHS): both sides = reify cGS_V3'.
-- By treeEqSelf: TreeEq(X, X) = O.  Thus O = poo.  QED.
```

**Why the two-variable trick works.**  In V2, `thFunTFor` is hCode-agnostic, so the sentence's `thFunTFor(var 0)` and `corr pe`'s `thFunTFor` are trivially the same function.  In V3, we keep `thmT`'s hCode as a free `var v2` until just before it's needed, at which point `ruleInst v2 (reify cGS_V3')` binds it to match `corr pe`'s hCode.  This is a clean mechanical translation of V2's argument, not a structural redesign.

**Implementation plan (for next session):**

1. ✅ DONE. `Guard/SubstTForPrecompV3.agda` is written (~4.9s compile).  All
   abstract declarations in place: `codeLhsTV3`, `templateCodeV3`, `crTCV3`,
   `godelSentenceV3`, `cGSV3`, `cGSisCSV3`, `cstfV3`, `godelSentenceV3Form`.

2. ✅ DONE. `Guard/GodelIV3.agda`'s `diagFTargetV3` is proved:
     substOp(Pair(reify crTCV3)(reify(natCode v1)))(reify templateCodeV3)
       = reify cGSV3
   via `substOpEquiv + closedSTFNd + cGSisCSV3`.

3. PENDING.  The ruleInst chain for `godelIDerivV3` is blocked on
   performant substEq-lemmas.  The naive approach (4× `refl`) compiles
   in ~430s because each step re-traverses the large `reify templateCodeV3`.

**Next session: write schematic substEq-lemmas V2-Fast-style.**

The specific lemmas needed (all in `SubstTForPrecompV3.agda` abstract block,
each using Nelson-style structural proofs — NO naive `refl`):

```agda
-- (a) substF1 propagates through  thmT :
substThmT : (x : Nat) (r Y : Term) ->
  Eq (substF1 x r (thmT Y)) (thmT (subst x r Y))

-- (b) substF2 is identity on closed  substOp :
substSubstOpClosed : (x : Nat) (r : Term) ->
  Eq (substF2 x r substOp) substOp

-- (c) For each step of the ruleInst chain, a one-line Deriv-level
--     conversion lemma built from (a), (b), and Nelson's substReify.
```

The `godelIDerivV3` draft is already in a block comment at the bottom
of `Guard/GodelIV3.agda`.  Once the substEq-lemmas exist, activate it
by uncommenting and adjusting the convert steps to use the schematic
lemmas (not definitional equality).

Estimated: one full session for the substEq-lemmas + activation.

**Bottom line.** D6 is a mechanical port after all — the trick is to add one more free variable (`var v2`) for thmT's hCode, separate from V2's `var v1`.

### D7 — Gödel II on V3 + negative test

Once `godelIDeriv` exists:

```agda
-- Guard/GodelIIV3.agda
provBot : Prov3 godelSentence_V3 (eqn trueT falseT)
provBot = necessitation (thm14EV3 godelIDeriv)

conToBot : {hyp : Equation} ->
           Deriv hyp conSentenceV3 ->
           Deriv hyp (eqn trueT falseT)
conToBot dCon = diagContradict codeBotT
  (ruleTrans (ruleSym (congL TreeEq codeBotT (corr provBot)))
             (ruleInst zero (enc provBot) dCon))
```

Note: V3 `conSentenceV3` = `eqn (ap2 TreeEq (ap1 (thmT hCodeH) (var zero)) codeBotT) falseT` is **H-dependent** (hCodeH = reify (codeEqn H)).  In V2 it was H-independent.

**Negative acceptance test** — `Guard/GodelIITestV3.agda`:

```agda
fakeTrans : ProofE3 whatever (eqn trueT falseT)
fakeTrans = thm14EV3Trans (thm14EV3Refl _ trueT) (thm14EV3Refl _ falseT)
```

MUST not typecheck — `case19V3` rejects `trans(refl trueT, refl falseT)` because the middle terms (`trueT` vs `falseT`) disagree.  If it DOES typecheck, the V3 redesign has a hole.

Actually the check may fail at a different layer — `thm14EV3Trans`'s type signature requires `ProofE3 H (eqn t u)` and `ProofE3 H (eqn u v)` with the same `u`.  Since `u = trueT` from the first and `u = falseT` from the second, the types don't unify.  This is the static guard.

### D8 — Prov refactor, LaTeX, cleanup

- `Guard/ProvV3.agda` with `Prov3 H eq := Σ enc, corr` over the new `thmT ⌜H⌝`.
- Update `Guard/guard-godelII.tex` (currently in `archive/`) — restore, add a new section on the RecP extension and substOp, re-derive Section 6 using `case19V3` + `substOp` + `case23V3`.
- Rename `*V3.agda` files to drop the suffix (or leave as V3 for clarity).

## Key files (updated set)

- `Guard/SubstOp.agda` — substOp + correctness (D2 complete).
- `Guard/Term.agda`, `Guard/Step.agda` — RecP primitive + axioms (D1).
- `Guard/ThFunTForV3.agda` — case23V3, case27, case28, extended chain to ndT29V3.
- `Guard/ThFunTForV3Pass.agda` — 29-branch miss chains.
- `Guard/ThFunTForV3Defs.agda` — case23V3Match.
- `Guard/Thm14EV3.agda` — all 29 thm14EV3* functions + top-level dispatcher.
- `Guard/archive/v2/GodelII.agda`, `Guard/archive/v2/GodelIIFull.agda` — V2 reference to port.
- `Guard/SubstTForPrecomp.agda` — V2 diagonal machinery to mirror for V3.

## Anticipated session count (updated)

| Phase | Estimate |
|---|---|
| D6    | 2 sessions (SubstTForPrecompV3 + GodelIV3) |
| D7    | 1 session (mostly mechanical port) |
| D8    | 2 sessions (LaTeX + rename) |
| Slippage | 1 session |

**Total remaining: ~6 sessions.**

## Opening move for the next session

1. `cd /Users/coquand/CHWISTEK && git pull`
2. Read this doc + `Guard/archive/v2/GodelIIFull.agda` for reference.
3. Start by copying `SubstTForPrecomp.agda` to `SubstTForPrecompV3.agda`, then do the three substitutions (thFunTFor → thmT(var v1), substTFor → substOp, drop v11/v12).  Work through compilation errors one at a time.
4. Commit each sub-lemma that typechecks. Don't accumulate untested chains longer than ~20 lines.
