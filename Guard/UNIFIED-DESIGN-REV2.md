# UNIFIED-DESIGN Rev 2: hyp-free thmT with codeTrueT sentinel

## Context

REV1 concluded that Thm14EV3 couldn't port cleanly due to Agda's
`--without-K` splitting limitations on `ruleInst` when the outer
Deriv index is constrained to atomic.  On re-reading guard15.pdf
(Def 12, p.15), the user identified that the REAL issue is our
architectural deviation from Guard:

1. Guard's `th` is a hyp-free function: `th : Nat → Nat`.  No
   hypothesis argument.  It enumerates the Gödel numbers of ALL
   theorems of BRA absolutely.  Meta-soundness: "th(0), th(1), ...
   enumerates the Gödel numbers of all and only the theorems of
   BRA."
2. Our `thmT : Term → Fun1` takes an `hCode` argument (the encoded
   hypothesis), because our Deriv was hyp-carrying.  With the
   unified hyp-less Deriv, `hCode` is vestigial.
3. Our `thmT` uses `O` as a validation-failure sentinel.  `O` is
   not the code of any formula, so the image of our `thmT`
   includes non-formula values — it doesn't match Guard's meta-
   property that th's image = theorem set.

REV2's design fixes all three:

- `thmT : Fun1` (single argument: the encoded proof tree).
- No `hCode` passing around.  No `case26` (which was the
  "ruleHyp + hypothesis-match" case).  `trivCT`, `trivC`, etc. all
  become dead code.
- Validation-failure sentinel changes from `O` to `codeTrueT`,
  which is the Gödel code of the trivially-true equation `O = O`.
  This ensures every `thmT` output is the code of SOME theorem
  (either the intended conclusion, or the trivial `0=0` fallback).

## codeTrueT

```agda
codeTrueT : Term
codeTrueT = reify (codeEqn (eqn O O))
          = ap2 Pair (reify (code O)) (reify (code O))
          = ap2 Pair (ap2 Pair O O) (ap2 Pair O O)
          = ap2 Pair falseT falseT
```

(Yes: the "code of 0=0" contains `falseT` as subterms — `falseT`
is our term for `Pair O O`, which is `reify (code O)`.  The naming
is unfortunate but the tree structure is correct: `codeTrueT` is
the codeEqn of `eqn O O`, a trivially-true statement.)

`Deriv (atomic (eqn O O))` is trivially inhabited via `axRefl O`.

## Why the sentinel change matters

Under the chain hypothesis `thmT(var zero) = j` (where `j` is the
code of the Gödel sentence):

- Old `O`-sentinel: `thmT(x) = j` implies `x` encodes a valid proof
  of gsCR, because `j ≠ O` syntactically (j is a non-trivial Pair,
  O is lf).  Works, but inelegant (the image includes `O`).
- New `codeTrueT`-sentinel: `thmT(x) = j` implies `x` encodes a
  valid proof of gsCR, as long as `j ≠ codeTrueT`.  Since gsCR is
  a non-trivial Gödel sentence (not `0=0`), this holds.  Every
  thmT output is the code of a theorem — matches Guard's meta-
  property.

## Changes to thmT

### Structure unchanged

`thmT` is still defined as `Rec O thmTStep` (primitive recursion
on trees).  `thmTStep` still uses `Fan`/`IfLf`/`branch` combinators
for case analysis.  Validation of nested encodings (check1mp,
check2mp at case33; middle-term agreement at case19V3) is
preserved.

### What's removed

- `hCode : Term` parameter on `thmT`, `thmTStep`, `ndDispatchV3`,
  `ndT*V3`.
- `case26` (the hypothesis-use case).  No `ruleHyp` in hyp-free
  Deriv means no need to match `body = hCode`.
- `case26Match` lemma (gone with case26).
- `case26` references in `ndT*V3` dispatch chain — the chain
  skips from case25 to case27 directly.
- All `trivCT`, `trivC`, `hCode` passings in downstream modules.

### What's changed

- `kF2 O` → `kF2 codeTrueT` in every fallback branch:
  - `case33` (encMp): both `check1mp` and `check2mp` failure
    branches return `codeTrueT` (was `O`).
  - `case19V3` (trans): middle-term mismatch returns `codeTrueT`.
  - `lfDispatchV3`'s tag13 mismatch: returns `codeTrueT`.
  - `ndDispatchV3`'s bottom-of-chain (`sndArg2`): stays as
    `sndArg2` (not a literal sentinel; it returns the passthrough
    recs — the *caller* interprets "non-matching tag" as a
    sub-encoding passthrough).  No change.

### Signature changes

```agda
-- Old:
thmT       : Term -> Fun1
thmTStep   : Term -> Fun2
ndDispatchV3 : Term -> Fun2
ndT1V3 ... ndT33V3 : Term -> Fun2
case26 : Term -> Fun2

-- New:
thmT       : Fun1
thmTStep   : Fun2
ndDispatchV3 : Fun2
ndT1V3 ... ndT34V3 : Fun2   (-- numbering shifts since case26 gone)
-- case26 removed
```

## Changes to encoders

### What survives

- `encAxI, encAxFst, ..., encAxGoodstein`: unchanged, but their
  correctness lemmas drop the `hCode : Term` argument.
- `encRuleSym, encRuleTrans, encCong1/L/R`: same.
- `encRuleInst`: unchanged (tag n23, uses `substOp`).
- `encAxK, encAxS, encAxNeg`: unchanged (tags n30-32).
- `encMp`: unchanged (tag n33).

### What's removed

- `encRuleHyp` and `encRuleHypCorr`: no `ruleHyp` in hyp-free
  Deriv.  Gone.

### What's changed

- All `*Corr` lemma signatures lose `(hCode : Term)`:
  - Old: `encAxICorr : (hCode tC : Term) -> Deriv (eqF (ap1 (thmT hCode) (encAxI tC)) ...)`
  - New: `encAxICorr : (tC : Term) -> Deriv (eqF (ap1 thmT (encAxI tC)) ...)`
- `*Pass` lemmas lose `hCode` similarly.
- Dispatch-chain lemmas (`passthroughSucV3`, `ndDispatchV3PairMiss`,
  etc.) lose `hCode`.

## Changes to downstream

### GodelI, Thm14EV3, SubstTForPrecompClassical

- Module imports update: `Guard.ThFunTForV3Unify` → new name
  (e.g., `Guard.ThFunTForHF` for "hyp-free") with the updated
  types.
- `godelIClassical`'s signature simplifies: no need for
  `hCode = trivCT` passing.
- `SubstTForPrecompClassical`'s `trivCT`, `trivC` become unused
  (the latter stays for the Gödel sentence's self-reference, but
  is no longer applied to `thmT`).  May be able to simplify gsCR's
  form slightly.

### Chain and Gödel II

- Chain steps drop the `trivCT` threading.
- Simpler signatures throughout.
- No observable behavior change for the chain's reasoning — only
  the hyp parameter is eliminated.

## Does this enable Gödel II?

Yes — same as previous plans, now architecturally clean:

- Chain produces specific encoded terms (`combined`) via encoder
  composition.
- Chain step 5: under `conjHyp = atomic (eqn thx j)` (where
  `thx = ap1 thmT (var zero)`), derive atomic `(thmT combined =
  codeBotT)`.
- Closure: substitute conBRAEqn at x := combined → atomic
  `(TreeEq (thmT combined) codeBotT = falseT)`.  Combine with step
  5 + treeEqSelfReify → atomic `(O = falseT)`.  Contradicts
  Consistent.
- The `not conjHyp` / gsCR route also works cleanly under the
  ~-formula gsCR (see REV1's "formula-level negation" resolution),
  but may not be needed if we can close directly via the above.

`thm14EV3` is NOT reintroduced.  It was the wrong abstraction.
Guard doesn't formalize "Deriv → encoded proof" as a recursor —
users CONSTRUCT encoded proofs directly via encoder composition,
parallel to their Deriv proofs.  Our chain follows this pattern.

## Migration order

### [unify-5a] New hyp-free thmT

- Create `Guard/ThFunTForHF.agda` (or reuse the name
  `Guard/ThFunTForV3Unify` and overwrite — preferable for clarity).
- `thmT : Fun1`, `thmTStep : Fun2`, `ndDispatchV3 : Fun2` (no
  hCode).
- `case26` removed, `ndT26V3` renamed/removed in dispatch chain.
- `codeTrueT` defined and used in place of `O` sentinels.
- Typechecks standalone.

### [unify-5b] Update downstream -Unify modules

- `ThFunTForV3DefsUnify`: drop hCode, update `case26Match` removal,
  `intermediateGenericV3`.
- `ThFunTForV3PassUnify`: drop hCode.
- `ProofEncUnify`, `ProofEncFormula`: drop hCode in all *Corr and
  *Pass lemmas.  Remove `encRuleHyp` and friends.
- `SubstTForPrecompClassicalUnify`: drop hCode threading.

### [unify-5c] Gödel II chain retargeting

- Rewrite the chain (steps 1-3 currently via provToBRA bridge;
  replace with direct hyp-free DerivF constructions).
- Step 4 + 5 new constructions using hyp-free encoders.
- Closure via equational argument + Consistent.

### [unify-5d] Cleanup

- Delete obsolete non-Unify modules.
- Rename -Unify → unified names.
- Delete `Guard.Step`, `Guard.Provable`, `Guard.BRA`, `Guard.BRAGodelIBridge`,
  `Guard.GodelIIBRAPort`, etc.

## Estimated size

- [unify-5a]: ~500 lines (rewrite of ThFunTForV3 sans hCode).
- [unify-5b]: ~1500 lines touched, mostly mechanical hCode removal.
- [unify-5c]: ~500 lines (chain transcription).
- [unify-5d]: ~500-1000 lines deleted.

Total: ~2500 lines touched, roughly 2-3 sessions.

## Open questions (decide during implementation)

1. Whether to keep `tag26` as a hole in the dispatch chain (for
   compat with existing encoder tag numbering) or renumber
   downstream tags (n27 → n26, n28 → n27, etc.).  Renumbering is
   cleaner but touches every Corr/Pass lemma.  Hole is easier —
   skip case26 but keep the tag slot empty (returns sentinel via
   the chain).
   
   Recommendation: keep hole (tag26 produces codeTrueT).  Existing
   encoders use tags n23 and below + n27 and above; renumbering
   buys nothing.

2. Whether `0=0` should be literally `eqn O O` or something more
   semantically convenient.  `eqn O O` is simplest and directly
   derivable by `axRefl O`.  No reason to deviate.

## What's discarded from earlier plans

- UNIFIED-DESIGN-REV1.md's "Thm14EV3 stays on old Deriv" —
  discarded.  No need for old Deriv at all.
- DerivE/Deriv split — discarded.  Guard has no such split; the
  right fix was hyp-free thmT + hyp-free Deriv, not two Deriv
  types.
- thm14EV3 recursor on Deriv — discarded.  Not in Guard.  Users
  compose encoders directly.
- ProofE3 record type — discarded.  Not in Guard.  Replace with a
  Sigma type if ever needed, but the chain doesn't need it.
