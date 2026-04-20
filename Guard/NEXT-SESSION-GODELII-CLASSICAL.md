# Next Session: Classical Gödel II

## Setup

```
cd /Users/coquand/CHWISTEK
~/.cabal/bin/agda-2.9.0 <file>     # use THIS binary, not /opt/homebrew/bin/agda
```

Repo: `https://github.com/coquand/agda-godel-tree.git`, branch `main`.
Last commit: `8229215` `[godelI-classical] Classical Gödel I with single-free-variable sentence`.
Everything under `Guard/` typechecks under `--safe --without-K --exact-split`.
Each file compiles under 10s via the abstract-block + fused-lemma pattern.

## What's done (classical Gödel I)

Commit `8229215` delivers Ryan's Lemma 3 in tree form:

- `Guard/CodeOfReify.agda` — **`cor : Fun1`** (= `Rec poo stepCor`), a pure Rec-based Fun1 with lemma
  ```agda
  corOfReify : (t : Tree) -> {hyp : Equation} ->
    Deriv hyp (eqn (ap1 cor (reify t)) (reify (code (reify t))))
  ```
  No new primitive; proved by induction on `t`.
- `Guard/SubstTForPrecompClassical.agda` — one-free-variable diagonal. Template `lhsTermCR` uses
  `substOp (Pair (ap1 cor (var v1)) (reify (natCode v1))) (var v1)`.
  After `substEq v1 := reify templateCodeCR`, `gsCR` has **only `v_0` free** (proof slot). `crTCCR = code (reify templateCodeCR)` and `cGSCR = codeEqn gsCR`.
- `Guard/GodelIClassical.agda` —
  ```agda
  godelIClassical       : Deriv Triv gsCR -> Deriv Triv (eqn trueT falseT)
  godelIClassicalContra : Consistent Triv -> Deriv Triv gsCR -> Empty
  ```
  `Triv = eqn O O` (trivially-consistent hypothesis; `trivCT = reify (codeEqn Triv)`).

Meaning of `gsCR`: after the diagonal identity, `gsCR ≡ TreeEq(thmT(trivCT)(x_0), ⌜gsCR⌝) = falseT`, i.e. "for every candidate encoding `x_0`, its decoding under the Triv-evaluator is not the code of me". One free variable — classical Ryan Lemma 3 form.

## Target

```agda
ConTriv : Equation
ConTriv = eqn (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT) falseT

godelIIClassical : Deriv Triv ConTriv -> Deriv Triv (eqn trueT falseT)

godelIIClassicalContra : Consistent Triv -> Deriv Triv ConTriv -> Empty
```

`ConTriv` says "no `x_0` is a Triv-derivation of ⊥". The positive form says: if Triv proves its own consistency, Triv is inconsistent. Contrapositive is the sharp form of Gödel II.

## Why the existing V3 Gödel II is not enough

`Guard/GodelIIV3.agda` proves
```
conSentenceV3 : eqn (ap2 TreeEq (ap1 (thmT (reify cGSV3)) (var zero)) codeBotT) falseT
conToBotV3    : Deriv hyp conSentenceV3 -> Deriv hyp (eqn trueT falseT)
```
but this is a statement about `gsV3`-derivations of ⊥, not about Triv-derivations of ⊥. And `gsV3` itself has the two-free-variable exhibition property — not classical Gödel I. For classical Gödel II we need the Triv-evaluator version, linked through `godelIClassical`.

## The barrier: the DC2 bridge

Standard Gödel II (Löb-style) routes: Gödel I + DC1 + DC2 + DC3 ⟹ Gödel II. In our equational setting:
- **DC1** (necessitation): `Guard/Thm14EV3.agda` (2448 lines) turns `Deriv H eq` into `ProofE3 H eq` with polymorphic `corr`. ✓
- **DC2** (internal modus ponens): **missing**. Required shape: a closed Fun1 `Phi` such that, polymorphically in any ambient `hyp`,
  ```
  Deriv hyp (eqn (ap1 (thmT trivCT) v0) (reify cGSCR))
  -- implies --
  Deriv hyp (eqn (ap1 (thmT trivCT) (ap1 Phi v0)) codeBotT)
  ```
  i.e. `Phi` transforms any encoding of a Triv-derivation of `gsCR` into an encoding of a Triv-derivation of ⊥.
- **DC3** (Prov(⌜A⌝) ⟹ Prov(⌜Prov(⌜A⌝)⌝)): not needed for this route; our Gödel I does not use it.

`Phi` is the internalisation of `godelIClassical`. Its body is a structural map on proof-encodings that mirrors the Agda-level construction
```
godelIClassical d = ruleTrans (ruleSym selfEq) stepB
  where stepB = ruleTrans (ruleSym (congR TreeEq ... diagFTargetCR)) stepA
        stepA = ruleTrans (ruleSym (congL TreeEq rhsT corrPf)) d1Conv
        d1Conv = eqSubst (Deriv Triv) (subst0GSCR enc) d1
        d1 = ruleInst zero enc d       -- d is the input; enc = encT (thm14EV3 d)
        corrPf = eqSubst ... (corr (thm14EV3 d))
        selfEq = treeEqSelf (reify cGSCR)
```
All of these steps have explicit **proof-code** formulations under our tag scheme (tags `n0..n28` in `ThFunTForV3.agda`). `Phi` must emit the composite encoding.

## Scope estimate

**Size**: ~1500–2500 new Agda lines, comparable to `Thm14EV3.agda` (2448). The core work is packaging each Agda-level derivation step as a closed tree-builder and proving, by `Rec`/`RecP` induction, that `thmT trivCT` on the builder's output yields the correct encoded equation.

**Sessions**: 3–5.

## Proposed file layout

1. **`Guard/ProofEnc.agda`** — small constants and utilities.
   - `encRuleTrans : Fun2` (combine two encoded Derivs using `case1`'s shape).
   - `encRuleSym : Fun1` (flip an encoded Deriv using `case2`).
   - `encCongL / encCongR : Fun2` (congruence, using `case3..`).
   - `encRuleInst : Fun1 → Fun1` built via `substOp` + proof-code rewrapping (the hard one; needs `case23V3`).
   - Each comes with a **correctness lemma** proving `thmT trivCT (encXXX a b) = expected code` under the hypothesis that the inputs are themselves correct encodings. These lemmas mirror `ndDispNN` cases in `Thm14EV3.agda`.

2. **`Guard/EncTreeEqSelf.agda`** — a closed Term `encSelfEq` such that `thmT trivCT encSelfEq = codeEqn (eqn (ap2 TreeEq c c) O)` for a specific target `c`. Use `treeEqSelf`'s structure (it's just `axEq` + `treeEqSelfBool` applied at a parameter). The parameter `c` can be supplied as part of the Term (reified). No induction — finite composition.

3. **`Guard/EncDiagFTargetCR.agda`** — a closed Term `encDiagFTargetCR` encoding the entire `diagFTargetCR` derivation. Heavy rewriting chain (~130 lines of Agda), but mechanical.

4. **`Guard/EncGodelIClassical.agda`** — the main construction.
   - `Phi : Fun1` such that on input `v0 = enc` where `enc` encodes some Triv-derivation of `gsCR`, `ap1 Phi v0` returns a new proof encoding. Built compositionally from the encoders in step 1.
   - Key lemma **`phiCorr`**:
     ```agda
     phiCorr : {hyp : Equation} (v0 : Term) ->
       Deriv hyp (eqn (ap1 (thmT trivCT) v0) (reify cGSCR)) ->
       Deriv hyp (eqn (ap1 (thmT trivCT) (ap1 Phi v0)) codeBotT)
     ```
     This is **not** a record-style DC2 — it takes a Deriv hypothesis polymorphically. That is the cleanest formulation in our setup.

5. **`Guard/GodelIIClassical.agda`** — the final two theorems.
   ```agda
   godelIIClassical       : Deriv Triv ConTriv -> Deriv Triv (eqn trueT falseT)
   godelIIClassicalContra : Consistent Triv    -> Deriv Triv ConTriv -> Empty
   ```
   Proof sketch for `godelIIClassical`:
   - From `godelIClassical` + contrapositive: assuming `ConTriv`, for every `v0`, `thmT trivCT v0 ≠ ⌜gsCR⌝` — i.e. Triv ⊢ gsCR.
     - This step is the **crux**. It requires `phiCorr` run contrapositively (in the equational form: if `thmT trivCT (Phi v0) = ⌜⊥⌝` is impossible by `ConTriv`, then `thmT trivCT v0 = ⌜gsCR⌝` is impossible) — but our setting has no negation / modus tollens inside Deriv, so we must derive the equation `TreeEq(thmT trivCT v0, ⌜gsCR⌝) = falseT` directly, by an equational argument on `phiCorr`'s output.
     - Concrete shape: the bridge equation
       ```
       Deriv hyp (eqn (TreeEq (thmT trivCT v0) (reify cGSCR))
                      (TreeEq (thmT trivCT (ap1 Phi v0)) codeBotT))
       ```
       is the load-bearing equational reflection of `phiCorr`. Once this is derivable (it follows from `phiCorr` by `congR`/`congL TreeEq`), combining with `ConTriv` specialised at `Phi v0` — which gives `TreeEq(..., codeBotT) = falseT` — yields, by `ruleTrans`, `gsCR`.
   - Then apply `godelIClassical` to get `Deriv Triv (eqn trueT falseT)`.

Do NOT assume the bridge equation holds without a proof term. It requires exhibiting a Deriv that equates two `TreeEq`s by congruence over the equation `phiCorr` provides — this is where the "polymorphic in hyp" shape of `phiCorr` is used.

## Step-by-step opening

1. **Read** `Guard/GodelIClassical.agda` and `Guard/SubstTForPrecompClassical.agda` in full; they are short (~200 lines each) and hold the target types.
2. **Read** `Guard/Thm14EV3.agda` top-to-bottom (skim section markers; focus on `ndDisp01V3`..`ndDisp23V3` and the `case*V3` definitions in `ThFunTForV3.agda`). These set the encoding convention for each Deriv constructor.
3. **Create `Guard/ProofEnc.agda`** first. Start with `encRuleSym` (simplest): a closed Fun1 that wraps a proof encoding with the `n2` tag. Prove its correctness via `case2V3Match`. Target compile time ≤10s.
4. **Then `encRuleTrans`** — uses `n1` tag and `case19V3`. Test the pattern.
5. **Then `encCongL`, `encCongR`** — `n3`/`n4` tags.
6. **Then `encRuleInst`** — the hardest of the primitives. Uses `n23` + `substOp`. Pattern similar to `ndDisp23V3` in `Thm14EV3.agda`.
7. Build `encSelfEq`, `encDiagFTargetCR`, `Phi` on top. Each is a finite composition.
8. Prove `phiCorr` by composing the correctness lemmas.
9. Finally build `godelIIClassical` using the bridge argument above.

## Must-have invariants

- **No postulates. No holes.** If something cannot be closed, stop and write a session doc.
- **Every file compiles under 10s** via abstract blocks and fused lemmas (follow `SubstTForPrecompV3`'s `fullyInstGS` pattern).
- **Use `~/.cabal/bin/agda-2.9.0`**, not `/opt/homebrew/bin/agda`.
- **No new Term/Step primitives.** `RecP` is sufficient; everything else can be built.
- **Stay syntactic.** No semantic arguments, no "true but unprovable" reasoning — only Deriv.

## Sanity check at the start

```
~/.cabal/bin/agda-2.9.0 Guard/GodelIClassical.agda
```
Should succeed in under 10s with no output. If it does not, something has regressed and you should stop and investigate before starting new work.

## Fallback options if Phi is too large

If after 2 sessions `Phi` is clearly going to exceed 3000 lines:
- **Option A**: Factor out a `Guard.ProofCombinators` file with generic `encDeriv` builders indexed by tag, reducing duplication.
- **Option B**: Prove `phiCorr` as a polymorphic `{hyp}` Deriv rather than as a closed Term-level function (weakens `Phi` from "closed Fun1" to "Deriv-family"). This still proves Gödel II but sacrifices the "fully internalised" reading. Document the trade-off and ask.
- **Option C** (not recommended): a Löb-style variant using DC3 could shorten things but requires proving DC3 (another ~1000 lines).

Preferred order: A then B. Do not take C without explicit go-ahead.

## Files expected to be created

```
Guard/ProofEnc.agda             (~600 lines)
Guard/EncTreeEqSelf.agda        (~150 lines)
Guard/EncDiagFTargetCR.agda     (~400 lines)
Guard/EncGodelIClassical.agda   (~800 lines)
Guard/GodelIIClassical.agda     (~200 lines)
```

Total ~2150 lines of new Agda. Update `Guard/guard-godelII-complete.tex` with a final section once done.
