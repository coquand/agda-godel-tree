# Next Session: Classical Gödel II

## Setup

```
cd /Users/coquand/CHWISTEK
~/.cabal/bin/agda-2.9.0 <file>     # use THIS binary, not /opt/homebrew/bin/agda
```

Repo: `https://github.com/coquand/agda-godel-tree.git`, branch `main`.
Last commit: `e17eb10` `[proofenc] Add encRuleInst (n23) combinator`.
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

## Progress made on classical Gödel II (April 2026 session)

Commit range `9856d71..e17eb10` — `Guard/ProofEnc.agda` (564 lines, compiles in 0.23s):

Five proof-encoding combinators built. Each takes Term-level sub-encodings
and a polymorphic Deriv correctness assumption, producing a new Term +
polymorphic correctness lemma + tag-opaque pass property.

| Combinator       | Tag | Mirrors            | Purpose                               |
|------------------|-----|--------------------|---------------------------------------|
| `encRuleSym`     | n18 | `thm14EV3Sym`      | wrap sub-proof as Sym                 |
| `encRuleTrans`   | n19 | `thm14EV3Trans`    | compose two sub-proofs as Trans       |
| `encCongL`       | n21 | `thm14EV3CongL`    | congL g x wrap of sub-proof           |
| `encCongR`       | n22 | `thm14EV3CongR`    | congR g x wrap of sub-proof           |
| `encRuleInst`    | n23 | `thm14EV3Inst`     | instantiate sub-proof at (t, x)       |

All five:
- Take sub-proof as `Pair paR pbR` (standard proof-encoding shape).
- Take correctness `Deriv hyp (eqn (thmT hCode (Pair paR pbR)) (Pair lC rC))`.
- For congL/R/Inst: take dispMiss as a parameter (avoids pulling in the
  private `f2xDispMissV3`/`aRPassV3` helpers from `Thm14EV3.agda`).
- Yield a polymorphic Deriv of the combined encoding's evaluation.
- Expose a `*Pass` tag-opacity property via `ndDispatchV3PairMiss`.

`ndDisp18V3Pub`, `ndDisp19V3Pub`, `ndDisp21V3Pub`, `ndDisp22V3Pub`,
`ndDisp23V3Pub` are publicly accessible copies of the private navigation
helpers in `Thm14EV3.agda`.

**No postulates, no holes, compiles clean under `--safe --without-K --exact-split`.**

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
All of these steps have explicit **proof-code** formulations under our tag scheme (tags `n0..n28` in `ThFunTForForV3.agda`). `Phi` must emit the composite encoding.

## Scope estimate

**Size**: ~1500–2500 new Agda lines, comparable to `Thm14EV3.agda` (2448). The core work is packaging each Agda-level derivation step as a closed tree-builder and proving, by `Rec`/`RecP` induction, that `thmT trivCT` on the builder's output yields the correct encoded equation.

**Sessions**: 3–5 (one session complete — ~25% progress, covering the 5 primitive combinators).

## Remaining work (in order)

1. **Axiom encoders** in `Guard/ProofEnc.agda` (~400 lines): `encAxI` (n0), `encAxFst` (n1), `encAxSnd` (n2), `encAxComp2` (n5), `encAxKT` (n25), `encAxTreeEqLL` (n13), `encAxTreeEqNN` (n16), `encAxPost` (n7), `encAxLift` (n6) — closed (no sub-proofs) Term builders.
   Each mirrors a `thm14EV3Ax*` case from `Thm14EV3.agda`.
   Most are direct: encode the axiom tag n_k with the reified parameters as body; correctness uses the matching `ndDispNNV3Pub` + `mkEqFRed`/`mkAp1FRed`/`mkAp2FRed` chain.
   `encAxKT` uses n25 (currently no `ndDisp25V3Pub` published — needs to be added).

2. **Schema F encoder** in `Guard/ProofEnc.agda` (~200 lines): `encRuleF` (n24). Takes 4 sub-proofs. Mirrors `thm14EV3F`. Requires a new `ndDisp24V3Pub` publication and the `f1gDispMissV3` helper (private in `Thm14EV3.agda`).

3. **`Guard/EncTreeEqSelf.agda`** (~150 lines): closed Term `encSelfEq` for `thmT trivCT encSelfEq = codeEqn (eqn (TreeEq c c) O)` at a specific `c`. Uses the axiom encoders + `encRuleF` + `encRuleInst`. The target `c = reify cGSCR` in our use.

4. **`Guard/EncDiagFTargetCR.agda`** (~400 lines): encode the `diagFTargetCR` derivation. Mechanical — applies encCongL/R, encRuleTrans, encRuleSym and axiom encoders in the same pattern as the Agda-level proof in `Guard/GodelIClassical.agda`.

5. **`Guard/EncGodelIClassical.agda`** (~800 lines):
   - `Phi : Term -> Term` (a closed meta-function on Terms, potentially also as `Fun1` via `Comp2 Pair ...` compositions). On input `v0` = encoded `d : Deriv Triv gsCR`, returns the encoded Deriv of `eqn trueT falseT`.
   - `phiCorr` — the DC2 bridge at the polymorphic `{hyp}` Deriv level (Option B fallback). This is the deviation the user specified: "replace object-language → with meta-level `Deriv hyp → Deriv hyp`".

6. **`Guard/GodelIIClassical.agda`** (~200 lines):
   - From `d : Deriv Triv ConTriv`, derive `Deriv Triv (eqn trueT falseT)`.
   - Strategy: the meta-level `phiCorr` is NOT a Deriv; it's a function `Deriv hyp A → Deriv hyp B`. The bridge equation ⦃Deriv hyp (eqn (TreeEq (thmT trivCT v0) cGSCR) (TreeEq (thmT trivCT (Phi v0)) codeBotT))⦄ does NOT follow from `phiCorr` alone (both sides can be unconditional).
   - **Open question**: how to derive `Deriv Triv gsCR` from `Deriv Triv ConTriv` given only meta-level `phiCorr`.
     - Option A: give up on one-free-variable form, switch to a Löb-style sentence that has internal implication. This changes gsCR's definition.
     - Option B: give an EXISTENCE witness — show that a specific encoded proof (built from an assumed `Deriv Triv ConTriv`) decodes to ⊥'s code. This still requires a bridge.
     - Option C: prove `Deriv Triv (eqn (TreeEq (thmT trivCT (Phi (var zero))) codeBotT) (TreeEq (thmT trivCT (var zero)) (reify cGSCR)))` via Schema F or induction over all v_0. Not clear this is derivable.

## Proposed file layout (updated)

1. **`Guard/ProofEnc.agda`** (currently 564 lines, target ~1200 after axioms + ruleF). [25% done]

2. **`Guard/EncTreeEqSelf.agda`** (~150 lines). [Not started]

3. **`Guard/EncDiagFTargetCR.agda`** (~400 lines). [Not started]

4. **`Guard/EncGodelIClassical.agda`** (~800 lines). [Not started]

5. **`Guard/GodelIIClassical.agda`** (~200 lines). [Not started; blocked on architectural decision above]

## Must-have invariants (unchanged)

- **No postulates. No holes.** If something cannot be closed, stop and write a session doc.
- **Every file compiles under 10s** via abstract blocks and fused lemmas.
- **Use `~/.cabal/bin/agda-2.9.0`**, not `/opt/homebrew/bin/agda`.
- **No new Term/Step primitives.** `RecP` is sufficient; everything else can be built.
- **Stay syntactic.** No semantic arguments, no "true but unprovable" reasoning — only Deriv.

## Sanity check at the start of the next session

```
~/.cabal/bin/agda-2.9.0 Guard/ProofEnc.agda
~/.cabal/bin/agda-2.9.0 Guard/GodelIClassical.agda
```

Both should succeed in under 1s with no output.

## Open architectural question for user

The NEXT-SESSION doc's "bridge equation" claim:
> "it follows from `phiCorr` by `congR`/`congL TreeEq`"

But `phiCorr` (in the Option B / user's deviation formulation) is a meta-level function type, not a Deriv. `congR` takes a Deriv, not a function. So the bridge can't "follow" from `phiCorr` by congR directly.

**Need user input** on whether to:
- (a) formulate `phiCorr` as a Deriv rather than a meta-function (object-language ⇒ on encoded proofs — which is a specific schema relation we'd have to express via IfLf on encoded equations);
- (b) change the proof strategy of `godelIIClassical` so it doesn't need the bridge equation (e.g., use Schema F-induction over all v_0);
- (c) weaken the goal — e.g., prove `godelIIClassicalContra` directly at the meta level without building `Deriv Triv gsCR`.

**Recommendation from this session**: option (c). Under option (c), `godelIIClassicalContra con d` does the following meta-level argument:
- Suppose (for contradiction) `con : Consistent Triv` and `d : Deriv Triv ConTriv`.
- Build encT-style encoding `enc_d = encT (thm14EV3 d)` : closed Term.
- Instantiate `d` at `var zero := reify (code enc_d)` (or similar) to get a specific Deriv equation.
- ... still needs a bridge to ⊥. ???

Option (c) also doesn't trivially work. This deserves a dedicated design session.
