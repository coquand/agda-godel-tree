# Ryan Main Theorem — Paper Trace

Source: Ryan.pdf (3 pages). Rose.pdf not consulted — contains a
mistake per user instruction; only use Ryan as the primary reference.

## Ryan's ingredients (complete list)

### §1 PR machinery (pp.457-458)

| Ryan | Guard analogue |
|---|---|
| `var(x)` — Gödel-number-of-variable predicate | tree-shape check `nd tagVar _` |
| `k_n` — numeral's Gödel number | `natCode n` / `reify (natCode n)` |
| `η(n, i)` — enumerate n-place function constants | `codeF1` / `codeF2` |
| `ℰ-term(x)` | `code` / structural checks |
| `θ_1(x), θ_2(x)` — LHS/RHS extraction | `axFst` / `axSnd` on `codeEqn` nodes |
| `Sub(x, t, e)` — substitution at coded level | `substOp` |
| `sub(x, n, e) = Sub(x, "k_n", e)` | `substOp` specialised |
| `Ax(n)` — enumerate axioms | implicit via encoders in `Thm14EV3.agda` |
| `th(y)` — theorem enumerator (5-case definition) | **`thmT trivCT`** (`Guard/ThFunTForV3.agda`) |
| `ε(x)` — e-negation toggle | **`eT`** + `eTCorrect` (`Guard/RoseEFun.agda`) |
| `→` (arithmetic implication) | **`impT`** (`Guard/ImpT.agda`) |
| `≠` (arithmetic inequality) | `TreeEq` yielding `poo = Pair O O` |
| `{f(X_n) = x_0}` (Gödel number) | `reify (codeEqn (eqn ... ...))` |

### §2 The four theorems

**Lemma 1** (n general). If `E_1, ..., E_n ⊢ E_{n+1}` in ℰ^rec_E,
there exists a PR `V(X_n)` such that
`⊢ th(x_1) = "E_1" → [... → [th(x_n) = "E_n" → th(V(X_n)) = "E_{n+1}"] ...]`.

- *Our version at n=1:* `roseLemma1T` (`Guard/RoseLemma1T.agda`) —
  packaged as a `Lemma1T` record with `vCorr` conditional on `tCorr`.
- *At n>1:* not implemented; not needed per Ryan's actual chain.

**Lemma 2.** For each n-place PR `f`, there exists PR `p_f(X_n, x_0)`
with `⊢_ℰ f(X_n) = x_0 → th(p_f(X_n, x_0)) = {f(X_n) = x_0}`.

- *Our version:* `thm14EV3` (`Guard/Thm14EV3.agda`) subsumes it —
  encodes ANY Deriv, not just PR-evaluations. `corr` is the
  equational content: `thmT hCode enc = reify (codeEqn B)`.
- Bridge from "under Triv" to "under trivCT":
  `corrPf` pattern in `Guard/GodelIClassical.agda` lines 148-154.

**Lemma 3** (Gödel I). Let `N = "sub('x_0', x_0, x_0) ≠ th(x_1)"`.
Then `⊢ sub('x_0', k_N, k_N) = "sub('x_0', k_N, k_N) ≠ th(x_1)"`,
and if consistent, `sub('x_0', k_N, k_N) ≠ th(x_1)` is true but not
provable.

- *Our version:* `godelIClassical`
  (`Guard/GodelIClassical.agda`). The diagonal identity
  `sub('x_0', k_N, k_N) = "G"` becomes `diagFTargetCR : rhsT =
  reify cGSCR`.

**Main Theorem** (Gödel II). If ℰ^rec_E is consistent, then
`th(x_0) ≠ ε(th(x_1))` is not a theorem.

- *Our goal:* `godelIIClassicalTrivStrong`.

## What Ryan does NOT list

- NO explicit reflection rule `|a-b|=0 → a=b` or `TreeEq A B = O →
  A = B` as an axiom. Rose's PRA derives the numerical version from
  induction on numerals; Ryan's general-recursive setting presumably
  derives its analogue from its own induction principles. Since Ryan
  doesn't list it as a primitive, we shouldn't add it as one either.

- NO proof of the Main Theorem — Ryan says "parallel the proofs in
  ROSE [4, 5]". Per user instruction, Rose.pdf has a mistake and is
  not to be consulted. So the chain must be reconstructed from
  Ryan's four ingredients directly.

## Chain reconstruction from Ryan's ingredients

Target: `dConStrong : ⊢ th(x_0) ≠ ε(th(x_1))` + consistent ⇒ contradiction.

Sketch (proof of Main Theorem, reconstructed):

1. **Lemma 3 / diagonal:** `⊢ sub('x_0', k_N, k_N) = "G"` where
   `G = "sub('x_0', k_N, k_N) ≠ th(x_1)"`.

2. **Lemma 2 applied to step 1's equation** (f = sub, X_n = (k_N, k_N),
   x_0 = "G"): there exists a proof-code `P_{diag}` with
   `⊢ th(P_{diag}) = "sub('x_0', k_N, k_N) = "G""`.

3. **dConStrong** instantiated at `(x_0, x_1) := (z, P_{diag})`:
   `⊢ th(z) ≠ ε(th(P_{diag}))` for any z.

4. **ε applied to step 2's equation:**
   `ε(th(P_{diag})) = ε("sub('x_0', k_N, k_N) = "G"")`
                   `= "sub('x_0', k_N, k_N) ≠ "G""`.
   So step 3 becomes `⊢ th(z) ≠ "sub('x_0', k_N, k_N) ≠ "G""` for any z.

5. **Lemma 1** applied to the derivation `⊢ G` (if G is provable;
   this is the reductio-assumption): V with
   `⊢ th(V) = "G" = "sub('x_0', k_N, k_N) ≠ th(x_1)"`.

6. **Substitute z := V** in step 4:
   `⊢ th(V) ≠ "sub('x_0', k_N, k_N) ≠ "G""`.
   Combined with step 5:
   `"sub('x_0', k_N, k_N) ≠ th(x_1)" ≠ "sub('x_0', k_N, k_N) ≠ "G""`.

7. Specialize step 6 at `x_1 := V_{at_G}` (some specific witness of
   "th equals G") to produce the actual contradiction with Lemma 3's
   diagonal.

8. Close by reductio: the reductio-assumption (G is provable) was
   forced by assuming dConStrong is a theorem + Lemma 3 (G is true).

## Status

Paper trace complete. Chain reconstruction is sketched but not fully
formalised — step 6-7 need precise Term-level instantiations and
specific roseLemma1T + thm14EV3 compositions.

The key technical issue: making step 7's "specialize x_1 := V_{at_G}"
actually compose with the forms produced by `roseLemma1T` and
`thm14EV3` — i.e., threading `tCorr` / `corr` equations through the
chain in a way that yields a `Deriv Triv (O = poo)` (bot) or a
`Deriv Triv gsCR` (then closed by `godelIClassical`).

**Specific missing piece identified:** none as an axiom. All the
structural pieces exist. The chain is a matter of finding the correct
instantiations and compositions.
