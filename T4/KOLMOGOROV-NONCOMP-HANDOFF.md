# Handoff: finish #4 — non-computability of Kolmogorov complexity (the Berry program)

## 0. One-paragraph summary

A small **Kolmogorov-complexity library** was built on top of the existing BRA3/T4
universal-machine + Chaitin infrastructure. The **upper bound** `K(x) ≤ log₃ x + O(1)`,
the **counting bound** `#{x : K(x) ≤ L} ≤ 3^{L+1}`, **incompressible numbers exist**,
**`K` unbounded**, **abundance**, and the **non-computability CLASH CORE** are all done
(green, no holes/postulates). The one piece left is the **runnable Berry search program**
that turns the clash core into the full non-computability headline. This document is the
spec for that build.

All code is committed to branch `kritchman-raz-spikeB`. Everything compiles with
`agda T4/<file>.agda` (OPTIONS `--safe --without-K --exact-split` on every file).

---

## 1. What exists (reuse these — do NOT rebuild)

### The KC library (all green, no holes/postulates)

| File | Key exports |
|---|---|
| `T4/KolmHorner.agda` | `DL` (digit list), `horner : DL → Fun1`, `hVal : DL → Nat`, `horner_correct : Deriv (eqF (ap1 (horner ds) O) (natCode (hVal ds)))`, `addD`, `threeT` |
| `T4/KolmDigits.agda` | `digits3 : Nat → DL`, `digits3_correct : Eq (hVal (digits3 x)) x`, `div3`, `mod3`, `euclid3`, `div3_suc_le`, `digitsFuel` |
| `T4/KolmRun.agda` | `Sg`/`mkSg`/`Pr`/`pr`, `Describes p N x = Deriv (eqF (ap2 runProgN (natCode p) (natCode N)) (ap1 s (natCode x)))`, `kolmRun : (x) → Sg p. Pr (p < 3^(nodes(...)+1)) (Sg N. Describes p N x)` |
| `T4/KolmSize.agda` | `lenDL`, `AllLt3`, `baseN`, `PDmax`, `repAdd`, `nodes_horner_bound : AllLt3 ds → NatLe (nodes (mcode1 (horner ds))) (addN baseN (repAdd PDmax (lenDL ds)))`, `le_addN_1st/2nd`, `gnodes`, `gnodes_eq` (the refl decomposition of `nodes(mcode1(compose1U f P))`) |
| `T4/KolmLog.agda` | `kolmLog`, `pow3_ge1`, `pow3_mono : NatLe a b → NatLe (pow3 a)(pow3 b)`, `threeT_mono`, `digit_log : 1≤x → NatLe (pow3 (pr0 (lenDL (digits3 x)))) x`, `allLt3_digits3 : AllLt3 (digits3 x)` |
| `T4/KolmNumReflect.agda` | `Sg`/`mkSg`, `numEqToFalse : (a b) → Not (Eq a b) → Deriv (eqF (natCode a)(natCode b)) → Deriv falseF` |
| `T4/KolmCount.agda` | `And`/`and`/`p1`/`p2`, `Kle L x = Sg p. And (Lt p (pow3 (suc L))) (Sg N. Describes-style Deriv)`, `valEq` (determinism+con), `pos_to_suc`, `countingBound` |
| `T4/KolmIncompress.agda` | `incompressible : con → (L) → ¬ (∀ i ≤ 3^(L+1), Kle L i)`, `kUnbounded` |
| `T4/KolmAbundance.agda` | `compressibleBounded`, `blockHasIncompressible` |
| `T4/KolmMono.agda` | `kle_mono : (a b x) → Kle a x → NatLe a b → Kle b x`, `ltLeTrans : Lt p K1 → NatLe K1 K2 → Lt p K2` |
| `T4/KolmNonComp.agda` | **`nonComputable_clash`** (see §3), `KSound` |

### Underlying machine infrastructure (reuse)

- `T4/EvalUCorrect.agda`:
  - `evalN1 : Fun1 → Nat → Nat`, `evalN2 : Fun2 → Nat → Nat → Nat` — the **meta reference
    semantics**. Equations:
    ```
    evalN1 s n = suc n;  evalN1 o n = zero;  evalN1 u n = n
    evalN1 (C g h1 h2) n = evalN2 g (evalN1 h1 n) (evalN1 h2 n)
    evalN2 v x y = y
    evalN2 (R g h1 h2) x zero    = evalN1 g x
    evalN2 (R g h1 h2) x (suc y) = evalN2 h1 (evalN2 h2 x y) (evalN2 (R g h1 h2) x y)
    ```
  - `evalN1_sound : (f n) → Deriv (eqF (natCode (evalN1 f n)) (ap1 f (natCode n)))`
  - `record EvalsTo (e out)` { `fuel : Nat`, `ev : Deriv (eqF (ap2 evalU e (natCode fuel)) out)` }
  - **`evalU_correct_num : (f : Fun1) → EvalsTo (mcode1 f) (ap1 s (natCode (evalN1 f zero)))`**
    — THE bridge: any μ-free Fun1's code runs (some fuel) to `s (natCode (evalN1 f 0))`.
    ⚠️ This is for the **μ-free** fragment only (s/o/u/C/v/R). Keep the Berry program μ-free.
- `T4/EvalU.agda`: `mcode1 : Fun1 → Term`, `mcode2 : Fun2 → Term`.
- `T4/McodeInAlph.agda`: `inAlph_mcode1 : (f) → InAlph (mcode1 f)`.
- `T4/ParseN.agda`: `runProgN`, `diagRank gL = rank (treeToDigits gL)`,
  `runProgN_at_diag : (gL) → InAlph gL → (y) → Deriv (eqF (ap2 runProgN (natCode (diagRank gL)) y) (ap2 evalU gL y))`.
- `T4/TreeDigitsSize.agda`: `pow3 : Nat → Nat` (`pow3 (suc k) = m3 (pow3 k) = 3·pow3 k`),
  `n0_lt_pow3 : (t) → NatLe (suc (rank (treeToDigits t))) (pow3 (suc (nodes t)))`,
  `m3`, `m3_suc`.
- `T4/Exp3.agda`: `exp3 : Fun1` with `exp3_natCode : (k) → Deriv (eqF (ap1 exp3 (natCode k)) (natCode (pow3 k)))`;
  `triple_F1 : Fun1` (×3) with `triple_F1_natCode`.
- `T4/ProgEnc.agda`: `nodes : Term → Nat` (`nodes O = 1`, `nodes (ap1 f t) = suc (nodes t)`,
  `nodes (ap2 g a b) = suc (addN (nodes a)(nodes b))`).
- `BRA3/Fan.agda`: `compose1U : Fun1 → Fun1 → Fun1` (`= C (Lift1 f) g u`),
  `compose1U_eq : ap1 (compose1U f g) x = ap1 f (ap1 g x)`.
- `BRA3/Numerals.agda`: `sigma_natCode : (x y) → Deriv (eqF (ap2 sigma (natCode x)(natCode y))(natCode (addN x y)))`,
  `substT_natCode`.
- `BRA3/Dispatch.agda`: `constN : Nat → Fun1` with `constN_eq`, `eqAtT`, `eqAtT_match`, `eqAtT_above`.
- `T4/RunProgMonoN.agda`: `runProgMonoPlusN : (p val L g) → Deriv (runProgN p L = s val) → Deriv (runProgN p (sigma L g) = s val)` (run is monotone in fuel).
- **Bounded search already present** (object-level, maybe reusable for the spec/structure):
  - `T4/FirstHit.agda`: a least-number search recursor `gRec : Fun2` with `least_first`/`least_hit`
    (for `p : Fun1`, `p ≤ 1`, witness `B` with `p B = s O`).
  - `T4/ExistsHit.agda`: bounded-exists indicator (PR `Fun2`, like `SpikeChaitin.lastPosRec`).
- `T4/SurpriseG2/MetaPigeonhole.agda`: `Lt`/`ltZ`/`ltS`/`ltSelf`/`ltIrrefl`/`ltTrans`,
  `NatCmp`/`ltC`/`eqC`/`gtC`/`natCmp`, `Collide`, `pigeonhole`, `natDecEq`, `sucInj`.
  (NOTE: this `Lt` is the program-bound order used by `Kle`; `BRA3.RuleInst2.NatLe` is the
  other order. `ltLeTrans` in `KolmMono` bridges them.)
- `con` (simple consistency) is the only hypothesis used by the lower-bound results:
  `Not (Deriv falseF)` where `falseF = eqF O (ap1 s O)` (`T4/Code.agda`).

### GOTCHAS already hit (avoid re-discovering)

- `v` and `u` are `Fun2`/`Fun1` constructors — **never name a Nat/Term variable `v`, `u`,
  `o`, `s`, `C`, `R`**; Agda reads them as constructors in patterns (`[ConstructorPatternInWrongDatatype]`).
  Use `vv`, `uu`, etc.
- Parametrized **top-level** module telescopes can't reference imported types
  (`module M (Kf : Fun1)` fails: `Fun1` not in scope). Pass such params as ordinary
  arguments to each definition instead.
- Record field projections are NOT auto-exported; use `Sg.fst`, `And.p1`, `Collide.i_idx`
  qualified, or `open` the record.
- `eqF a b = atomic (eqn a b)` and `falseF = eqF O (ap1 s O)` definitionally; `natCode (suc n)
  = ap1 s (natCode n)` and `natCode zero = O` definitionally.
- `nodes (mcode1 (compose1U f P))` **reduces by `refl`** (structural) with `f`,`P` abstract —
  this is why `KolmSize.gnodes_eq` works; reuse that pattern for the Berry program's size.

---

## 2. The goal (the only thing left)

Prove **non-computability of `K`**: there is no total `Kf : Fun1` computing exact
Kolmogorov complexity. The CLASH CORE is already done (§3); you must **feed it** by
constructing, from a hypothesised computing `Kf`, the Berry witness `(bL, M)` for some `L`.

Final headline to produce (suggested shape — adapt as the build dictates):

```agda
-- "Kf computes K":  Kf is sound AND complete for the Kle predicate.
KComputes : Fun1 → Set
KComputes Kf =
  ( (L x : Nat) → Kle L x → NatLe (evalN1 Kf x) L )          -- sound  (KSound)
  × ( (L x : Nat) → ¬ Kle L x → Lt L (evalN1 Kf x) )          -- complete
  × ( (L x : Nat) → NatLe (evalN1 Kf x) L → Kle L x )          -- realizes: Kf x ≤ L ⇒ describable at L

nonComputable :
  Not (Deriv falseF) → (Kf : Fun1) → KComputes Kf → Empty
```

(The three clauses are the honest content of "Kf computes K"; the third is what lets the
bounded search constructively succeed — see §4 step B.)

---

## 3. The clash core (DONE — `T4/KolmNonComp.agda`)

```agda
KSound : Fun1 → Set
KSound Kf = (L x : Nat) → Kle L x → NatLe (evalN1 Kf x) L

nonComputable_clash :
  (Kf : Fun1) → KSound Kf →
  (L M bL : Nat) → NatLe M L → Lt L (evalN1 Kf bL) → Kle M bL → Empty
nonComputable_clash Kf kfSound L M bL leML ltLkf kleMbL =
  ltIrrefl (ltLeTrans ltLkf (kfSound L bL (kle_mono M L bL kleMbL leML)))
```

So once you produce, for a suitable `L`: `bL`, `M ≤ L`, `Lt L (evalN1 Kf bL)`, and
`Kle M bL`, you call `nonComputable_clash` and you're done.

---

## 4. The remaining bricks (the actual work)

Let `kf x := evalN1 Kf x`. Fix `L`. Let `B := pow3 (suc L) = 3^(L+1)`.

### Brick A — the Berry function as a fixed μ-free `Fun1`

Build a **fixed** `Fun1` `BerryF : Fun1` (independent of `L`) such that
`evalN1 BerryF L = bfun L`, where `bfun L = the least x < B with kf x > L` (or `0`/`B`
if none). Structure:

```
BerryF  =  bounded-search over x ∈ [0, exp3(L+1))  for  ( gt (Kf x) L )
```

- Use `exp3` (`T4/Exp3.agda`) to compute the bound `B` from the input `L`.
- Use a **bounded minimisation** combinator built from `R` (primitive recursion → μ-free,
  so `evalU_correct_num` applies). EITHER hand-build it and prove its `evalN`-correctness by
  induction on the bound, OR adapt `FirstHit.gRec` / `ExistsHit.existsHitRec` (object-level;
  you'd need the `evalN`-level spec, so a fresh meta build may be cleaner).
- `gt : Fun2` ("`a > b`") from the existing `leq`/`sub`/`isZero` machinery (`BRA3.Church`,
  `BRA3.Dispatch.eqAtT`-style).
- The predicate is `q_L(x) = gt (Kf x) L`, i.e. a `Fun2` in `(x, L)`; `Kf` enters here as a
  fixed sub-`Fun1`.

**Deliverable:** `evalN1 BerryF L = bfun L`, plus the meta lemmas
- `bfun_lt_B : bfun L < B`  (it returns an index in range — needs the search to succeed),
- `bfun_hit  : Lt L (kf (bfun L))`  (the found index really has `kf > L`).

### Brick B — the search succeeds (uses `incompressible` + completeness + realizes)

The bounded search succeeds because **some** `x < B` has `kf x > L`. Prove it by ruling out
"none":
- Decidable bounded search gives `Or (least hit) (∀ x < B, ¬(kf x > L))`.
- In the "none" branch: `∀ x < B, kf x ≤ L`. By the **realizes** clause
  (`kf x ≤ L → Kle L x`): `∀ x < B, Kle L x`, i.e. `∀ i ≤ N0 (= B-1), Kle L i`,
  contradicting `KolmIncompress.incompressible con L`. So "none" is impossible ⇒ the hit
  branch holds. This yields `bfun_hit` and `bfun_lt_B` constructively.

(`incompressible` is negative-form `¬ ∀`, which is exactly enough to close the decidable
"none" branch.)

### Brick C — the runnable program of size O(log L), describing `bL := bfun L`

```
berry L  :=  compose1U BerryF (horner (digits3 L))         -- a closed Fun1
```

- `evalN1 (berry L) O = evalN1 BerryF (evalN1 (horner (digits3 L)) O) = evalN1 BerryF L = bfun L`.
  (`evalN1` of `compose1U` = composition — prove a small `evalN1_compose1U` lemma, OR work at
  the object level via `compose1U_eq` + `evalN1_sound` exactly as `KolmRun` does.)
- **Run it** with `evalU_correct_num (berry L)` ⇒ `EvalsTo (mcode1 (berry L)) (ap1 s (natCode (evalN1 (berry L) zero)))`
  = `... (ap1 s (natCode bL))` after rewriting `evalN1 (berry L) zero = bfun L = bL`.
- **Lift to `runProgN`** exactly as `KolmRun` does: `runProgN_at_diag (mcode1 (berry L))
  (inAlph_mcode1 (berry L)) (natCode N)` gives a program number
  `p := diagRank (mcode1 (berry L))` with `Describes p N bL`.
- **Size:** `p < pow3 (suc (nodes (mcode1 (berry L))))` by `n0_lt_pow3`. Now bound
  `nodes (mcode1 (berry L))`:
  `mcode1 (berry L) = mcode1 (compose1U BerryF (horner (digits3 L)))`, and
  `nodes (mcode1 (compose1U f P))` reduces structurally (refl) to
  `gnodes f (nodes (mcode1 P))` (`KolmSize.gnodes` / `gnodes_eq`). So
  `nodes (mcode1 (berry L)) = const(BerryF) + nodes (mcode1 (horner (digits3 L)))`,
  and `nodes (mcode1 (horner (digits3 L))) ≤ baseN + PDmax · lenDL (digits3 L)`
  (`KolmSize.nodes_horner_bound` + `KolmLog.allLt3_digits3`). Hence
  `nodes (mcode1 (berry L)) ≤ c + d · lenDL (digits3 L)` with `c, d` concrete.
- Conclude **`Kle (M_L) bL`** with `M_L := nodes (mcode1 (berry L))` (package `p`, `N`,
  the `Describes`, and `p < pow3 (suc M_L)` into a `Kle`-style witness — note `Kle` wants
  `p < pow3 (suc M_L)`, which is exactly `n0_lt_pow3`).

### Brick D — exp-beats-linear: pick `L` with `M_L ≤ L`

`M_L ≤ c + d · lenDL (digits3 L)` and `lenDL (digits3 L) ≤ log₃ L + 1` (via `KolmLog.digit_log`:
`3^(D-1) ≤ L`). So `M_L ≤ c + d·(log₃ L + 1)`. Need one `L` with `M_L ≤ L`, i.e.
`c + d·(log₃ L + 1) ≤ L`. Cleanest: take `L := pow3 k` for `k` large; then
`lenDL (digits3 (pow3 k)) = k+1` (the base-3 length of `3^k`), so `M_L ≤ c + d·(k+1)`, and
`L = 3^k`; prove `c + d·(k+1) ≤ 3^k` for an explicit `k` (exp dominates linear — a finite
arithmetic lemma; pick `k` from `c, d`). This is the only genuinely new arithmetic; keep it
self-contained.

### Brick E — assemble

For that `L`: `bL = bfun L`, `Lt L (kf bL)` (= `bfun_hit`), `M_L ≤ L` (brick D),
`Kle M_L bL` (brick C). Feed `nonComputable_clash Kf (proj₁ KComputes) L M_L bL …`. Done.

---

## 5. Suggested file layout

- `T4/KolmBoundedSearch.agda` — bricks A + B: `BerryF`, `bfun`, `bfun_hit`, `bfun_lt_B`
  (this is the hard, ~150–250 line file; the `R`-based bounded-min + its `evalN` correctness).
- `T4/KolmBerry.agda` — brick C: `berry L`, `evalN1 (berry L) O = bfun L`, the run + size,
  `Kle M_L bL`. Heavily mirrors `T4/KolmRun.agda` + `T4/KolmSize.agda`.
- `T4/KolmExpLinear.agda` — brick D: the `c + d·(k+1) ≤ 3^k` lemma + the choice of `L`.
- `T4/KolmNonCompFull.agda` — brick E: `nonComputable : con → (Kf) → KComputes Kf → Empty`,
  via `nonComputable_clash`.

## 6. Risk notes / advice

- The **linchpin is brick A** (bounded-min `Fun1` + `evalN`-correctness). Build the meta
  `bfun` first and a matching `R`-combinator; prove `evalN1/evalN2` of it equals `bfun` by
  induction on the bound. If `FirstHit`/`ExistsHit` can be lifted to the `evalN` level cheaply,
  use them — but they are object/`Deriv`-level, so a fresh meta build is likely cleaner.
- Keep `berry L` **μ-free** (only s/o/u/C/v/R, `compose1U`, `R`-recursion, `exp3`, `Kf`) so
  `evalU_correct_num` applies. Do NOT use the `mu`/`tag_mu` machinery.
- Reuse the **object-level chain** in `T4/KolmRun.agda` verbatim for brick C (it already does
  `evalU_correct_num` → `evalN1_sound` → `runProgN_at_diag` → `n0_lt_pow3`).
- Discharge brick D's exp-beats-linear with a concrete `k` EARLY (it's the only place the
  proof could secretly fail to close); pick `k` as a closed function of the concrete `c, d`
  that come out of `nodes (mcode1 BerryF)` and `PDmax`.
- Every file: `{-# OPTIONS --safe --without-K --exact-split #-}`. No postulates, no holes
  (project rule — see `MEMORY.md` "no discharge-later parameters").
- Compile each file with `agda T4/<file>.agda`; the `RuleInst3.agda` `UnreachableClauses`
  warning is pre-existing and harmless.

## 7. Done-definition

`agda T4/KolmNonCompFull.agda` is green, no holes/postulates, and exports
`nonComputable : Not (Deriv falseF) → (Kf : Fun1) → KComputes Kf → Empty`
(or the agreed shape). That is #4 complete, and connects the KC library back to
incompleteness exactly as the upper bound / counting bound did for the rest of the theory.
