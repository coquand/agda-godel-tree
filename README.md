# Syntax-Native Incompleteness in Agda

A formalization of Goedel's incompleteness theorems using binary-tree syntax
instead of arithmetic coding, inspired by Chwistek's approach to formal
metamathematics.

**26 Agda files, ~6500 lines. No postulates, no standard library.**

## Key features

- **No arithmetization**: syntax is represented as binary trees (`Code`), not
  unary natural numbers. No Goedel numbering.
- **No postulates**: everything is proved from scratch, including soundness.
- **No standard library**: fully self-contained.
- **ASCII only**: no Unicode identifiers.
- **Finite self-reference**: the Goedel sentence refers to its own code via
  the classical quine trick (`csub`), avoiding infinite terms.
- **Two architectures compared**: stratified (Chwistek-style) vs fuel-based
  (Guard-style), with sharp separation theorems.

## Main results

### Goedel I (stratified, no assumptions)

```
goedel1-final : MetaNot (Proof GoedelSentence)
```

The Goedel sentence is not provable. No consistency assumption is needed.

### Constructive Goedel I (internal proof transformation)

```
constructive-goedel1 : ProofC GoedelSentence -> Code -> enc-correct -> ProofC fbot
```

From a proof of the Goedel sentence, construct a proof of fbot INSIDE the system.

### Goedel II for the SD-extended system

```
Con-implies-G : ProofSD n Con -> ProofSD n GoedelSentence
goedel2-SD    : ProofSD n Con -> EmptySD
```

Con is not provable in ProofSD (the system extended with `axSDrule`).
The proof uses the genuine Goedel-II chain: `Con-implies-G` derives
GoedelSentence from Con using the sentence-specific self-destruct
reflection axiom, then GoodSD soundness gives Empty.

This is Goedel II **relative to axSD**, not for the bare system.
`axSD` internalizes the constructive Goedel I transformation as
an axiom. See `ChwistekGodel2SD.agda`.

### Semantic unprovability of ConG (no extra axioms)

```
conG-unprovable-semantic : ProofG n ConG -> EmptyG2
```

ConG is unprovable in ProofG via the GoodG valuation.
This is a valid unprovability theorem but does NOT use self-reference,
the Goedel sentence, or an internal Con -> G derivation. It works
because GoodG trivializes all code equalities, making any formula
of the shape `fcAll (fimp (fceq ...) fbot)` false under the
interpretation.

### Goedel II via axSDruleG (self-referential, relative to axiom)

```
Con-implies-G    : ProofG2 n ConG -> ProofG2 n GoedelSentence
goedel2-via-axSD : ProofG2 n ConG -> EmptyG2
```

ConG is unprovable in ProofG2 (the system extended with `axSDruleG`).

This is Goedel II **relative to axSDruleG**, not for the bare system.
`axSDruleG` internalizes the constructive Goedel I transformation
("if code e proves G then self-destruct(e) proves fbot") as an axiom.
The internal derivation `Con-implies-G` composes this axiom with
instantiated consistency via Hilbert S/K combinators. The contradiction
follows from `soundGoodG2` under a valuation where `fceq -> Unit` and
`fbot -> Empty`.

The result isolates `axSDruleG` as the **precise missing ingredient**
for Goedel II: everything else (diagonalization, self-reference,
encoding correctness, fuel monotonicity, D1-D3) is derived. What
cannot be derived is the reflection step that turns a proof of G into
a proof of fbot internally. This is the classical Goedel II barrier:
the system cannot internalize its own soundness.

Additionally proved: fuel monotonicity for `checkG`/`evalG`
(`checkG-mono`, `evalG-mono`) and encoding correctness with
existential fuel (`encodeBaseG-fuel`).

See `ChwistekGodel2Genuine.agda`.

### Goedel II via template-closure (self-referential)

```
Con-implies-GTP  : ProofTP n ConGP -> ProofTP n GoedelSentenceP
goedel2-internal : ProofTP n ConGP -> EmptyG2
```

ConGP is unprovable in ProofTP. The proof goes through the full
self-referential chain: `Con-implies-GTP` derives `GoedelSentenceP`
from `ConGP` using the template-closure axiom, then `soundGoodTP`
gives `EmptyG2`.

The system ProofTP extends ProofG with:
- `FormulaP` / `CExpP`: formulas and code expressions with `cpair`
  (the code-level `cnode` constructor)
- `sdExp`: the self-destruct template expressed as a `CExpP`
  (`sdExp-clit-correct = refl`)
- `axSdExp` (template-closure): if `ccheck(e)` evaluates to `enc(G)`,
  then `ccheck(sdExp(e))` evaluates to `enc(fbot)`

`axSdExp` is the **only axiom** beyond ProofG. It is the exact
internal counterpart of `sd-meta-correct` (proved metatheoretically
in `SelfDestruct.agda` by finite template analysis, no induction).

See `Godel2Internal.agda`.

### Strict reflection hierarchy

```
evalCExp-blind-to-ax-eval : evalCExp (ccheck (clit (encodeProofExt (ax-eval e c eq)))) = nothing
no-self-reflect-ax-eval   : MetaNot (Sigma Code (\ d -> Eq (evalCExp ...) (just d)))
```

Each reflection layer can reason about the layer below but not about itself.
Chwistek's metasystem separation is structurally necessary.

### Fuel-based D1/D2/D3

```
represent-fuel : checkProofN (suc n) p = just A -> checkProofN (suc (suc (suc n))) q = just (fceq ...)
D3-fuel        : (iterated) self-reflection at +4 fuel per level
```

The fuel-based architecture collapses the hierarchy. All three Hilbert-Bernays
derivability conditions hold.

### Bounded Goedel I and II (meta-level)

```
goedel1-fuel  : ProofN GoedelSentence -> (enc-correct) -> Empty
goedel2-meta  : ProofN Con -> ProofN GoedelSentence -> (enc-correct) -> Empty
```

## Architecture comparison

| | Stratified | Fuel-based |
|---|---|---|
| Goedel I | Proved (no assumptions) | Proved (with enc-correct) |
| D1 (representability) | Base proofs only | All proofs |
| D3 (self-reflection) | **Blocked** (blind to tag 36) | **Works** (+4 fuel) |
| Hierarchy | Strict (proved) | Collapses |
| Goedel II | Impossible | Meta-level; relative to axSD |

## File structure

### Core development (Goedel I)

| File | Contents |
|------|----------|
| `ChwistekSyntax.agda` | Nat, Eq, Code, CVar, CExp, Var, Term, Formula, Proof |
| `ChwistekDiagonal.agda` | Schema, instantiation, `encSchema`, `diag` |
| `ChwistekProvability.agda` | Bool equality, Maybe, decoding, `checkProof` |
| `ChwistekCodeLogic.agda` | Roundtrip lemmas, `diagEnc` bridge |
| `ChwistekCodeQuant.agda` | Code-variable substitution, `evalCExp` |
| `ChwistekGodelSentence.agda` | `phi`, `phiCode`, `GoedelSentence`, self-reference |
| `ChwistekGodelProof.agda` | Goedel I conditional on soundness |
| `ChwistekGodel1.agda` | Analysis of proto-G (too weak) |
| `ChwistekSoundness.agda` | Soundness, `encodeProof`, **`goedel1-final`** |

### Reflection hierarchy

| File | Contents |
|------|----------|
| `ChwistekProofExt.agda` | `ProofExt` with `ax-eval`, soundness, D1 |
| `ChwistekProofExtCheck.agda` | `checkProofExt`, `encodeProofExt-correct` |
| `ChwistekDerivabilityBoundary.agda` | D1, D2, D3 analysis, boundary |
| `ChwistekReflectionHierarchy.agda` | Blindness lemma, hierarchy strictness |

### Fuel-based development (toward Goedel II)

| File | Contents |
|------|----------|
| `ChwistekFuelChecker.agda` | `checkProofN` / `evalCExpN` (unified) |
| `ChwistekFuelGodel.agda` | `represent-fuel`, `D1-fuel`, `D3-fuel` |
| `ChwistekFuelGodel2.agda` | `soundProofN`, `goedel1-fuel`, `goedel2-meta` |
| `ChwistekNelsonCorollary.agda` | Instance vs universal verification gap |
| `ChwistekOpenConsistency.agda` | Open consistency of propositional fragment |
| `ChwistekNelson.agda` | Corrected Nelson program (packaged theorem) |
| `ChwistekConstructiveGodel.agda` | Constructive Goedel I (ProofC G -> ProofC fbot) |
| `ChwistekGodel2SD.agda` | Goedel II for SD-extended system |
| `ChwistekGodel2Genuine.agda` | Goedel II relative to axSDruleG |
| `CodeRecursion.agda` | `Code-rec`, `Code-rec-unique` (tree recursion/uniqueness) |
| `SelfDestruct.agda` | `sdCode`, **`sd-meta-correct`** (self-destruct admissibility) |
| `CExpPair.agda` | `CExpP` with `cpair`, `evalGP`, compatibility lemmas |
| `SelfDestructExp.agda` | `sdExp`, **`sdExp-clit-correct = refl`** |
| `Godel2Internal.agda` | **`goedel2-internal`** (Goedel II via axSdExp) |
| `ChwistekGodel2Sound.agda` | Standard-semantics soundProofG (WIP, has holes) |

## The Goedel II analysis

### Three levels of Goedel II

The development proves Goedel II at three increasing levels of
self-referential content:

| Result | Self-referential? | Extra axioms? | File |
|--------|-------------------|---------------|------|
| `conG-unprovable-semantic` | No | None | ChwistekGodel2Genuine |
| `goedel2-via-axSD` | Yes | axSDruleG | ChwistekGodel2Genuine |
| `goedel2-internal` | Yes | **axSdExp** | Godel2Internal |

`goedel2-internal` uses the narrowest axiom (`axSdExp`: template-
closure for the verified self-destruct template). It is the exact
internal counterpart of `sd-meta-correct`.

### What is derived vs assumed

| Component | Status |
|-----------|--------|
| Self-reference (quine via `csub`) | Derived |
| Encoding/decoding roundtrips | Derived |
| Proof encoding (`encodeProofG`) | Derived |
| Fuel monotonicity (`checkG-mono`, `evalG-mono`) | Derived |
| Encoding correctness (`encodeBaseG-fuel`) | Derived |
| D1 (representability) | Derived |
| Goedel I (meta-level) | Derived |
| Constructive Goedel I (`ProofC G -> ProofC fbot`) | Derived |
| Self-destruct code builder (`sdCode`) | Derived |
| Self-destruct admissibility (`sd-meta-correct`) | Derived |
| Self-destruct as internal template (`sdExp`) | Derived (`refl`) |
| **Template-closure axiom (`axSdExp`)** | **Assumed** |

### What axSdExp says

```
axSdExp : ProofTP n (fimpP (fceqP (ccheckP e) (csub-expr))
                           (fceqP (ccheckP (sdExp e)) (clitP (encFormula fbot))))
```

"If `ccheck(e)` evaluates to `enc(G)`, then `ccheck(sdExp(e))`
evaluates to `enc(fbot)`." This says checker-validity is preserved
by the verified self-destruct template `sdExp`.

### sd-meta-correct: metatheoretic validation

```
sd-meta-correct : (n : Nat) -> (p : Code) ->
  Eq (checkG (suc n) p) (just GoedelSentence) ->
  Eq (checkG (suc (sdFuel n)) (sdCode p)) (just fbot)
```

This Agda-level theorem proves that `axSdExp` is
**metatheoretically conservative**: it only asserts what the checker
can already verify on closed proof codes by direct computation.
The proof is finite case analysis on the fixed template structure
of `sdCode(p)` — no induction on `p` is needed.

### Why axSdExp cannot be derived

`axSdExp` lifts a metatheorem (`sd-meta-correct`) into an
object-theoretic rule. Any schema that internalizes "whatever the
Agda metalevel proves about the checker, the object theory can
conclude" is a **reflection principle**. Goedel's second
incompleteness theorem says a consistent system cannot fully
reflect its own metatheory.

Concretely: `sd-meta-correct` works by unfolding `checkG` on the
specific template structure of `sdCode(p)`. To derive this
*internally*, the object theory would need to reproduce this
checker-unfolding argument uniformly for a variable proof code `e`.
That requires the system to verify its own checker's behavior —
which is the classical Goedel II barrier.

The development shows this barrier is **very narrow**: it is not
full internal soundness, not structural induction over codes, not
general representability. It is exactly **one conditional checker
computation on one verified template**. That is as minimal as a
Goedel-II-enabling extension can be.

### Comparison with known approaches

| Approach | How reflection is handled |
|----------|--------------------------|
| Paulson (Isabelle) | Sigma-1 completeness of arithmetic |
| Shankar (Nqthm) | Representability + arithmetized induction |
| O'Connor (Coq) | Primitive recursive arithmetic |
| **This development** | **Template-closure (axSdExp)** |

All complete proofs of Goedel II derive the reflection step from
arithmetic induction over the proof predicate. This development
avoids arithmetic entirely (syntax-native). The `axSdExp` axiom
marks the exact point where arithmetic reasoning would be needed
in the classical route. It is the tree-native minimal reflection
principle for Goedel II.

## How it works

The object language has seven formula constructors:
`fbot`, `feq`, `fimp`, `fall`, `fcode`, `fceq`, `fcAll`.

The proof system is Hilbert-style: `ax-refl`, `ax-k`, `ax-s`, `mp`, `gen`, `cgen`.

The Goedel sentence uses a **quine construction**:

1. Define `phi` with one free code variable containing `csub (cvar cvz) (cvar cvz)`.
2. Compute `phiCode = encFormula phi`.
3. `GoedelSentence = substFormulaCode0 (clit phiCode) phi`.
4. `csub (clit phiCode) (clit phiCode)` evaluates to `encFormula GoedelSentence`.

## Building

Requires Agda 2.8.0. To type-check all results:

```
agda ChwistekSoundness.agda              # Goedel I
agda ChwistekReflectionHierarchy.agda    # Hierarchy theorem
agda ChwistekFuelGodel2.agda             # Fuel-based Goedel II
agda ChwistekGodel2Genuine.agda          # Goedel II (relative to axSD)
agda Godel2Internal.agda                 # Goedel II (via template-closure)
```

## Paper

See `paper.tex` / `paper.pdf` for a detailed presentation of the results.

## Inspiration

This development captures the spirit of Chwistek's formal metamathematics:
syntax is primitive, substitution is structural, proofs are explicit objects,
and self-reference is achieved through direct manipulation of expressions
rather than arithmetic coding. The comparison between stratified and fuel-based
architectures formalizes the distinction between Chwistek's metasystem approach
and Guard's single-system approach to incompleteness.
