# Syntax-Native Incompleteness in Agda

A formalization of Goedel's incompleteness theorems using binary-tree syntax
instead of arithmetic coding, inspired by Chwistek's approach to formal
metamathematics.

**22 Agda files, ~5400 lines. No postulates, no standard library.**

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

### Goedel II for the reflection-extended system

```
Con-implies-G   : ProofG2 n ConG -> ProofG2 n GoedelSentence
goedel2-genuine : ProofG2 n ConG -> EmptyG2
```

ConG is not provable in ProofG2 (the system extended with `axSDruleG`).

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
| `ChwistekGodel2Sound.agda` | Standard-semantics soundProofG (WIP, has holes) |

## The Goedel II gap

The development proves Goedel II **relative to axSDruleG**, not for the
bare system. This section analyzes what is missing.

### What is proved without axioms

Everything except the reflection step:

| Component | Status |
|-----------|--------|
| Self-reference (quine via `csub`) | Derived |
| Encoding/decoding roundtrips | Derived |
| Proof encoding (`encodeProofG`) | Derived |
| Fuel monotonicity (`checkG-mono`) | Derived |
| Encoding correctness (`encodeBaseG-fuel`) | Derived |
| D1 (representability) | Derived |
| Goedel I (meta-level) | Derived |
| Constructive Goedel I (`ProofG G -> ProofG fbot`) | Derived |
| **Internalized reflection (`axSDruleG`)** | **Assumed** |

### What axSDruleG says

```
axSDruleG : ProofG2 n (fimp (fceq (ccheck e) (csub phiCode phiCode))
                             (fceq (ccheck (csub phiCode e)) (clit (encFormula fbot))))
```

In words: "if code e proves G, then the self-destruct code proves fbot."
This is the constructive Goedel I transformation — but stated as an
axiom of the system rather than derived internally.

### Why it cannot be derived

Deriving `axSDruleG` internally would require the system to prove:

1. If `checkG` accepts code `e` as proving G, then the self-destruct
   construction (instantiate G at `e`, apply modus ponens) produces
   a valid proof of fbot.
2. This valid proof is *accepted by `checkG` itself*.

Step 2 is the barrier: the system would need to verify that its own
checker accepts the constructed proof code. This requires the system
to reason about `checkG` by induction over all possible proof codes —
i.e., to prove its own soundness internally. This is exactly what
Goedel II says a consistent system cannot do.

### The classical barrier

The gap is the same one identified by the reflection hierarchy theorem
(`ChwistekReflectionHierarchy.agda`): each proof system can reflect
the layer below but is provably blind to its own reflective reasoning.
`axSDruleG` bridges this gap by fiat.

Concretely, to derive `axSDruleG` one would need:

- **Internal induction over proof codes**: the system proves that for
  ALL codes accepted by `checkG`, the self-destruct transformation
  produces a code also accepted by `checkG`. This is Sigma-1 complete
  induction over the proof predicate.
- **Or equivalently**: internal soundness — the system proves that
  everything it proves is true. Goedel II says this is impossible
  for consistent systems.

### Relationship to known approaches

| Approach | How reflection is handled |
|----------|--------------------------|
| Paulson (Isabelle) | Sigma-1 completeness of arithmetic |
| Shankar (Nqthm) | Representability + arithmetized induction |
| O'Connor (Coq) | Primitive recursive arithmetic |
| **This development** | **Assumed as axSDruleG** |

All complete proofs of Goedel II ultimately derive the reflection step
from arithmetic induction over the proof predicate. This development
avoids arithmetic entirely (syntax-native), which is a strength for
Goedel I but means the standard route to Goedel II (Sigma-1
completeness) is not available. The `axSDruleG` axiom marks the
precise point where arithmetic reasoning would be needed.

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
