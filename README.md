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

### Genuine Goedel II (Guard-style unified checker)

```
Con-implies-G  : ProofG2 n ConG -> ProofG2 n GoedelSentence
goedel2-genuine : ProofG2 n ConG -> EmptyG2
```

A self-contained Goedel II using a unified mutual-recursive checker
(`checkG`/`evalG`) with tags 30-39 covering all proof rules, code
evaluation, transitivity, symmetry, and quantifier instantiation.

The proof system `ProofG` extends the base Hilbert system with:
- `axEvalG`: evaluation reflection (if `evalG n e = just c` then
  `fceq e (clit c)` is provable)
- `cinstG`, `fceqTrG`, `fceqSyG`: code quantifier elimination,
  code-equality transitivity and symmetry

`ProofG2` further extends `ProofG` with `cinstEG` (CExp quantifier
elimination) and `axSDruleG` (self-destruct reflection). The internal
derivation `Con-implies-G` composes `axSDruleG` with instantiated
consistency via Hilbert S/K combinators. The contradiction follows
from `soundGoodG2` under a valuation where `fceq -> UnitG2` and
`fbot -> EmptyG2`.

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
| Goedel II | Impossible | Meta-level; genuine with axSD |

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
| `ChwistekGodel2Genuine.agda` | Genuine Goedel II (Guard-style unified checker) |

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
agda ChwistekGodel2Genuine.agda          # Genuine Goedel II
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
