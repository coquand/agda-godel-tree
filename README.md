# Chwistek-style Goedel I in Agda

A syntax-native formalization of Goedel's first incompleteness theorem in Agda,
inspired by Chwistek's approach to formal metamathematics.

## Key features

- **No arithmetization**: syntax is represented as binary trees (`Code`), not
  unary natural numbers. No Goedel numbering.
- **No postulates**: everything is proved from scratch, including soundness.
- **No standard library**: fully self-contained.
- **ASCII only**: no Unicode identifiers.
- **Finite self-reference**: the Goedel sentence refers to its own code via
  the classical quine trick (`csub`), avoiding infinite terms.

## Main result

```
goedel1-final : MetaNot (Proof GoedelSentence)
```

The Goedel sentence is not provable in the Hilbert-style proof system.
No consistency assumption is needed — the proof derives a contradiction
directly from a hypothetical `Proof GoedelSentence` using:

1. **Soundness** (`soundProof`): every provable formula is true in all environments.
2. **Encoding** (`encodeProof`): every `Proof` tree has a corresponding proof code.
3. **Encoding correctness** (`encodeProof-correct`): the proof checker accepts encoded proofs.
4. **Self-reference** (`GoedelSentence-self-ref`): the `csub` expression inside `GoedelSentence`
   evaluates to `encFormula GoedelSentence`.

## File structure

| File | Contents |
|------|----------|
| `ChwistekSyntax.agda` | Nat, Eq, Code, Var, CVar, CExp, Term, Formula, Proof, encoding, substitution |
| `ChwistekDiagonal.agda` | Schema, instantiation, `encSchema`, `diag` |
| `ChwistekProvability.agda` | Bool equality, Maybe, decoding, `checkProof`, `ProvableFormula` |
| `ChwistekCodeLogic.agda` | `decSchema`, roundtrip lemmas (`decFormula-encFormula`, etc.), `diagEnc` bridge |
| `ChwistekCodeQuant.agda` | Code-variable substitution (`substCExp0`, `substFormulaCode0`), `evalCExp` |
| `ChwistekGodelSentence.agda` | `phi`, `phiCode`, `GoedelSentence`, self-reference property |
| `ChwistekGodelProof.agda` | Goedel I conditional on soundness (intermediate step) |
| `ChwistekGodel1.agda` | Earlier analysis showing proto-G was too weak |
| `ChwistekSoundness.agda` | General soundness, `encodeProof`, `encodeProof-correct`, **`goedel1-final`** |

## How it works

The object language has seven formula constructors:

- `fbot` (falsity), `feq` (term equality), `fimp` (implication)
- `fall` (term quantification), `fcode` (code leaf)
- `fceq` (code expression equality), `fcAll` (code quantification)

The proof system is Hilbert-style: `ax-refl`, `ax-k`, `ax-s`, `mp`, `gen`, `cgen`.

The Goedel sentence uses a **quine construction**:

1. Define `phi` — a formula with one free code variable containing `csub (cvar cvz) (cvar cvz)`.
2. Compute `phiCode = encFormula phi`.
3. `GoedelSentence = substFormulaCode0 (clit phiCode) phi` — substitute the code of phi for the free variable.
4. The `csub` expression inside GoedelSentence evaluates to `encFormula GoedelSentence` at runtime, achieving self-reference without circularity.

## Building

Requires Agda 2.8.0. To type-check the main result:

```
agda ChwistekSoundness.agda
```

## Reflection hierarchy

Beyond Goedel I, the development explores what is needed for Goedel II
by adding an extended proof system (`ProofExt`) with a reflection rule
(`ax-eval`) that internalizes evaluation facts as provable `fceq` formulas.

The key finding is a **strict reflection hierarchy**:

- **Reflection success**: the extended system can prove that old proof codes
  check correctly (D1, the first Hilbert-Bernays condition).
- **Reflection failure**: the old evaluator is provably blind to extended
  proof codes (`evalCExp-blind-to-ax-eval`). Tag 36 codes return `nothing`.
- **Self-reflection impossible**: no equality witness exists for re-reflecting
  ax-eval proofs (`no-self-reflect-ax-eval`).

This shows that Chwistek's metasystem/object-system separation is
structurally necessary: each layer can reason about the layer below,
but not about its own reflective reasoning.

### Extended files

| File | Contents |
|------|----------|
| `ChwistekProofExt.agda` | `ProofExt` with `ax-eval`, soundness, D1/self-ref |
| `ChwistekProofExtCheck.agda` | `checkProofExt`, `encodeProofExt-correct` |
| `ChwistekDerivabilityBoundary.agda` | D1, D2, D3 analysis, `Con`, boundary |
| `ChwistekReflectionHierarchy.agda` | Blindness lemma, hierarchy strictness |

## Inspiration

This development captures the spirit of Chwistek's formal metamathematics:
syntax is primitive, substitution is structural, proofs are explicit objects,
and self-reference is achieved through direct manipulation of expressions
rather than arithmetic coding.
