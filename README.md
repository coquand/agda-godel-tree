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

## Boundary

The current proof system is strong enough for Goedel I but too weak for
a non-vacuous Goedel II. The system lacks internal reasoning principles
for code computation (no axioms produce `fceq` formulas), so the consistency
formula `Con` is trivially unprovable for the wrong reason. Extending
to Goedel II requires adding reflection rules (`ax-check`, `cinst`, `ax-eval`)
that let the system prove facts about its own proof checker.

## Inspiration

This development captures the spirit of Chwistek's formal metamathematics:
syntax is primitive, substitution is structural, proofs are explicit objects,
and self-reference is achieved through direct manipulation of expressions
rather than arithmetic coding.
