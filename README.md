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

### Why it cannot be derived (yet)

Deriving `axSDruleG` internally requires the system to prove a
**uniform internal proof-transformation theorem**: for all proof
codes `e`, if `e` proves G, then `selfDestruct(e)` proves fbot.

This is weaker than full internal soundness — it is a statement about
one specific formula (G) and one specific transformation. But it still
requires the system to **reason uniformly over arbitrary proof codes**
and verify that the self-destruct transformer preserves checker
acceptance. The system currently lacks the machinery for this.

### What is missing concretely

The gap is not "internal soundness" in full generality. It is:

1. **A totalized internal checker**: the current checker returns
   `Maybe Formula` (partial). Formulas cannot reason about partial
   results on arbitrary code variables — only on closed literals
   via `axEvalG`. A total code-valued checker (`checkCodeT : Nat ->
   Code -> Code`) would let formulas express "code e proves formula A"
   as `fceq (ccheckT e) (clit (encFormula A))` for variable `e`.

2. **Induction over codes**: to prove that the self-destruct
   transformation preserves checker acceptance for ALL codes, the
   system needs an induction principle over binary-tree codes
   (structural induction on `catom`/`cnode`).

3. **Internal representability of the checker's behavior**: enough
   internal lemmas to verify that `checkG` is compositional — that
   mp, instantiation, and the self-destruct construction produce
   codes that the checker accepts, provably inside the system.

None of these require arithmetization. They are the **tree-native
analogues** of what arithmetic supplies in the classical route
(Sigma-1 completeness, primitive recursive representability).

### Relationship to known approaches

| Approach | How reflection is handled |
|----------|--------------------------|
| Paulson (Isabelle) | Sigma-1 completeness of arithmetic |
| Shankar (Nqthm) | Representability + arithmetized induction |
| O'Connor (Coq) | Primitive recursive arithmetic |
| **This development** | **Assumed as axSDruleG** |

The standard route derives the reflection step from arithmetic
induction over the proof predicate. This development avoids
arithmetic entirely (syntax-native), which is a strength for
Goedel I but means the standard Sigma-1 route is not available.

The right next step is not "give up and arithmetize" but
**build Guard over trees**: totalized checker, code induction,
internal representability — all on binary trees without Goedel
numbering.

### The key distinction: quantification vs induction

The current system has `fcAll` which gives **universal quantification**
over codes: "for all codes c, P(c)." But Goedel II needs **structural
induction** over codes: the ability to prove P(c) for all c by showing
P holds for atoms and is preserved by `cnode`.

These are completely different proof-theoretic resources. The current
formula language is first-order in codes:

- Code variables: yes
- Formulas about codes: yes
- Predicates on codes as objects: no
- Induction schema over such predicates: no

The system can talk *about* arbitrary proof codes but cannot
internalize the structural reasoning needed to prove uniform facts
about all proof codes.

### Self-destruct admissibility (proved)

The self-destruct map `sdCode : Code -> Code` wraps a proof code `p`
in the 6-step constructive Goedel I derivation template. It is NOT
recursive in `p` — it is a fixed-depth wrapper.

```
sd-meta-correct : (n : Nat) -> (p : Code) ->
  Eq (checkG (suc n) p) (just GoedelSentence) ->
  Eq (checkG (suc (sdFuel n)) (sdCode p)) (just fbot)
```

Whenever `checkG` accepts `p` as proving G, it accepts `sdCode(p)` as
proving fbot. The proof is finite case analysis on the known template
structure (no induction on `p`). Therefore `axSDruleG` is
**metatheoretically conservative** over direct checker computation on
closed proof codes.

See `SelfDestruct.agda`.

### Remaining problem

To obtain genuine Goedel II in the base object theory, one must
internalize this conditional checker argument uniformly for
**variable** proof codes. The barrier is not code induction or
defining `sd`, but **transporting a hypothesis about `ccheck(p)`
through a verified template when `p` is universally quantified**.

The precise target: design the weakest object-language extension
that turns `sd-meta-correct` into a derivable object-theoretic rule.
This is best described as **conditional representability of checker
computation** or **internal admissibility of checker-verified
templates**.

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
