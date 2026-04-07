# Next Session: Chaitin Machine and Proof Encoding

## Setup
Use `~/.cabal/bin/agda-2.9.0`. The Guard/ directory has the complete formalization.

## What was built (sessions of April 6-7)

### The R/Q lemma technique
Two Schema F lemmas that handle ALL program types at BLevel 0:

- **R** (ifLfCollapse): `IfLf(x, Pair(poo, poo)) = poo` for all x.
- **Q_{a,b}**: `IfLf(TreeEq(x, a), Pair(TreeEq(x, b), poo)) = poo` when a ≠ b.

### Five complete equational proofs (all BLevel 0, all O(1))

| # | File | Program | Case | Technique |
|---|------|---------|------|-----------|
| 1 | KRShortProof.agda | natCodeIter | 1: constant Fst | Fst mismatch, oblivious |
| 2 | DoublerProof.agda | doubler | 3: same variable | Q lemma, 3 nested Schema F |
| 3 | GeneralQ.agda | tripler | 2: Pair-vs-O | axTreeEqNL + R collapse |
| 4 | GeneralQ.agda | mixed | 2: Fst match | treeEqSelf + axIfLfL fallthrough |
| 5 | SwapProof.agda | rotate | 4: different projections | Modular h2 helper + R |

### Case classification resolved

For step f(x) = Pair(g(x), h(x)) vs xi = Pair(a, b):
- **Case 1**: g constant, g ≠ a → immediate short-circuit
- **Case 2**: one component gives Pair-vs-O → axTreeEqNL + R collapse
- **Case 3**: g = h (same variable) → Q lemma
- **Case 4**: g ≠ h (different projections) → modular h2 helper: prove TreeEq(f(x), xi) = poo by its own Schema F, then instantiate in the iterate proof

Key insight for Case 4: IfLf-guarded step functions have f(O) = O (trivial base), and the Pair structure in f(Pair(a,b)) always creates a Pair-vs-O comparison at some component, which collapses via R.

### MicroNelson.agda: complete finite KR instance

28 step functions (all Comp2 Pair f g where f,g ∈ {I, Fst, Snd, KT O, KT poo}, plus 5 base Fun1) × 2 modes (iterate + direct) = **56 programs**, all verified against xi4 = Pair(Pair(Pair(O,O),O), Pair(O,O)).

- All 56: checkProof2 = true (verified by Agda `refl`)
- KT(reify xi4): checkProof2 = false (sanity check)
- 0 postulates, --safe, all BLevel 0

### Experiment files
- ObliviousTest.agda: 10 programs vs xi1 (8 true, 2 false)
- ObliviousXi.agda: 5 xi × 9 programs + acid tests; discovered checkProof2 false positives
- ObliviousAnalysis.agda: stuck-var outputs; all iterate programs give f(O)
- ObliviousChar.agda: characterization theorem (skeleton analysis)

### Documents
- general-oblivious.tex: full analysis with theorems, all 4 cases, micro-Nelson
- oblivious-analysis.tex: earlier analysis (superseded by general-oblivious.tex)

## Current state of Guard/

~40 .agda files. Key layers:
1. Base/Term/Step: tree system, equational derivations, Schema F
2. ThFun/ThFunCorrect: proof encoding, thFun, checkProof2/geval
3. GodelII.agda: Gödel II proved (0 postulates)
4. Machine/KR/GroundEval/FindError: Leivant machines, KR framework, evaluators
5. KRShortProof/DoublerProof/GeneralQ/SwapProof: invariant proofs
6. MicroNelson: complete finite KR instance (56 programs)

## What to do next

### 1. The Chaitin machine (most important)
The KR argument needs a program C(l) that:
- Enumerates proofs in the system
- Searches for a proof of "∃ xi. K(xi) > l"
- Extracts xi from the proof and outputs it

If the system proves its own consistency, this search terminates, giving K(xi) ≤ |C| < l for large l, contradiction.

The key question: can C(l) be defined as a Fun1 in the tree system?
- Proof enumeration: iterate over all trees t, check if thFun(t) encodes a valid equation
- The "∃ xi. K(xi) > l" statement: for all programs p of size ≤ l, for all clocks c, p(c) ≠ xi
- Extracting xi: from the proof structure

This is where the formalization connects back to Gödel II. The GodelII.agda proof uses the diagonal method. The KR approach avoids the diagonal but needs the Chaitin machine.

### 2. Encode proof chains for checkProof2
Currently checkProof2 only checks the OUTERMOST Schema F conclusion. The doubler proof uses R → Q → main (3 Schema F applications). Can the chain be encoded as a tree that a stronger verifier accepts?

One approach: extend checkProof2 to handle proof SEQUENCES (nd proof1 proof2 means "proof1 then proof2"). Each sub-proof is a Schema F encoding. The verifier checks each one and accumulates verified equations.

### 3. Internalize geval as Fun1
Can geval for BLevel k be defined as a Fun1 at BLevel k+1? This would close the feasibility loop: the system verifies itself level by level. Connected to Cook's PV hierarchy.

### 4. Formalize the pigeonhole in the system
The pigeonhole "∃ xi not output by any small program" is currently metalevel (Agda enumeration in MicroNelson). To fully formalize the KR argument, this needs to be an object-level derivation. Options:
- Encode as a concrete finite case-exhaustion in the equational system
- Use Rec on the enumeration of programs (bounded tree recursion)
- Accept it as a metalevel argument (sufficient for Nelson's program if the meta-reasoning is feasible)

### 5. Write the summary paper
The formalization now contains a substantial result: the structural obstacle to Nelson's feasibility program (variable-dependent reasoning) is eliminated for the KR approach. A clear write-up connecting Guard's equational system → Schema F → R/Q lemmas → micro-Nelson instance → implications for Nelson would be valuable.

## Key files for the next session
- Guard/MicroNelson.agda — the complete finite instance
- Guard/DoublerProof.agda — the Q/R technique template
- Guard/SwapProof.agda — the Case 4 / modular h2 pattern
- Guard/GodelII.agda — the existing Gödel II proof (diagonal approach)
- Guard/Machine.agda — Leivant machines, iterate combinator

## The big picture

Nelson's feasibility program asks: can consistency be proved by feasible means?

What we've shown:
- **YES** for the per-program invariant proofs (O(1) each, BLevel 0, ground-verifiable)
- **YES** for the enumeration (MicroNelson: 56 programs verified by Agda refl)
- **OPEN** for the Chaitin machine construction (self-referential step)
- **OPEN** for internalizing the pigeonhole (counting argument)

The structural obstacles (variable-dependent reasoning, BLevel hierarchy, evaluation universality) have all been bypassed by the R/Q lemma technique. What remains is the self-referential construction — which is the SAME obstacle as in the classical Gödel II proof, but now in a quantitative (KR/pigeonhole) rather than qualitative (diagonal) form.
