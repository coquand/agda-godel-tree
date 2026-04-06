# Next Session: Oblivious Invariants and Nelson

## Setup
Use `~/.cabal/bin/agda-2.9.0`. The Guard/ directory has the complete formalization.

## What was built this session

### Leivant machines (Machine.agda)
- iterate combinator: `Rec init (Post f (Post Snd sndArg))` gives f^n(init) on natCode n
- Proved: iterBase, iterNd, iterSuc; copyStep halt/advance correctness

### Feasibility tools
- `FindError.agda`: metalevel eval + checkProof + findError (crude evalCode)
- `GroundEval.agda`: full ground evaluator geval dispatching ALL functors including Rec/Comp/Comp2/Post/Fan/Lift. checkProof2 using geval.
- `KRIterate.agda`: iterate computations pass checkProof2
- `KRSchemaF.agda`: Schema F passes checkProof2 (general argument: universal truth → geval agrees)

### The key result (KRShortProof.agda)
A **constant-size** Schema F proof that natCodeIter never outputs ξ = nd(nd lf lf) lf:
- h = Comp2 TreeEq natCodeIter (KT xiT), g = KT(Pair(O,O))
- Base: TreeEq(O, Pair(Pair(O,O), O)) = Pair(O,O) by axTreeEqLN
- Step: TreeEq(Pair(O, nci(v1)), Pair(Pair(O,O), O)): IfLf dispatches on TreeEq(O, Pair(O,O)) = Pair(O,O) (ground, nonzero) → returns Pair(O,O) without examining v1
- Schema F: h(var 0) = g(var 0) = Pair(O,O). Meaning: natCodeIter(t) ≠ ξ for ALL trees.
- checkProof2 = true (verified by Agda refl)

This is an **oblivious invariant**: the proof short-circuits at a ground comparison before reaching any variable-dependent data.

## The sharp question

**Does every program of bounded code-size admit an oblivious invariant against some fixed ξ?**

If yes: the KR pigeonhole proof is O(N(l)) in size (one O(1) Schema F proof per program), all at BLevel 0, all passing checkProof2. Nelson's feasibility claim holds.

If no: some programs need variable-dependent reasoning (BLevel ≥ 1).

## What to do next

### 1. Test more program types
- Comp-based programs: e.g., Comp Fst (Comp2 Pair I I). Does the output have a fixed structural feature?
- Comp2-based: e.g., Comp2 Pair Fst Snd (swap). Apply to natCode values — what's the invariant?
- Rec-based (non-iterate): general tree recursion. Can the output's structure be characterized obliviously?

### 2. Characterize which programs have oblivious invariants
A program p has an oblivious invariant against ξ if there exists a position (a path of Fst/Snd projections) where p's outputs are always a fixed value differing from ξ's value at that position.

For iterate f init: this requires that some projection of the output is constant across all iterations. This holds when f preserves a projection (e.g., Fst(f(x)) = Fst(x) or Fst(f(x)) = c for constant c).

**Conjecture**: for any ξ with sufficiently "complex" structure (e.g., ξ has Fst = Pair(O,O) but all small programs produce outputs with Fst = O or Fst = Pair(O,O)), there's an oblivious invariant.

### 3. The ξ construction
Choose ξ so that at every Fst/Snd projection, ξ's value differs from what any small program can produce at that position. This is a combinatorial construction on trees.

### 4. Internalize geval
Can geval for BLevel k be defined as a Fun1 at BLevel k+1? This would:
- Close the feasibility loop (the system verifies itself, level by level)
- Give the stratified consistency proof Nelson may have envisioned
- Connect to Cook's PV hierarchy

### 5. Connect to proof complexity
The oblivious invariant approach gives proof size O(N(l)) for the pigeonhole instance. N(l) ≤ 2^l. Is there a way to batch the invariant proofs (prove them collectively rather than one per program)? This would reduce proof size further.

## Key insight for Nelson
The obstacle to feasible consistency is NOT:
- verification (always polynomial — geval works)
- universal over clocks (Schema F handles it at BLevel 0)
- self-reference (KR avoids diagonalization)

The obstacle IS:
- the NUMBER of programs (2^l of them need invariant proofs)
- whether oblivious invariants exist for all programs

This is a **counting obstacle**, not a structural or logical one. It's amenable to combinatorial analysis, not blocked by Gödel's theorem per se.
