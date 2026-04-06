# Next Session: Kritchman-Raz via Leivant Machines

## Setup
Use `~/.cabal/bin/agda-2.9.0`. The Guard/ directory has the complete formalization.

## What exists

### Nelson-WC Boundary (complete)
- `WellChained.agda` (475 lines): 16 WC constructors, semSound
- `BoundaryQuantitative.agda` (293 lines): WC0 (zero-backtracking), semSound0 with no external conditions
- `NelsonWCBoundary.agda` (233 lines): proofEToWC, derivToWC, obstruction theorem
- `nelson-wc-boundary.tex` (7 pages): write-up with connections to Nelson and Aschieri

### Gödel II (diagonal, complete)
- `GodelII.agda`: standard diagonal argument via thFunTFor + Schema F

### Key finding
The obstruction to uniform internal soundness is the evalCode side condition (EvalOK). But this is specific to the diagonal proof. A KR-based proof would have a DIFFERENT obstruction — about computation bounds rather than tag dispatch — which might connect more directly to Aschieri's complexity analysis.

## What to do

### Goal: Kritchman-Raz Gödel II in the tree system

Following Nelson's Elements §17-19 and Leivant:

1. **Register machines in the tree system**
   - Strings as trees (binary: nd for bit, lf for empty)
   - Registers as tuple of trees
   - Commands: 0 (prepend zero), 1 (prepend one), P (predecessor), C (case)
   - Key property (Leivant §3.3): one-step function uses NO recursion, just Pair/Fst/Snd/IfLf
   - Multi-step: Rec applied to the step function

2. **Kolmogorov complexity**
   - K(x) = length of shortest machine producing x
   - K is unbounded but K(specific-string) is provable for each string
   - Formalize as a bounded predicate in the system

3. **The KR surprise examination argument**
   - 2^{ℓ+1} strings but < 2^{ℓ+1} machines of length ≤ ℓ
   - Pigeonhole: some ξ has K(ξ) > ℓ
   - If system proves consistency → can bound Chaitin machine search → contradiction

4. **The new obstruction**
   - Where does the Buss-Tao gap appear in the KR formalization?
   - What replaces EvalOK as the side condition?
   - Does the BLevel stratification correspond to the surprise-exam δ parameter?

### The sharp question

Does the Nelson-WC boundary look different when Gödel II uses pigeonhole (KR) instead of diagonalization? Specifically:
- Is the obstruction still about evalCode/substTFor, or about computation bounds?
- Does the BLevel hierarchy align with the KR induction on δ?
- Can Aschieri's backtracking level be connected to the KR complexity bounds?

### References
- Elements §17 (Leivant register machines), §18 (incompleteness without diagonalization), §19 (the inconsistency theorem)
- Leivant, "Ramified recurrence and computational complexity I", 1994
- Kritchman-Raz, "The Surprise Examination", Notices AMS 2010
- Aschieri, "Game Semantics and the Geometry of Backtracking", 2016

### Technical note
The one-step-without-recursion property is what makes Leivant machines a good fit for our system. A single step is a Fun2 term (composition of IfLf, Pair, Fst, Snd). This avoids the substTFor commutativity problem at the single-step level — the issue only arises when iterating (Rec).
