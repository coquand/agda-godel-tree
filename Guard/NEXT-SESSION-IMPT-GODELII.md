# Next Session: Gödel II via object-level implication (Rose/Ryan approach)

## Motivation

The earlier attempts at classical Gödel II via
`GodelIIClassicalSkel.agda` + a `Phi` diagonal encoder ran into the
obstruction documented in `StrongPhiCorrAnalysis.agda` and
`EncCorrPfAnalysis.agda`: without some form of internal implication,
the `strongPhiCorr` equation cannot be derived polymorphically in
`v0`.  The obstruction boiled down to the missing
Hilbert–Bernays condition **DC2** (internalised modus ponens / proof
closure under implication).

**Rose (1967)** and **Ryan (1978)** prove Gödel II for primitive-
recursive arithmetic using object-level `→` as arithmetic implication
between characteristic values.  Their Lemma 1 is DC2 stated
internally; their Theorem 4 is a linear chain of implications closed
by reductio ad absurdum.

A prototype `Guard/ImpT.agda` (compiles under 0.05s, no postulates,
no holes) shows:

```agda
impT : Term -> Term -> Term
impT A B = ap2 IfLf A (ap2 Pair B O)
```

is exactly propositional implication on truth values `{O, Pair O O}`,
and **modus ponens is a derivable equational theorem**, not a new
Deriv rule.  This unlocks the Rose/Ryan path *without modifying
`Deriv`, `Thm14EV3`, or `ProofEnc`*.

## Architecture

### Layer 1 — `Guard/ImpT.agda` (DONE, prototype)

Basic `impT` definition, truth-table lemmas (`impTTrueAnt`,
`impTFalseAnt`), `modusPonens`, `transImpWithAntecedent`,
`reductioBranch`.  ~120 lines, 0.04s.

### Layer 2 — `Guard/ImpTProp.agda` (NEW, ~200 lines)

Propositional theorems for `impT`.  For values with **known head
shape** (`O` or `ap2 Pair x y`), derive:

- K axiom: `A -> (B -> A)` when `A = trueT`.
- Implication distributes: `A -> (B -> C) <-> (A ∧ B) -> C`.
- Contrapositive: `(A -> B) -> (¬B -> ¬A)` where `¬A := impT A falseT`.
- Chain: `(A -> B) -> (B -> C) -> (A -> C)`.
- Case-analysis on TreeEq results (TreeEq always produces O or poo).

Many of these will be **schematic** — parameterised by the known-
shape of one or more operands.  The TreeEq output shape is crucial:
`axTreeEq{LL,LN,NL,NN}` guarantee TreeEq produces O, poo, poo, or an
IfLf-expression respectively — all with decidable head shape.

### Layer 3 — `Guard/RoseDC1.agda` (repurpose existing, ~20 lines new)

Rose's Lemma 2 (DC1 for equations).  For each PR function `f` in our
primitives (I, Fst, Snd, Comp, ..., Pair, TreeEq, ...), provide a
function `p_f : Term -> Term -> Term` such that

```
Deriv hyp (eqn (ap2 f t1 t2) r)
  -> Deriv hyp (eqn (ap1 (thmT trivCT) (p_f t1 t2)) (reify (codeEqn (eqn (ap2 f t1 t2) r))))
```

This is **already provided by `thm14EV3`** for general Deriv.  We
just need to repackage the specific cases into `p_f` form for direct
use in Rose's proof.

### Layer 4 — `Guard/RoseDC2.agda` (NEW, the load-bearing piece, ~300 lines)

Rose's Lemma 1: internalised derivability is closed under modus
ponens.

```agda
roseLemma1 :
  {H : Equation} (A B : Equation) ->
  (d : Deriv H B) ->
  -- Given derivations of each hypothesis, V combines them:
  Sigma Term (\V ->
    (p q : Term) {hyp : Equation} ->
    -- "p is a proof of A"
    Deriv hyp (eqn (ap1 (thmT trivCT) p) (reify (codeEqn A))) ->
    -- "q is a proof of A -> B"
    Deriv hyp (eqn (ap1 (thmT trivCT) q)
                   (reify (codeEqn (impEqn A B)))) ->
    -- "V(p,q) is a proof of B"
    Deriv hyp (eqn (ap1 (thmT trivCT) (ap2 mpPair V (ap2 Pair p q)))
                   (reify (codeEqn B))))
```

Here `impEqn A B` is the "equation form of A -> B" -- use `impT` on
A's and B's characteristic values, dressed as an equation.

Proof strategy: induction on `Deriv H B`, following Rose's proof
shape.  Each case uses layer 2's propositional theorems + layer 3's
DC1.

Key insight: the V function does NOT need to manually encode the
derivation.  It just needs to combine `p` and `q` using `impT`'s
modus ponens (layer 1) at the object level.

### Layer 5 — `Guard/GodelIIRose.agda` (NEW, ~150 lines)

Gödel II via Rose's Theorem 4.  Direct transcription:

```
th(z) = se(nu(N), N)
  -> G(z) = 0
  -> th(p_G(z,0)) = {G(z) = 0}            [Lemma 2 = RoseDC1]
  -> th(V(p_G(z,0))) = {se(nu(N),N)=th(z)} [Lemma 1 = RoseDC2]
  -> e(th(V(...))) = {se(nu(N),N) != th(z)} [def of e]
  -> th(Y(z,z)) != {se(nu(N),N) != th(z)}   [CONSISTENCY]
  -> th(z) != [se(nu(N),N) != th(z)]
  -> th(z) != se(nu(N),N)                    [Lemma 3 = godelI]
```

Each `->` is `impT` at the object level, instantiated then closed by
`modusPonens`.  The final `!=` is derived as `impT (eqn X Y) falseT`
= trueT where X = thmT trivCT (var 0), Y = codeBotT.  Reductio closes
the diagonal.

## The consistency statement (Rose-style)

Rose uses `th(y) != e(th(z))` -- no equation is the negation of
another's theorem.  In our setting this transcribes to:

```agda
ConTrivRose : Equation
ConTrivRose = eqn
  (impT (ap2 TreeEq (ap1 (thmT trivCT) (var zero)) codeBotT) falseT)
  trueT
```

Read: "for all proof-encodings p, (thmT trivCT p = codeBotT) -> falseT"
= "no p is a proof of bot".  This is a SINGLE equation with `impT` on
the LHS.  It's morally equivalent to the old `ConTriv` but stated with
explicit implication, which makes Rose's proof transcribable.

The key semantic shift: `ConTrivRose` says "consistency is provable as
an implication that always yields true", NOT "TreeEq always produces
poo".  The former composes with `modusPonens`; the latter does not.

## Migration of existing code

- `Guard/ImpT.agda`: new (done).
- `Guard/GodelIIClassicalSkel.agda`: keep as an alternative / reference
  architecture.  The new path will produce `Guard/GodelIIRose.agda`
  as the canonical classical Gödel II.
- `Guard/ProofEnc.agda` 27 encoders: unchanged; used as building
  blocks for DC1.
- `Guard/StrongPhiCorrAnalysis.agda`, `Guard/EncCorrPfAnalysis.agda`:
  keep as historical documentation of why the pure-equational path
  failed and implication was needed.

## Suggested session plan

1. **Bulk out Layer 2** (`ImpTProp.agda`): prove the propositional
   theorems above.  Each one is 5-15 lines.  Check they all compile.
2. **Specialise DC1 as `p_f`** (`RoseDC1.agda`): repackage
   `thm14EV3AxI`, `thm14EV3AxFst`, etc., as `p_f` functions matching
   Rose's Lemma 2 form.
3. **Prove `roseLemma1`** (`RoseDC2.agda`): induction on Deriv, using
   Layer 2 at each step.  This is the creative work -- each Deriv
   constructor case mirrors a step in Rose's induction proof.
4. **Transcribe Theorem 4** (`GodelIIRose.agda`): chain of MPs.
5. **Verify**: full `GodelIIRose.agda` compiles under 10s.  Compare
   with `godelIIV3` to confirm both Gödel II statements are
   derivable.

## Size estimate

| Layer | File                     | Lines | Status           |
|-------|--------------------------|-------|------------------|
| 1     | `Guard/ImpT.agda`         | 160   | DONE             |
| 2     | `Guard/ImpTProp.agda`     | ~200  | TODO             |
| 3     | `Guard/RoseDC1.agda`      | ~50   | mostly wrapping  |
| 4     | `Guard/RoseDC2.agda`      | ~300  | creative work    |
| 5     | `Guard/GodelIIRose.agda`  | ~150  | mechanical       |
|       | **Total**                 | ~860  |                  |

Compare to approach (A)'s ~1000-2000 lines with no guarantee of
closing Gödel II at the end.

## Why this should work where approach (A) did not

The `strongPhiCorr` equation in the old skeleton demanded a
**polymorphic-in-v0 equational bridge** between two TreeEqs whose
second slots are distinct closed terms (`reify cGSCR` vs `codeBotT`).
This is provably unbridgeable.

Rose's Theorem 4 avoids this by chaining implications: each step is a
PROVABLE implication (`impT X Y = trueT`), and modus ponens closes
the chain with an ACTUAL derivation of the antecedent.  There is
never a need to bridge two unequal closed terms — they appear on
different sides of different implications, connected by modus ponens
not by equation.

## Commit convention

Per existing project style:

- `[impt]` for ImpT additions.
- `[rose-dc2]` for DC2 work.
- `[rose-godelII]` for Theorem 4.
- `[doc]` for NEXT-SESSION updates.

## Invariants

- `~/.cabal/bin/agda-2.9.0` (not `/opt/homebrew/bin/agda`).
- `--safe --without-K --exact-split`.
- No postulates, no holes.
- Object-level implication IS PERMITTED — it is a pure definition
  `impT A B = ap2 IfLf A (ap2 Pair B O)` using existing primitives.
  No extension of `Deriv`.
- Commit and push after each file compiles clean.

## Sanity check

```
~/.cabal/bin/agda-2.9.0 Guard/ImpT.agda
```

Under 0.1s with no output.
