# Next Session: Finish Guard-style Godel II for Binary Trees

## Read first

Read these files in order:
1. `CLAUDE.md` (conventions)
2. `Guard2.agda` (current Godel II — compiles but D2/D3 are axiom schemas)
3. `GuardG3.agda` (convergence semantics, D2 semantic proof)
4. `GuardChecker.agda` (self-encoding fold — the representability primitive)
5. `GuardFull.agda` (checker infrastructure: mpConverge, foldEnvIndep, d2Semantic, checkerOnCatom, checkerConvergeG2)
6. `p15.txt`, `p16.txt`, `p17.txt` (Guard's proof of Theorems 14-16)

## The problem

Guard2.agda proves `godel2G5 : ProofG5 ConG5 -> EmptyTA` but it is NOT
Guard-faithful because:

1. D2 and D3 are **axiom schemas** (constructors of ProofG5), not derived
2. The checker (`checkCG2` in GuardFull) has **13 trust tags** where
   `hTrust = ctVar v2` returns the proof code's payload without verification
3. This makes `ProvG5(bot)` satisfiable via `cnode(catom tagEvalEq, encFormTA3 fbotTA3)`
4. So the Godel II result is formally correct but semantically vacuous

## What exists and compiles (0 postulates, 0 holes)

| File | Lines | What |
|------|-------|------|
| GuardChecker.agda | 180 | `encLiftCorrect`: self-encoding fold computes `encCodeTm(liftCode(c))` |
| GuardG3.agda | 448 | Convergence semantics (`GoodG3`), D1, D2 semantic proof |
| GuardFull.agda | 1400+ | `mpConverge`, `foldEnvIndep`, `d2Semantic`, `checkerOnCatom` |
| Guard2.agda | 232 | `godel2G5` via Loeb (axiom-schema D2/D3) |

## What must be done

### Step 1: Build a genuine checker (no trust tags)

Create `checkCG4` in a new file (or modify GuardFull) where:

**Genuine handlers** (already exist in ncG2, keep them):
- tagK3 -> hK (verifies K axiom structure)
- tagS3 -> hS (verifies S axiom structure)
- tagMP3 -> hMP (recursively checks sub-proofs, extracts conclusion via mp)
- tagGen3 -> hGen (wraps sub-proof result with universal quantifier encoding)
- tagInst3 -> hInst (verifies instantiation)
- tagEx3 -> hExI (verifies existential introduction)
- tagRefl3 -> hRefl (constructs reflexive equation encoding)
- tagSym3 -> hSym (swaps equation sides)
- tagTrans3 -> hTrans (chains equations)

**New genuine handler for tagEvalEq**:

The encoding changes from:
```
cnode(catom tagEvalEq, encFormTA3(conclusion))
```
to:
```
cnode(catom tagEvalEq, cnode(witness_code, encFormTA3(conclusion)))
```

The handler:
1. v4 = fold(right child) = cnode(fold(witness), fold(formula_enc))
2. Extract fold(witness) via ctCase on v4
3. fold(witness) = enc(A) if witness is a valid proof of A
4. Construct expected formula: `enc(fexTA3(feqTA3(checkCG4, liftCode(enc(A)))))`
   - This is: `cnode(catom ft3, cnode(catom ft4, cnode(encCodeTm(checkCG4), encLiftCode(fold(witness)))))`
   - `encCodeTm(checkCG4)` is a FIXED constant (compute once)
   - `encLiftCode(fold(witness))` is computed by `encLiftCodeTm` from GuardChecker.agda
5. Compare with the provided formula_enc using ctEqCode
6. If match: return the formula. If not: return catom 0.

**All other trust tags**: return `ctAtom zero` (always fail).

### Step 2: Modify encProofTA3 for axExEval

In TreeArithBootstrap (or locally), change:
```agda
encProofTA3 (axExEval chk c r f eq) =
  cnode (catom tagEvalEq) (cnode c (encFormTA3 (fexTA3 (feqTA3 chk (liftCode r)))))
```

The witness code `c` is now included in the encoding.

### Step 3: Prove foldCorrectG4

Reprove the checker correctness theorem for checkCG4. The structure
mirrors foldCorrectG2 from GuardFull:

- Axiom cases (K, S, refl, etc.): `refl` (same as foldCorrectG2)
- mp case: same as foldCorrectG2-mp (uses mpConverge pattern)
- gen case: same as foldCorrectG2-gen
- inst case: same as foldCorrectG2-inst
- axExEval case: NEW — must show the genuine handler produces the
  correct formula when the witness is a valid proof code.
  Uses `encLiftCorrect` from GuardChecker.agda.

### Step 4: Prove foldEnvIndep for checkCG4

Same approach as GuardFull's foldEnvIndep:
- Define FVB certificate for the new ncG4
- Apply evalCT-local / foldCT-local

The new genuine handler for tagEvalEq may use more variables than
hTrust (which only used v2). The FVB certificate needs updating.

### Step 5: Define ProvG4 and prove D1

```agda
ProvG4 : FormTA3 -> FormTA3
ProvG4 A = fexTA3 (feqTA3 checkCG4 (liftCode (encFormTA3 A)))

d1G4 : ProofG4 A -> ProofG4 (ProvG4 A)
```

D1 uses `checkerConvergeG4` (analogous to checkerConvergeG2) +
`liftCodeConv` from GuardG3.

### Step 6: Prove D2

Use the same semantic approach as GuardG3:
1. Extract witnesses from ProvG4(A->B) and ProvG4(A)
2. foldEnvIndep transfers convergence to mp fold env
3. mpConverge (adapted for checkCG4) gives fold convergence of mp witness
4. liftCodeConv gives convergence of liftCode enc(B)
5. Combine

### Step 7: Prove D3

D3: ProvG4(A) -> ProvG4(ProvG4(A))

Given code c1 with checker(c1) converging to enc(A), construct c2 with
checker(c2) converging to enc(ProvG4(A)).

The witness c2 = cnode(catom tagEvalEq, cnode(c1, encFormTA3(ProvG4(A)))).

The genuine tagEvalEq handler:
1. Recursively folds c1, getting enc(A)
2. Constructs enc(ProvG4(A)) from enc(A) using encLiftCodeTm
3. Compares with the provided encFormTA3(ProvG4(A))
4. They match! Returns the formula.

So the checker on c2 returns enc(ProvG4(A)). This is the D3 witness.

The proof needs:
- Checker convergence for c2 (from convergence of c1 + encLiftCorrect)
- foldEnvIndep to transfer convergence
- liftCodeConv for the RHS

### Step 8: Verify ProvG4(bot) is NOT satisfiable

Under convergence semantics:
- catom witnesses: checkerOnCatom rules them out (checker returns catom 0)
- cnode(tagEvalEq, cnode(witness, enc(bot))): the genuine handler checks
  fold(witness) and constructs enc(ProvG4(A)) from it. For this to equal
  enc(bot), we'd need enc(ProvG4(A)) = enc(bot) = catom n110t. But
  enc(ProvG4(A)) is always a cnode (it's an fexTA3 formula encoding).
  So the handler comparison via ctEqCode fails, returning catom 0.
- cnode(otherTag, ...): all other trust tags return catom 0. Genuine
  tags (K, S, mp, etc.) return formula encodings that are NOT enc(bot)
  for any valid proof (since bot is not provable in a consistent system).

### Step 9: Assemble Godel II

```agda
godel2G4 : ProofG4 ConG4 -> EmptyTA
godel2G4 = loeb-godel2 (record { ... d1 = d1G4 ; d2 = d2G4 ; d3 = d3G4 ; consistent = conG4 })
```

## Key technical details

### Variable positions in ncG4's atom branch (bound 5)
- v0 = tag atom value (from ctCase on left child)
- v1 = left child of proof code (= catom tag)
- v2 = right child of proof code (= payload)
- v3 = fold(left) = catom 0
- v4 = fold(right) = fold(payload)

### For the genuine tagEvalEq handler
The payload is cnode(witness, formula_enc). So:
- v4 = fold(cnode(witness, formula_enc))

By the node branch of ncG4 (returns cnode(fold(left), fold(right))):
- v4 = cnode(fold(witness), fold(formula_enc))

The handler does ctCase on v4:
- atom: fail (catom 0)
- node: new v0 = fold(witness), new v1 = fold(formula_enc)
  Then: apply encLiftCodeTm fold to v0 to get encLift(fold(witness))
  Construct: cnode(catom ft3, cnode(catom ft4, cnode(ENC_CHK, encLift_result)))
  Compare with formula from payload (extract via ctCase on v2)
  If equal (ctEqCode): return formula
  If not: catom 0

### encCodeTm(checkCG4) — the fixed constant
This is a Code value: encCodeTm(ctFold (ctVar 0) acG4 ncG4).
Compute it once at the meta level and embed as a sequence of ctAtom/ctNode.
It's large but fixed.

### Fuel accounting
Use the same pattern as foldCorrectG2:
- proofFuelG4(p) = addB n30cG4 (proofExtraG4 p)
- n30cG4 needs to be large enough for the ncG4 dispatch (including the
  genuine tagEvalEq handler + encLiftCodeTm fold)
- Estimate: n30cG4 ~ 200 (the encLiftCodeTm fold adds overhead per
  sub-code of the witness result)

## Constraints

- Zero postulates
- Zero holes
- `{-# OPTIONS --without-K --exact-split #-}`
- ASCII only, LLMPrelude conventions
- All files must compile

## Estimated size

- New checker definition (ncG4, checkCG4): ~80 lines
- New proof encoding (encProofG4): ~40 lines
- foldCorrectG4: ~300 lines (most cases refl, axExEval case uses encLiftCorrect)
- foldEnvIndep for checkCG4: ~150 lines (FVB certificate for ncG4)
- D1, D2, D3 under convergence: ~100 lines each
- Godel sentence + assembly: ~50 lines
- Total: ~900 lines

## Bottom line

The pieces exist:
- mpConverge (mp representability) ✓
- foldEnvIndep (env locality) ✓
- encLiftCorrect (self-encoding fold) ✓
- convergence semantics (GoodG3) ✓
- D2 semantic proof pattern (GuardG3) ✓

What remains is INTEGRATION: threading encLiftCodeTm through a genuine
tagEvalEq handler in a new checker, reproving foldCorrect, and
assembling D1/D2/D3/Godel II on top.

This is Guard's Theorem 12 (representability) + Theorem 14 (Godel II)
for binary trees.
