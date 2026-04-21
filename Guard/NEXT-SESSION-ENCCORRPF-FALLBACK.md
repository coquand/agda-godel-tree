# Next Session: encCorrPf fall-back (approach A)

## Outcome of the meta-reflection exploration

**The meta-reflection approach to `encCorrPf` (parameterising
`thm14EV3` over a hypothetical `d`) is intractable under the project's
no-postulates / no-holes discipline.**

See `Guard/EncCorrPfAnalysis.agda` (compiled, under 0.2s) for the
formal documentation.  It proves the conditional

```
encCorrPfFromTemplate : MissingTemplateDeriv -> EncCorrPfSpec
```

where `MissingTemplateDeriv` is a specific `Deriv Triv` of the
template equation `ap1 (thmT trivCT) (var 0) = reify cGSCR`.  The
conditional compiles clean and demonstrates that **the only missing
ingredient is this template derivation**.

The obstruction: `Triv` (= `eqn O O`) does not prove the template
equation.  `ap1 (thmT trivCT) (var 0)` is stuck (no axRec-axiom fires
on a free variable), and no axiom / ruleF / congruence chain can
bridge the stuck term to the closed reified `cGSCR`.  Choosing a
different ambient hypothesis (e.g. `H = template`) makes `ruleHyp`
work but produces the wrong `hCode` (`reify (codeEqn H)` instead of
`trivCT`), which the spec forbids.

## Recommendation: approach (A) --- inline the encoder chain into Phi

Rather than building a standalone `encCorrPf` and feeding it into the
Skel's `Phi`, construct Phi directly using the 27 existing encoders
in `Guard.ProofEnc`.  **Phi is the encoded form of
godelIClassical's derivation**, treating `v0` as the hypothetical
proof encoding.

### Concrete plan

godelIClassical's derivation chains:

```
godelIClassical d = ruleTrans (ruleSym selfEq) stepB
  where
  pe      = thm14EV3 d              -- depends on d
  enc     = encT pe                 -- depends on d
  corrPf  = ...uses corr pe...      -- depends on d
  d1Conv  = ...uses ruleInst d...   -- depends on d
  stepA   = ruleTrans (ruleSym (congL TreeEq rhsT corrPf)) d1Conv
  stepB   = ruleTrans (ruleSym (congR TreeEq (reify cGSCR) diagFTargetCR)) stepA
  selfEq  = treeEqSelf (reify cGSCR)   -- closed
  diagFTargetCR = ...                  -- closed
```

Mapping to encoded combinators:

| Derivation piece          | Encoded form                                                   | Dependency         |
| ------------------------- | -------------------------------------------------------------- | ------------------ |
| `selfEq`                  | `encSelfEq` (already done in `Guard/EncSelfEq.agda`)           | Closed             |
| `diagFTargetCR`           | `encDiagFTargetCR` (closed -- use `thm14EV3` meta-reflection)  | Closed             |
| `corrPf`                  | *requires `encCorrPf`* -- use ruleInst + encSubstOp trick      | v0-dependent       |
| `d1Conv`                  | `encRuleInst (Pair (reify (code v0)) (reify (natCode 0))) v0`  | v0-dependent       |
| `congL TreeEq rhsT`       | `encCongL TreeEq (reify (code rhsT))`                          | wraps v0-part      |
| `ruleSym`                 | `encRuleSym`                                                   | wraps v0-part      |
| `congR TreeEq (reify cGSCR)` | `encCongR TreeEq (reify (code (reify cGSCR)))`             | wraps closed       |
| `ruleTrans`               | `encRuleTrans`                                                 | combines both      |

### The crux: `encCorrPf` redux

Even with inlined Phi, we still need the `corrPf` internalisation.
However, the inlined version has TWO advantages over a standalone
`encCorrPf`:

1. **Phi is a single Fun1** (e.g. `Comp (chain of Comps) I`), so it can
   be a flat composition of encoded primitives, not requiring a
   separate Deriv derivation.
2. **strongPhiCorr becomes a direct ruleTrans chain** over the
   combinator correctness lemmas (`encRuleSymCorr`,
   `encRuleTransCorr`, etc.), each of which is already available and
   mechanical.

The key insight: instead of constructing an ENCODED DERIVATION of
`ap1 (thmT trivCT) v0 = reify cGSCR` (which requires
`MissingTemplateDeriv`), Phi constructs an ENCODED DERIVATION of
`trueT = falseT` directly, exploiting the assumption that `v0`
encodes a gsCR-proof only via structural combinators.  If `v0` is
invalid, the encoded derivation is garbage but `thmT trivCT` of it
still reduces to SOMETHING, and we verify strongPhiCorr holds case-
by-case via TreeEq's axioms.

### Size estimate

~500-1000 lines.  The bulk is mechanical combinator application plus
Fun2 dispatch code.  The subtle parts are:

- Ensuring Phi's `dispMiss` passthroughs compose cleanly (each sub-
  encoding's tag must not match anything in outer dispatches).
- The final `strongPhiCorr` derivation uses axTreeEqNN + axIfLfL /
  axIfLfN case-analysis, not direct equality.

## Files already in place

- `Guard/GodelIIClassicalSkel.agda` (207 lines, 0.13s) -- parametric
  Gödel II given `Phi` + `strongPhiCorr`.
- `Guard/ProofEnc.agda` (2521 lines, 0.17s) -- 27/28 combinators done.
- `Guard/EncSelfEq.agda` (105 lines, 0.12s) -- meta-reflection POC.
- `Guard/StrongPhiCorrAnalysis.agda` -- approach (C) intractability.
- `Guard/EncCorrPfAnalysis.agda` (NEW, ~150 lines, 0.1s) --
  meta-reflection approach intractability for encCorrPf.

## Suggested order for the next session

1. **Write `encDiagFTargetCR`**: closed encoding of `diagFTargetCR`
   via `thm14EV3` meta-reflection (analogous to `encSelfEq`).  Should
   be ~20 lines.  Closed sub-derivation, no obstruction.

2. **Design Phi structurally**: decide Phi's Fun1 skeleton.  Options:
   - (a) `Phi = Comp (...) (Comp (...) ...)` -- flat composition.
   - (b) `Phi = Rec z s` -- recursive descent on v0.
   Option (a) is simpler if it suffices; option (b) is needed if
   diagonal awareness requires case-analysis on v0's top-level tag.

3. **Build strongPhiCorr piecewise**: for each major component of
   godelIClassical (ruleSym, ruleTrans, congL, congR, ruleInst),
   combine the corresponding encoder's `*Corr` lemma.  Chain via
   ruleTrans at the object level.

4. **Verify**: compile Phi + strongPhiCorr, instantiate the Skel's
   `WithPhi` module, produce `godelIIClassical`.

## Invariants

- Use `~/.cabal/bin/agda-2.9.0` (not `/opt/homebrew/bin/agda`).
- `--safe --without-K --exact-split`.
- **No postulates, no holes**.
- Object-level implication is FORBIDDEN (only meta-level Agda arrow
  `Deriv hyp A -> Deriv hyp B`).  `IfLf` is permitted.
- Commit and push after each file compiles clean.

## Sanity check

```
~/.cabal/bin/agda-2.9.0 Guard/EncCorrPfAnalysis.agda
~/.cabal/bin/agda-2.9.0 Guard/StrongPhiCorrAnalysis.agda
~/.cabal/bin/agda-2.9.0 Guard/EncSelfEq.agda
~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalSkel.agda
~/.cabal/bin/agda-2.9.0 Guard/ProofEnc.agda
```

All under 1s.
