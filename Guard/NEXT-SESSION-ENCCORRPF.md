# Next Session: encCorrPf — second-order reflection

## Command

From `/Users/coquand/CHWISTEK`:

```
claude
```

Then paste the prompt below.

## Prompt

```
Read Guard/NEXT-SESSION-ENCCORRPF.md and Guard/NEXT-SESSION-PHI-PATH.md, then proceed.

Goal: tackle encCorrPf — the load-bearing second-order reflection
encoder.  This is the only remaining piece needed before classical
Gödel II closes via Guard/GodelIIClassicalSkel.agda.

This is DESIGN work, not mechanical porting.  The previous session
finished all 27 mechanical axiom/rule encoders in Guard/ProofEnc.agda;
encCorrPf is the genuinely novel piece.

The question: given a polymorphic d-dependent Deriv  corrPf : Deriv hyp
(eqn (ap1 (thmT trivCT) enc) (reify cGSCR))  where  enc = encT (thm14EV3 d),
construct a Term  encCorrPf v0  such that for any hyp,
  Deriv hyp (eqn (ap1 (thmT trivCT) (encCorrPf v0))
                 (reify (codeEqn (eqn (ap1 (thmT trivCT) v0) (reify cGSCR)))))
i.e. an encoded self-applicative reflection of corrPf with v0 abstracted
in place of enc.

Approach (per NEXT-SESSION-PHI-PATH.md):
  Investigate whether the meta-reflection pattern from EncSelfEq.agda
  (encT ∘ thm14EV3 packaging closed sub-derivations) extends to the
  d-dependent case by parameterising thm14EV3 over a hypothetical d.

Start by running:
  ~/.cabal/bin/agda-2.9.0 Guard/EncSelfEq.agda
  ~/.cabal/bin/agda-2.9.0 Guard/GodelIIClassicalSkel.agda
  ~/.cabal/bin/agda-2.9.0 Guard/ProofEnc.agda
All should compile under 1s with no output.

Reference files:
  - Guard/GodelIClassical.agda — see godelIClassical's body, find
    corrPf at line ~148 (depends on d via thm14EV3 d ; encT pe).
  - Guard/EncSelfEq.agda — proof-of-concept that closed sub-derivations
    package via encT ∘ thm14EV3 in 3 lines.
  - Guard/ProofEnc.agda — 27 encoders ready to use as building blocks.
  - Guard/Thm14EV3.agda — has thm14EV3* functions per Deriv constructor.
  - Guard/GodelIIClassicalSkel.agda — the parametric module that
    consumes Phi + strongPhiCorr.  Once encCorrPf exists, Phi can be
    built using the encoders + encCorrPf, and strongPhiCorr becomes
    derivable.

Use ~/.cabal/bin/agda-2.9.0 (NOT /opt/homebrew/bin/agda).
Conventions: --safe --without-K --exact-split.
No postulates, no holes.  Each file under 10s.
Object-level implication is FORBIDDEN — only meta-level Agda arrow
(polymorphic Deriv hyp A → Deriv hyp B).  IfLf is permitted (it is an
existing Fun2 primitive).
Commit and push after each file compiles clean.

If approach (parameterise thm14EV3 over hypothetical d) is provably
intractable, document why in a markdown file (mirror the
StrongPhiCorrAnalysis.agda style) and suggest fall-backs.

Proceed autonomously.
```

## Why a fresh session

The prior session was mechanical porting (mostly copy-from-Thm14EV3 +
fix paren counts).  encCorrPf is qualitatively different:

1. It is a SECOND-ORDER reflection — encoding the result of running
   thm14EV3 itself, not just one Deriv constructor.
2. The "right" encoding may require new infrastructure (e.g. a
   self-applicative thm14EV3 variant, or a different Phi shape).
3. It may turn out to be intractable at the Term level, in which case
   the answer is a different architectural decision (e.g. accept
   encCorrPf as a module parameter; redesign the diagonal).

Fresh context is helpful because the model can re-read the relevant
files with fresh eyes and consider alternative encodings the prior
session may have implicitly ruled out.

## What "done" looks like

  Guard/EncCorrPf.agda — defines encCorrPf : Term -> Term and proves
  encCorrPfCorr : (v0 : Term) {hyp : Equation} ->
    Deriv hyp (eqn (ap1 (thmT trivCT) (encCorrPf v0))
                   (reify (codeEqn (eqn (ap1 (thmT trivCT) v0) (reify cGSCR)))))
  Compiles under 10s, no postulates, no holes.

Then a follow-up file Guard/PhiBuild.agda assembles Phi using the
encoders + encCorrPf, derives strongPhiCorr, and instantiates
WithPhi from GodelIIClassicalSkel to obtain  godelIIClassical .

## Current state (commit a1ef28d)

- 27/28 encoders complete in Guard/ProofEnc.agda (2521 lines, 0.17s).
- Guard/StrongPhiCorrAnalysis.agda documents intractability of approach (C).
- Guard/EncSelfEq.agda demonstrates the closed-sub-derivation pattern.
- Guard/GodelIIClassicalSkel.agda waits for Phi + strongPhiCorr.
