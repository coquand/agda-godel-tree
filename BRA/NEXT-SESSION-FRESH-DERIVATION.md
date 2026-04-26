# Next session: fresh derivation of Goedel II from Guard's argument

**Recommended for a fresh session.**  This session (2026-04-26)
ended with the user observing that prior reasoning had been
misled by Hilbert-Bernays-Löb-shaped framings, while Guard's
actual argument lives in quantifier-free BRA with universal-
closure semantics throughout.  Continuation in the same session
risks re-anchoring on those framings; a fresh session has a
better chance of producing a clean re-derivation.

## The prompt

> **Re-derive Guard's Theorem 14 (guard15.pdf pp.15-17) from
> scratch**, working in quantifier-free BRA with universal-closure
> semantics (free variables = implicitly universally quantified;
> `Deriv P` for P with x free means BRA proves the universal closure).
>
> Use only:
> - **`encode`** (existence of Tree witnesses for any `Deriv P`).
> - **The diagonal lemma at the meta level** (already in
>   `BRA/Thm11Diagonal.agda`; works for any tree y).
> - **BRA's substitution rule (`ruleInst`)** at any Term substituent.
> - **Standard structural rules**: `axEqTrans`, `axEqCong*`,
>   `axContrapos`, `mp`, `axRefl`, `ruleSym`.
> - **The closed-input dispatch lemmas already in `BRA/Thm/ThmT.agda`**
>   (`thmTDispRuleInst`, `thmTDispMp`, etc.) — these handle thmT on
>   closed reified-Tree witnesses.
> - **Safe-default versions** of `mp_codeF2`, `sb`, `ax`, `ind`
>   (per `BRA/AUX-SAFE-DEFAULTS.md` — required regardless).
>
> **Do not** assume you need parametric defining equations of
> `thmT` on open Term variables.  If you find you need them, that's
> a finding worth reporting.  If you find you don't (e.g., because
> universal-closure semantics + ruleInst at closed witnesses
> + meta-existential extraction does the job), then the corrected-
> thmT rebuild plan in `BRA/THMT-CORRECTED-DESIGN.md` can be
> discarded as unnecessary.
>
> **Ignore** `BRA/THMT-CORRECTED-DESIGN.md`,
> `BRA/THMT-EQUATIONS.md`, and `BRA/THM14-STEP4-OBSTRUCTION.md` on
> a first pass — don't read them until after you've worked out the
> derivation independently.  Then compare.
>
> **Output**: a step-by-step *informal* derivation of
> `Deriv Con → Deriv bot`, mirroring Guard's argument's structure,
> with each step annotated by which BRA-internal mechanism justifies
> it.  No code first.  Identify exactly where (if anywhere) thmT
> needs to be reasoned about parametrically in an open Term variable.

## Why this framing

Guard's argument structure (re-read carefully in 2026-04-26 session):

  1. Step 4 invokes Definition 12 line 2 of th, "by the definition
     of j".  Whether this needs thmT to admit a parametric
     defining equation in BRA, or whether it can be done via
     meta-existential extraction (encode at a specific closed
     witness) plus universal-closure semantics, was the unresolved
     question.

  2. Universal-closure semantics: in Hilbert-style BRA, `Deriv P`
     with x free *is* the universal closure.  ruleInst on this
     derivation at any specific Term gives the closed instance.
     We may have been over-formalising by treating step 5 as a
     `Deriv (A imp B)` (an internal implication) when in Guard's
     setup it might just be a `Deriv` of the implication-shaped
     formula with x universally closed — same thing semantically,
     but the proof structure differs.

  3. The Hilbert-Bernays-Löb framework explicitly builds machinery
     for talking about provability internally (the `Pr(.)`
     predicate, with its three derivability conditions).  Guard
     does NOT use this framework — he uses `th` (an enumeration
     functor) directly, and reasons about `th(k) = code(P)` for
     specific k extracted via meta-existential.

## What's preserved across the session boundary

Independent of which formulation wins:

  * `BRA/Sb.agda` — `sb : Fun2` and `sbDef`.
  * `BRA/SbAxiom.agda` — bridge sb to outRuleInst via codeCommutesFormula.
  * `BRA/AUX-SAFE-DEFAULTS.md` — safe-default obligation; required
    regardless of formulation.
  * `BRA/Thm/ThmT.agda` (9000 LoC) — concrete thmT and 40 closed-input
    dispatch lemmas.  Keep intact.
  * `BRA/Thm14Abstract.agda` — abstract chain contract (currently
    Term-parametric form).  May be reformulated by the fresh
    session, but the existing form is committed and recoverable.
  * `BRA/Thm/Parts/RuleInst.agda` — `encRuleInst`, `outRuleInst`.
  * `BRA/Thm11Diagonal.agda` — diagonal lemma; meta-level, works for
    any tree.

## Stop conditions for the fresh session

If the fresh derivation discovers:

(a) **No parametric defining equations of thmT on open Term
    variables are needed**: discard the corrected-thmT design;
    proceed with the simpler implementation using existing thmT +
    closed-input dispatch lemmas + safe-default auxiliaries +
    meta-existential closure mechanism.  Implementation cost drops
    significantly.

(b) **Parametric defining equations are genuinely needed (or
    something equivalent)**: revisit the corrected-thmT design or
    document what's needed precisely.

(c) **The argument requires a rule that's not in BRA's primitives**:
    stop and report; that's a foundation question, not an
    implementation one.

## How to use this doc

Start the fresh session with the **prompt** at the top of this file
verbatim.  Do not give the fresh session access to
`BRA/THMT-CORRECTED-DESIGN.md` or the obstruction reports.  Let it
work out Guard's argument independently first.  Then have it compare
its derivation to the existing artefacts and report what carries
over and what doesn't.
