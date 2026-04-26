# Next session: fresh derivation of Goedel II from Guard's argument

## THE LOAD-BEARING USER INSIGHT (read first)

> **"Guard's argument is different since the formulation is with
> formula with free variables implicitly universally quantified."**
>                                                  — user, 2026-04-26

In Guard's quantifier-free BRA:

  * **Free variables are implicitly universally quantified.**
    `Deriv P` for P with x free *means* "BRA proves the universal
    closure of P".  No internalised ∀ exists.
  * **`ruleInst` instantiates** at any specific Term: from
    `Deriv P` with x free, derive `Deriv (P[x:=t])` for any t.
  * **Step 5's "implication"** in Guard is just a BRA implication-
    formula with x free.  It is not a `Deriv (A imp B)` arising
    from internalising a meta-arrow `Deriv A → Deriv B`.  Guard
    has only the universally-closed Deriv of an implication-
    shaped formula.

This is **structurally different** from Hilbert-Bernays-Löb-style
provability logic, which builds an internalised `Pr` predicate
with three derivability conditions and reasons via internalised
implications and meta-Pi.  Guard does **none** of that machinery.

## Why this matters

Prior sessions (including the immediately preceding one,
2026-04-26) drifted into HBL-shaped framings:

  * Treating step 5 as a `Deriv (A imp B)` parametric in `var 1`,
    requiring a thmT defining equation parametric in open Term
    variables.
  * Building a corrected-thmT redesign (`BRA/THMT-CORRECTED-DESIGN.md`)
    to make those parametric defining equations derivable via `axFst`.
  * Documenting "obstructions" (`BRA/THM14-STEP4-OBSTRUCTION.md`)
    that exist only because of this framing.

If Guard's argument doesn't actually require thmT to admit
parametric defining equations on open Term variables — and if
universally-closed Derivs + ruleInst at closed witnesses suffice
— then **the obstruction is artificial and the rebuild plan is
unnecessary**.

A fresh session, started without anchoring on the corrected-thmT
framing, has the best chance of producing a clean re-derivation
that confirms or refutes this.

## Status (preserved across the session boundary)

This session (2026-04-26) ended with the user observing that
prior reasoning had been misled by Hilbert-Bernays-Löb-shaped
framings, while Guard's actual argument lives in quantifier-free
BRA with universal-closure semantics throughout.  Continuation in
the same session risks re-anchoring on those framings; a fresh
session has a better chance of producing a clean re-derivation.

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
>
> **Stopping criteria for the session**:
>
>  1. Derivation goes through using only the listed mechanisms ⟹
>     write up the derivation as a `BRA/GUARD-T14-DERIVATION.md`
>     document.  Conclude that the corrected-thmT rebuild is
>     unnecessary; only safe-default auxiliaries are needed.
>     Recommend next-session implementation plan.
>
>  2. Derivation gets stuck at a specific step that genuinely
>     needs a parametric defining equation of thmT on open Term
>     variables ⟹ document the precise step and what's missing.
>     Compare to the existing corrected-thmT design and confirm
>     or refute that it solves the gap.
>
>  3. Derivation gets stuck for a different reason ⟹ document
>     where, what would be needed, and whether that's a foundation
>     question or an implementation question.
>
> **Length**: ~1-3 hours of focused thinking, written up.  This is
> a research-and-writing session, not a coding session.  Stop
> writing when the derivation is complete *or* when a clear stuck-
> point is documented.

> **Be actively skeptical of the prior session's framings.** When
> you find yourself reaching for "internalised implication",
> "Sigma form witness", "meta-Pi over Term", "parametric defining
> equation of thmT on open variables" — pause and ask whether
> Guard actually uses that, or whether it's a HBL-shaped artifact
> from prior reasoning.

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
