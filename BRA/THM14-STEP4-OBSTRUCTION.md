# Thm 14 step 4 obstruction: parametric thmT-substitution dispatch

Session date: 2026-04-25.  Branch: `main`.

This note documents an obstruction to filling step 4 of Goedel II
(BRA `Thm14Abstract`) **after**  `BRA/Sb.agda`  and  `BRA/SbAxiom.agda`
were completed.  Both Sb files are correct and stable; the obstruction
is at the next layer (linking `thmT` to `sb` parametrically).

Per `BRA/NEXT-SESSION-GODELII-V3.md` stop condition #4
("step 4 needs general reflection axioms — stop and report"), this
file is the report.

## Summary

* `BRA/Sb.agda` (done): `sb : Fun2` with closed-input defining
  equation `sbDef`.  No issues.
* `BRA/SbAxiom.agda` (done): closed-input bridge
  `sbForOutRuleInst`.  No issues.
* **Step 4 (next): blocked**.  Requires either (a) a parametric
  ground axiom in `BRA/Deriv.agda` for `thmT`'s substitution-rule
  defining equation, or (b) a different architectural strategy.
  Neither is unambiguously sanctioned by current project methodology.

## What step 4 requires

Step 4 of Goedel II must be proved **parametric in a Term variable**
`x : Term`, because Goedel II's closure (in
`BRA.Thm14Abstract.Thm14.GodelII.closureToG`) does:

  `ruleInst Con` at the witness term `constr5 (var 1)`  →  closure.

So step 5 (which depends on step 4) must be a Deriv parametric in
`x : Term` (the meta-Pi shape was correctly identified in V2).
For any specific `x` (in particular `x = var 1`), we must derive

  `Deriv ((atomic (eqn (ap1 thmT x) cG)) imp
          (atomic (eqn (ap1 thmT (subProofEnc x)) ...)))`

where `subProofEnc : Term -> Term` is BRA's analog of Guard's
`4J(J(num x, 1), x) + 1`:

```
subProofEnc x
  = ap2 Pair tagRuleInstT
            (ap2 Pair varCode1T
                      (ap2 Pair x (ap1 cor x))) .
```

Discharging the consequent requires reducing `ap1 thmT (subProofEnc x)`
to a form involving `ap1 thmT x` (so that the antecedent's
`thmT x = cG` can be applied via `congR`).

## Why Option B (no new axiom) is blocked

`thmT = Rec O stepProto` (in `BRA.Thm.ThmT`).  Reducing
`thmT (subProofEnc x)` proceeds via:

1. `axRecNd` unfolds `thmT` on the OUTER `Pair tagRuleInstT inner` —
   works for any Term children.  Dispatches via `stepProto`.
2. `stepProto`'s IfLf cascade matches `tagRuleInst` on the closed
   `tagRuleInstT` — works.
3. `body_ruleInst` extracts components from
   `bb = Pair (thmT tagRuleInstT) (thmT inner)` , in particular
   `tjH = ap1 thmT x` from inside `bb`.  This requires
   `Snd bb = Pair tjV (Pair tjH tjT)` , i.e., **`thmT inner` must
   distribute over its inner Pair structure**.

It is step 3 that blocks parametrically.  `thmTDistrib` (line 7217 of
`BRA/Thm/ThmT.agda`) provides this distribution but **requires a
shape hypothesis**:

  `Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair x' y_h')))`

For closed `y_h` this comes from `fstReifyCodeF2` etc.  For an open
Term variable `x` substituted for `reify y_h`:

  `ap1 Fst x` does NOT reduce.

There is no Deriv inhabitant of `(ap1 Fst x = Pair x' y')` for an
arbitrary open `x` (and no project-level rule supplying one).

The same obstacle appears one level deeper: even if we could push
through the outer level, the inner `Pair x (ap1 cor x)` needs a shape
proof on `Fst (Fst (Pair x cor_x)) = Fst x` , which again does not
reduce.

**Conclusion**: existing infrastructure (axRecNd, stepProto_else,
thmTDistrib, body_ruleInst_eval) only proves the substitution-rule
defining equation of thmT for **closed** `y_h = reify someTree`.
Parametric (open-x) form is not derivable.

## What Option A would look like

A clean ground defining-equation axiom for `thmT`'s substitution-
rule clause, parametric in the proof-position Term `x`:

```
axThmTSubRule : (x : Term) ->
  Deriv (atomic (eqn
    (ap1 thmT (subProofEnc x))
    (ap2 sb (ap2 Pair (ap1 cor x) (reify (natCode (suc zero))))
            (ap1 thmT x))))
```

Shape-wise it is identical to `axRecLf` / `axFan` / `axComp` etc. —
parametric in Term variables, no premise, defining equation of a
specific construction.  Mathematically it is exactly Guard's
Definition 12 line 2 of `th` (`th(4y+1) = sb(KKy, IKy, th(Iy))`)
parametrised at proof-position `y = x`.

### Pros

  * Matches Guard's definitional structure literally.
  * Same shape as existing project axioms (axRecLf, axFan, …).
  * Discharges step 4 in 5–10 lines after definition.
  * No "general reflection rule" pattern (no `Deriv P -> Deriv (...)`
    premise; just a parametric equation).

### Cons

  * Modifies `BRA/Deriv.agda`'s constructor list — a foundation
    modification.  All downstream files inherit the new axiom.
  * Bypasses the fact that `thmT`'s body computes the equation
    constructively for closed inputs.  In effect, it's an axiom
    capturing **what the body would compute** if BRA's term-rewriting
    extended to open inputs.
  * Layering: `Deriv.agda` would need to depend on `subProofEnc`,
    `cor`, `sb` definitions, all of which currently live above it.
    Workaround: state the axiom abstractly (over a chosen subEnc),
    or move it into a new file like `BRA/Deriv2.agda` that imports
    `BRA.Term + BRA.Sb + BRA.Cor`.
  * Borderline: the boundary between "ground defining equation" and
    "general reflection axiom" is judgment-dependent.  Project
    feedback memos sanction the former and forbid the latter.  This
    case sits near the boundary.

## Other options considered and rejected

* **Option C (Schema F / ruleIndBT)**: induction on `x` doesn't apply.
  Step 4's content is a direct consequence of Definition 12 line 2,
  not an inductive statement.
* **Stating step 5 closed-form, lifting via universal closure**: same
  blocker — step 5 must be parametric in x for the closure to ruleInst.
* **Defining `subProofEnc`-like construction via different combinators
  that DO reduce parametrically**: would require building thmT-on-open
  reduction into the construction itself, which is contradictory
  with thmT being dispatch-based.

## Recommended next step

This is a decision point that warrants user input rather than a
unilateral choice in-session.  Two viable paths:

1. **Add `axThmTSubRule` to `BRA/Deriv.agda`** as a ground defining
   equation (Option A), justified by Guard Definition 12 line 2.
   Also add `axThmTMpRule` (analogous) for the mp clause.  Then steps
   1–5 fill mechanically.  Net foundation cost: 2 new constructors.

2. **Re-architect to closed-form-only step 5**, deriving the closure
   via a different mechanism that doesn't require parametric step 5.
   This is a research direction; design effort is not estimable
   from current state.

Path 1 is the V2 plan's intended route (it explicitly anticipated an
`axThmTSub` axiom; it just hadn't yet investigated the precise shape).
Path 2 is open.

## What is shippable as-is

`BRA/Sb.agda` and `BRA/SbAxiom.agda` are correct, well-tested,
well-documented, and reusable independent of which path is chosen.
They do not depend on the resolution of this obstruction.

`BRA/NEXT-SESSION-GODELII-V3.md` and this file together capture the
state of the investigation at the end of the session.
