# Next session: fill the single Goedel II contract (constr5 + step5)

**This document supersedes `BRA/NEXT-SESSION-GODELII-STEPS.md`** (which
proposed 3 contracts in malformed shapes; pre-flight verification
revealed the misreadings -- see `BRA/THM14-OBSTRUCTIONS.md`).

## READ THIS FIRST: pre-flight order

Before writing ANY code:

1. Read **this file** end-to-end.
2. Read `BRA/THM14-OBSTRUCTIONS.md` ("PINNED" section + refactor
   status).
3. Re-read `guard15.pdf` Theorems 12, 13, 14 (pp.15-17, including
   Definition 12 on p.16). Spend at least 15 minutes.
4. **STOP and report** if any architectural claim in this file is
   wrong against guard15.

Skip a step and the same architectural mistakes will recur.

## Status (architectural baseline post-2026-04-25 refactor)

The Goedel II chain is now mathematically honest and the closure is
done. The remaining work is to fill ONE contract:

```
constr5 : Fun1
step5   : (x : Term) ->
          Deriv ((atomic (eqn (ap1 thmT x) cG))
                  imp (atomic (eqn (ap1 thmT (ap1 constr5 x))
                                   (reify (codeFormula bot)))))
```

This is in `BRA.Thm14Abstract.Thm14.GodelII` (and re-exported from
`BRA.GoedelII.Compose`).  When filled, `godelII : Deriv Con -> Deriv
bot` is unconditional.  Concrete Goedel I (`BRA/Thm/ThmT.agda`) is
already done and unconditional; do not modify.

## PINNED lessons from prior sessions (DO NOT repeat these mistakes)

These are not optional reminders. Each lesson cost a session before it
was learned.

### Lesson 1: universal-closure semantics of  not_

In our BRA (matching Guard 1963), `Deriv P` for an open formula P
means BRA proves the **universal closure** of P. So `not_` at the
Formula level is purely **syntactic**; it does NOT lift `Deriv` to
"BRA refutes P":

  * `Deriv (not P)` for open P with free var x  =  BRA proves
    "for all x, ~P(x)" .
  * It is NOT  "BRA does not derive P"  (that's meta:
    `Deriv P -> Empty`).
  * It is NOT  "there exists x such that  Deriv (not P[x])" .

**Operational rule**: stay at the **encoded layer**. Each Guard step
is a Deriv of an internal implication between two atomic encoded
equations. Never lift to `Deriv (not P)` for open P as an intermediate.
The `~` lives only inside quotation marks (`codeFormula`).

The only legitimate `Deriv (not P)` for open P is the GOAL: G itself
("forall x_1, ~(th(x_1) = sub(i,i))"), produced at the very end of the
closure.

(Memory: `feedback_universal_closure_not.md`. Full discussion:
`BRA/THM14-OBSTRUCTIONS.md` PINNED section.)

### Lesson 2: contract shapes — internal implication, not Sigma / meta-arrow

The contract for any Thm 14 step must be of the form

```
Deriv ((atomic-eqn-using-x) imp (atomic-eqn-using-x))
```

parametric in x (typically via meta-Pi `(x : Term) -> Deriv (...)`).

**NOT** any of these (all attempted, all wrong):

  * `(x : Term) -> Deriv (P x) -> Sigma Tree (\d -> Deriv (Q x d))`
    -- Sigma form. Doesn't compose with closure's `axContrapos` (would
    need Hilbert-Bernays Deduction Theorem to bridge).
  * `(x : Term) -> Deriv (P x) -> Deriv (Q x)`
    -- Meta-arrow. Same problem.
  * `Deriv (closed_formula imp open_formula)`
    -- Asks for closed-implies-universal; Hilbert `ruleInst` doesn't
    support generalisation.

(Reference: `BRA/THM14-OBSTRUCTIONS.md` (e), (f).)

### Lesson 3: step 4 internalises substitution, NOT the diagonal

Guard p.17 step 4 reads:

> By the definition of j ,
> 4) th(x) = j ⊃ th(4J(J(num x,1),x)+1) = "th(x) != sub(i,i)"

The justification "by the definition of j" invokes **Definition 12
line 2 of th** (the substitution clause `th(4y+1) = sb(KKy, IKy,
th(Iy))`) and a primitive-recursive `sb` operation on coded formulas.

It is NOT Thm 11's diagonal lemma. Thm 11's diagonal is a META
conclusion (for any concrete y, BRA proves `not (th(y) = cG)`); step
4 is INTERNAL (substitution rule of th).

Attempting "from Deriv (PrAtX x), derive Deriv (negSubF x)" is also
wrong (would entail BRA inconsistency on any provable PrAtX -- see
Lesson 1).

(Reference: `BRA/THM14-OBSTRUCTIONS.md` (e).)

### Lesson 4: Con must be parametric

```
Con : Formula
Con = not (atomic (eqn (ap1 thmT (var zero))
                        (reify (codeFormula bot))))
```

(`var zero` free.)  The closure `ruleInst`-s Con at `constr5 (var 1)`.

A closed Con like `not (Pr bot)` (= specific instance) is too weak:
the closure cannot instantiate it at the `<final x>` witness.

(Reference: `BRA/THM14-OBSTRUCTIONS.md` (g).)

## PINNED methodology (NON-NEGOTIABLE)

These are not engineering preferences. They are signals of mathematical
correctness in this project.

  * **Small files**: ~250 LoC max per file. If a file exceeds 250 LoC,
    STOP and refactor. Slowness/size signals math mismatch, not need
    for patience.
  * **Fast typecheck**: <2s cold per file. <10s for the full chain.
    If exceeded, STOP and reformulate -- the math is doing more work
    than it should.
  * **One named lemma per Guard step**: each Guard p.16-17 step =
    one named Agda lemma, signature first, body in a few `ruleTrans`
    lines. NO monolithic let-bodies.
  * **Topical commits**: one commit per Guard sub-step or per
    coherent infrastructure piece. Use the project's
    `[BRA-<topic>] <imperative>` format.

(Memories: `feedback_guard_fast_typecheck.md`,
`feedback_one_lemma_per_paper_step.md`, `feedback_no_with_agda.md`,
`feedback_eqcong_not_with.md`.)

## What's left to fill

Guard's step 5 (p.17 line 5) is built from steps 1-4 + Definition 12
mp/sb clauses. Translating each to BRA Agda:

| Sub-step | Mechanism | Status |
|---|---|---|
| Step 1: `th(x)=j ⊃ th(Dth(x))="th(x)=j"` | Thm 13 in internal-implication form | Need: port Thm12Abstract / Thm13Abstract from Sigma to internal-implication form (constructions as Fun1) |
| Step 2: `th(Dsub(i,i))="sub(i,i)=j"` (closed) | Thm 13 closed instance | Same as above |
| Step 3: `th(x)=j ⊃ th(g(x))="th(x)=sub(i,i)"` | internal eq-trans on 1+2 | Mechanical once 1+2 done |
| Step 4: `th(x)=j ⊃ th(<sub-construction>(x))="neg(th(x)=sub(i,i))"` | **Internalise Definition 12 line 2 (sb on coded formulas)** | **Major: needs `sb` PR function + `axThmTSub` axiom + computational lemma. Multi-file subproject.** |
| Step 5: `th(x)=j ⊃ th(<mp-construction>(x))="0=1"` | Internal ex-falso via Definition 12 line 3 (mp encoding) | Same-shape work for mp clause: `mp_enc` + `axThmTMp` |

Realistic scope: ~1500-2000 LoC across 3-5 sessions, dominated by
sb / mp-clause internalisation. Per-file budget ~250 LoC.

## Recommended FIRST step for next session

**Investigation, not implementation.** Spend ~30 min reading
`BRA/Thm/ThmT.agda`'s structure to determine whether `thmT`'s defining
clauses already contain Definition 12's `mp` and `sb` cases (Guard's
`4y+1` and `4y+2` clauses) as accessible axioms.

Possible outcomes:

  1. **Shortcut exists**: `axThmTSub` and `axThmTMp` can be extracted
     as specialisations of existing `BRA/Deriv.agda` axioms applied
     to `thmT`'s structure. 1-2 session win.
  2. **No shortcut**: must build sb / mp internalisation as new
     infrastructure (multi-file subproject).

Output of the investigation: `BRA/THM14-NEXT-INVESTIGATION.md` (new
file, ~100 LoC of analysis, 0 LoC of code) with findings + concrete
plan for the substantive work.

Do this investigation BEFORE committing to either path. The full
substantive work spans multiple sessions either way; one focused
investigation session de-risks the rest.

## Strategic options (after the investigation)

In order of methodological alignment with the small-files / fast-
typecheck principle:

  1. **Find a shortcut** (investigation outcome 1). Highest payoff.
  2. **Build sb + mp as ground axioms over thmT** if outcome 2 but
     the axioms can be added at the `BRA/Deriv.agda` level (per
     `feedback_ground_axioms_ok.md`, ground defining-equation axioms
     are fine). ~500 LoC subproject.
  3. **Build full sb / Definition 12 mechanisation as a subproject**
     (BRA/Sb.agda + computational lemmas + axiom). ~1500 LoC.
  4. **Ship the abstract chain as-is**. The current state ("Goedel
     II in BRA reduces to filling this single contract, parametric in
     constr5 + step5") is itself a valid deliverable.

## Pre-flight verification (mandatory first action)

Open guard15.pdf, read **Theorems 12, 13, and 14** (pp.15-17,
including Definition 12 on p.16), and confirm:

(a) Hypothesis of every Thm 14 step is `th(x) = j` where j = code G.
(b) Conclusion of every step is `th(...) = "..."` (encoded equation,
    NOT a `Deriv (not P)` for open P).
(c) Step 4's "by the definition of j" justification is Definition
    12 line 2 (sb clause), not Thm 11's diagonal.
(d) Closure (p.17 last paragraph) uses contrapose of step 5 + Con
    parametric in y + ruleInst, NOT a `~Pr(G) → G` direction.

If any answer is "no" or unclear, STOP and report. The plan in this
document depends on these readings being correct.

## Constraints (do not violate)

  * `--safe --without-K --exact-split`, ASCII only, low-mixfix prelude.
  * No new postulates.
  * No reproof of Thm 11 (`BRA/Thm/ThmT.agda`); use it via `encode`
    (and `thmT` defining axioms in `BRA/Deriv.agda`).
  * No new Deriv-level reflection axioms (per
    `feedback_no_new_deriv_axioms.md`); ground defining-equation axioms
    are OK (per `feedback_ground_axioms_ok.md`).
  * Run `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split <file>`
    to typecheck.

## Stop conditions (in priority order)

  1. **Pre-flight verification fails**: re-reading guard15.pdf
     reveals a claim in this doc is wrong. Stop and report.
  2. **Single file > 250 LoC OR single lemma body > 50 lines OR
     typecheck > 2s cold per file**. Indicates wrong abstraction
     granularity. Stop and refactor.
  3. **A step seems to need new BRA-foundation reflection axioms**
     (general universally-quantified rules, not ground defining
     equations). Stop and report -- the encode-based approach has a
     gap.
  4. **Universal-closure trap**: about to write a contract using
     `Deriv (not P)` for open P or Sigma form or closed Con. Stop
     and re-read Lessons 1-4 above.

## Files this session writes (estimate)

  * `BRA/THM14-NEXT-INVESTIGATION.md` (new) -- investigation report.

If outcome 2 (no shortcut), subsequent sessions write:

  * `BRA/Sb.agda` (new) -- `sb` PR function on coded formulas.
  * `BRA/SbAxiom.agda` (new) -- `axThmTSub` axiom + computational lemma.
  * `BRA/MpEnc.agda` (new) -- `mp_enc` PR function + `axThmTMp`.
  * `BRA/Thm14Step1.agda` -- internal Thm 13 specialised.
  * `BRA/Thm14Step2.agda` -- internal Thm 13 closed instance.
  * `BRA/Thm14Step3Int.agda` -- internal-implication step 3 (replaces
    Sigma `Thm14Step3.agda`).
  * `BRA/Thm14Step4.agda` -- internal step 4 using sb.
  * `BRA/Thm14Step5.agda` -- internal step 5 combining + mp_enc.
  * `BRA/Thm14ConstructStep5.agda` -- `constr5` + the chained Deriv,
    plugging into `BRA.GoedelII.Compose`.

Each ~150-250 LoC, <2s cold typecheck. If any exceeds budget, STOP
and refactor.

## Files this session does NOT write or modify

  * `BRA/Thm/ThmT.agda` -- stable, 9000 LoC, contains concrete Thm 11.
  * `BRA/Thm14CodeFTeq.agda` -- final.
  * `BRA/Thm14Abstract.agda` -- final (already in honest internal-
    implication form).
  * `BRA/GoedelII.agda` -- final EXCEPT for the `Compose` instantiation
    once `constr5` + `step5` are filled.
  * `BRA/Cor.agda`, `BRA/Sub.agda`, `BRA/SubT.agda`, `BRA/Mp.agda` --
    foundation, do not modify.
  * `BRA/Thm11Diagonal.agda` -- final (G_norm moved out of abstract
    block in 2026-04-25 refactor; do not move back in).

## Recommended commit messages

  * `[BRA-godelII-investigate]` -- investigation report.
  * `[BRA-godelII-sb-infra]` -- sb function + axThmTSub.
  * `[BRA-godelII-mp-enc]` -- mp_enc + axThmTMp.
  * `[BRA-godelII-step-N]` -- per Guard step.
  * `[BRA-godelII-constr5]` -- final plug-in.

## What success looks like

  * Realistic (multi-session): investigation done, sb + mp infrastructure
    built, steps 1-3 done as internal implications. ~1500 LoC, 3-4
    sessions. Goedel II still parametric over the final step5
    plug-in.

  * Aspirational (full mechanisation): all infrastructure + all steps,
    `constr5` + `step5` filled, `godelII` unconditional. ~5 sessions
    if no shortcut, ~2 if shortcut found.

The session's primary deliverable: **either concrete progress or a
crisp investigation report**. Both are valuable; per the methodology
principle, the investigation alone (if it lands at outcome 2) is
worth more than a hasty start on outcome 3 work.
