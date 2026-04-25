# Next session: implement Thm 14 steps 3-5 + closureToG (concrete Gödel II)

> **!!! SUPERSEDED 2026-04-25: read `BRA/NEXT-SESSION-GODELII-V2.md` !!!**
>
> Pre-flight verification of guard15.pdf revealed THREE architectural
> misreadings in the contracts proposed below: (e) step 4 mechanism is
> sb (Definition 12 line 2), not Thm 11's diagonal; (f) Sigma /
> meta-arrow forms don't compose with the closure's axContrapos; (g)
> Con must be parametric, not closed.  See
> `BRA/THM14-OBSTRUCTIONS.md`.
>
> The chain has been REFACTORED to a single contract
> (`constr5 : Fun1` + `step5` in meta-Pi internal-implication form).
> Closure is inlined and works.  This document is left in place for
> historical context but its contract proposals are wrong; do not
> implement against them.

## Status of Gödel I in BRA (already DONE)

**Gödel I (Theorem 11) is fully proved, concrete, and unconditional**
in `BRA/Thm/ThmT.agda`. Specifically:

  * `thmT : Fun1`         — concrete provability functor.
  * `thClosed`, `codeF1Th_noVar` — refl (1-line via abstract block).
  * `encode : (P : Formula) -> Deriv P -> Sigma Tree (...)` —
    walks all 40 Deriv constructors, all dispatch lemmas concrete.
  * `thm11 : Deriv G -> Deriv bot` — unconditional (no parameters,
    no postulates, no holes).

Cold typecheck of the whole concrete-Thm-11 chain: ~5s.  Verified by
running `agda --safe --without-K --exact-split BRA/Thm/ThmT.agda`
and `grep -c "postulate\|HOLE\|TERMINATING"` returning only the
literal comment "Zero postulates, zero holes" on line 42.

Earlier confusion in the project history claimed Thm 11 was
"parametric over 30 deferred dispatches" -- that was based on stale
header comments in ThmT.agda; the actual code has all 40 dispatches
concrete.  This session does NOT touch ThmT.agda; consume it via
`encode` only.

This session is about the REMAINING piece for Gödel II: the Thm 14
chain that internalises Gödel I.

## Universal closure: a critical principle

**In Guard's BRA, every  Deriv P  means BRA proves the UNIVERSAL
CLOSURE of P.**  If P has free variables x_1, ..., x_n, then
"Deriv P" is "for all x_1, ..., x_n, P".

This means:

  * The Goedel sentence  G = ¬(th(var 1) = sub(reify j, reify j))
    has free var 1.  Deriv G means  forall x_1, ¬(th(x_1) = sub(...)) .

  * Con  is universally closed (no free vars in its formula, but the
    "for all y" reading of "y is not a proof of bot" is built in).

  * "Pr(G)" (closed, specific:  th(cG) = cG ) and "G" (with free var 1)
    have DIFFERENT closure structure.  Stating  Deriv ((not (Pr G))
    imp G)  asks BRA to prove a closed-implies-open implication --
    going from a specific instance to a universal, which Hilbert-style
    ruleInst does NOT support.

**Consequence**:  any contract of the form  "Deriv (closed_thing imp
G)"  is MALFORMED if the closure rules don't match.  The closure of
Goedel II in Guard does NOT use such a contract.  Specifically:

  * `internalDiag : Deriv ((not (Pr G)) imp G)`  is NOT a thing to
    ask for.  The earlier contract surface was wrong on this point.

  * Guard's closure uses step 5 (universally-closed implication in
    x) + ruleInst on Con + axContrapos.  No  ¬Pr(G) → G  contract
    needed.

  * `internalStep5 : Deriv (Pr G imp Pr bot)`  (closed) is a special
    instance of step 5 (parametric in x) at  x := cG .  Subsumed.

**This collapses the 5-contract list to 3 contracts**: just step3,
step4, step5.  No separate HBL contracts.

## Pre-flight: VERIFY this prompt against guard15.pdf Theorems 12-14

**This prompt makes architectural claims about Guard's Theorems 12,
13, and 14 (pp.15-17 in guard15.pdf) and how they map to BRA.  Before
writing any code, RE-READ guard15.pdf Theorems 12, 13, AND 14
(pages 15-17 inclusive, including Definition 12 on p.16) and
confirm:**

1. **Naming**: Guard's `i` is the numeral of `code(F_pre)` (where
   F_pre = "th(x_1) ≠ sub(x_0, x_0)"). Guard's `j` is the numeral of
   `code(G)` where G = "th(x_1) ≠ sub(i, i)". `j = sub(i, i)` holds
   in BRA (subDef + codeCommutes).
2. **Thm 14's hypothesis is `th(x) = j`** (Guard's j = code G), not
   `th(x) = i`.
3. **Thm 14 steps 1-5 produce internal BRA implications** (Deriv of
   `... imp ...`), not meta-arrows. The meta-arrow form is acceptable
   in our setup if we use deduction-theorem packaging at closure.
4. **Thm 13 in Guard uses `cong1 num` on the hypothesis** — but with
   our concrete `encode` available, Thm 13 collapses to one-line use
   of `encode` on the hypothesis. **No need for `num`/`cor` to
   distribute over functor applications.** That was a wrong path
   considered in the previous session and rejected.

If the interpretation in (1)-(4) above is wrong, **STOP** and report
the discrepancy. The plan below depends on this reading.

## Current state (start of next session)

After commit `[BRA-godelII-symmetric-pivot]` (and the i/j naming fix
in Thm14Abstract), the chain looks like:

| File | Role | LoC code | Status |
|---|---|---|---|
| `BRA/Thm/ThmT.agda` | concrete Thm 11: thmT, thClosed, codeF1Th_noVar, encode, thm11 unconditional | ~5500 | DONE; do not modify |
| `BRA/Thm14CodeFTeq.agda` | symmetric `codeFTeq alpha beta = reify(codeFormula(atomic(eqn alpha beta)))` | 11 | DONE |
| `BRA/Thm12Abstract.agda` | Thm 12 (uniform) via `encode ∘ axRefl` | 28 | DONE |
| `BRA/Thm13Abstract.agda` | Thm 13 (uniform) via `encode` on hypothesis | 44 | DONE |
| `BRA/Thm14Closure.agda` | Pr/Con concrete + closureToG via Bridge (HBL contracts) | 42 | DONE |
| `BRA/Thm14Abstract.agda` | Top module. Defines i, cG, PrAtX, negSubF; takes step3/step4/step5 (Sigma form, abstract) + Con + closureToG | 60 | DONE except step3-5 are abstract contracts |
| `BRA/GoedelII.agda` | Composes everything; takes 5 irreducible parameters | 48 | DONE structure; 5 params unfilled |

The 3 unfilled parameters in `GoedelII.Compose` (after the universal-
closure correction above; previously listed 5, but internalStep5 and
internalDiag are dropped as malformed/redundant):

- **step3, step4, step5** (Sigma form, take `(x, H : Deriv (PrAtX x))` and produce a witness tree). These ARE Thm 14's substrates -- the parametric-in-x internal implications that compose with Con + axContrapos + ruleInst at closure.

The closure  closureToG : Deriv Con -> Deriv G  is built DIRECTLY
from step5 + Con (no separate HBL contracts).  Sketch:
  1.  Step 5 gives a parametric-in-x internal implication:
      Deriv (atomic(eqn (ap1 thmT (var k)) cG)
              imp atomic(eqn (ap1 thmT (<final x>)) (reify(codeFormula bot))))
      [In sigma form: (x : Term) -> Deriv (PrAtX x) ->
                       Sigma Tree (\d -> Deriv (...))].
  2.  axContrapos on step 5 gives:
      Deriv (¬(th(<final x>) = code bot) imp ¬(th(x) = cG)).
  3.  ruleInst on Con  at y := <final x>  gives:
      Deriv (¬(th(<final x>) = code bot)).
  4.  mp gives  Deriv (¬(th(x) = cG)) , with x free.
  5.  Transport via  Deriv (sub i i = cG) (= subDef + cc) gives
      Deriv (¬(th(x) = sub i i)) = Deriv G  (with var 1 free,
      universally closed).

## What this session does

1. **Verify the prompt** against guard15.pdf pp.15-17 (mandatory).
2. **Implement step3, step4, step5** following Guard's chain at p.16-17:
   - Step 3: from `Deriv (th x = cG)`, derive `Deriv (th x = sub(i, i))` inside BRA via `subDef + codeCommutes + axEqTrans + ruleSym + mp`. Then `encode` the result.
   - Step 4: from `Deriv (th x = cG)`, derive the coded form of `not (th x = sub(i, i))`. This uses Thm 11's `diagonal` parameter (which gives `Deriv G → Deriv (not (th x = cG))` for any x). The trick: instantiate `diagonal` at `(reify y_d for some witness)`, contrapose, etc. **REVIEW THIS STEP CAREFULLY** — step 4 is where the diagonal property is internalised, and it's the most subtle step.
   - Step 5: combine step3 + step4 via internal ex-falso (using `axExFalso`). Output is a witness for `Deriv bot`'s coded form.
3. **Implement closureToG** via `Thm14Closure.Bridge` taking the two HBL contracts. The HBL contracts (internalStep5, internalDiag) are themselves still abstract — they may be derivable from step5 + step4 with deduction-theorem packaging.
4. **Compose everything** in GoedelII.agda. Once all 5 params are filled, `godelII : Deriv Con -> Deriv bot` is unconditional.

## Resolution of an earlier "open question" (no longer open)

A previous session draft asked: "Does `Deriv ((not (Pr G)) imp G)`
hold in our Hilbert-style BRA?"  This was MISFORMED.  Per the
universal-closure principle above:

  * G has free var 1; "Deriv G" means BRA proves the universal
    closure  forall x_1, ¬(th(x_1) = sub(i,i)) .
  * (not (Pr G))  is closed.
  * Asking for a Deriv of a closed-implies-universal implication is
    asking for generalisation, which Hilbert-style ruleInst doesn't
    support.

Guard's closure (re-read p.17) uses step 5 directly, not via this
"backward diagonal direction".  See the closure sketch above.  No
internalDiag contract is needed.

## Methodological principle: small files + fast typecheck = math is right

**This is non-negotiable.**  In this project, file size and typecheck
speed are not engineering preferences -- they are SIGNALS of
mathematical correctness:

  * If a single file grows past ~250 LoC,
  * If a single lemma's body exceeds ~50 lines,
  * If cold typecheck of a single file exceeds 2 seconds,

then **STOP and refactor**.  Do NOT push through.  Slowness or size
indicates one of:

  * Wrong abstraction granularity (a lemma should be split, or a
    contract should be parameterised differently).
  * Heavy normalisation leaking out of an  abstract  block (the
    THM11-GAP framing principle is being violated -- spec lemmas
    should hide their internals).
  * Mismatch with the underlying mathematics (the proof is doing
    more work than the math requires; usually the formulation is
    wrong, not Agda).

The existing chain has total cold rebuild ~4-5s (5500 lines of
concrete Thm 11 + 230 lines of abstract Goedel II chain).  Each new
file added in this session should keep this property.  If it doesn't,
that is the loudest signal that the architectural approach is wrong.

See memory `feedback_guard_fast_typecheck` and
`feedback_one_lemma_per_paper_step` for the project's accumulated
experience on this principle.

## Constraints (do not violate)

- `--safe --without-K --exact-split`, ASCII only, low-mixfix prelude.
- No new postulates.
- No reproof of Thm 11 (BRA/Thm/ThmT.agda); use it via `encode` only.
- No new BRA-foundation axioms (no cor-distributes, no num-distributes).
  If the chain seems to need them, **STOP** and report — that means
  the encode-based approach has a gap.
- Per-file budgets (per the methodological principle above):
  - Step3, step4, step5 implementations: ~150-250 LoC each, in their
    own file (e.g., BRA/Thm14Step3.agda).  IF you find yourself going
    past 250 LoC in a single file, STOP -- that is the principle
    firing.  Split or refactor.
  - Cold typecheck per file < 2s.  IF a file exceeds 2s, STOP -- the
    formulation is likely wrong.
  - Total chain cold rebuild < 10s.
- One named Agda lemma per Guard step (no monolithic let-bodies).

## Stop conditions

In priority order:

1. **Pre-flight verification fails**: re-reading guard15.pdf reveals
   the prompt's interpretation is wrong. Stop and report.
2. **Open question resolves negatively**: internalDiag is genuinely
   unprovable in our BRA Hilbert system. Stop and report; need
   architectural rethink.
3. **Step 3 or 4 needs new BRA infrastructure**: e.g., we discover
   we need cor-distributes or a similar axiom. Stop and report.
4. **Single step lemma exceeds 50 lines body** OR file > 300 LoC OR
   typecheck > 2s cold. Indicates wrong abstraction granularity;
   stop and refactor.

## Realistic scope per session

- (a) **Optimistic**: all three steps + both HBL contracts implemented
  cleanly. godelII unconditional. Probably impossible in one session.
- (b) **Realistic**: step 3 + step 5 (the easier ones — direct uses of
  `encode` + simple BRA derivations). Step 4 (diagonal internalised)
  + internalDiag (open question above) deferred. ~500 LoC, multi-file.
- (c) **Pessimistic**: open question (b) resolves negatively;
  architectural rework needed before further progress. Document the
  finding and stop. ~50 LoC of investigation.

If (b), ship it. If (c), this is genuine progress (a research-grade
finding about BRA's Hilbert system), not failure.

## Files this session writes

- `BRA/Thm14Step3.agda` (new) — step3's concrete implementation. ~150-250 LoC.
- `BRA/Thm14Step4.agda` (new) — step4's concrete implementation OR a
  documented "open question" file if Direction 2 proves difficult.
- `BRA/Thm14Step5.agda` (new) — step5's concrete implementation.
- (Possibly) `BRA/Thm14InternalStep5.agda` and
  `BRA/Thm14InternalDiag.agda` — HBL contracts.
- Update `BRA/GoedelII.agda` to plug in the concrete steps.

## Files this session does NOT write or modify

- `BRA/Thm/ThmT.agda` — leave alone. Stable, 5500 lines, contains
  concrete Thm 11.
- `BRA/Thm14CodeFTeq.agda` — codeFTeq is final.
- `BRA/Thm12Abstract.agda`, `BRA/Thm13Abstract.agda` — final.
- `BRA/Cor.agda`, `BRA/Sub.agda`, `BRA/SubT.agda`, `BRA/Mp.agda` —
  foundation, do not modify.

## Specific Thm 14 chain to implement

Reading Guard p.16-17 (Thm 14 proof) gives the following 5 steps.
Numbers (1)-(5) are Guard's; descriptions translate to BRA notation
where  i = reify j  (= reify(code F_pre))  and  cG = reify(codeFormula G).

1. **Guard line 1**:  th(x) = j ⊃ th(Dth(x)) = "th(x) = j", by Th 13.
   - In BRA: from Deriv (th x = cG), use `Thm13Abstract.thm13_th`
     (= `encode (atomic (eqn (th x) cG)) HYP`) to get
     `Sigma Tree (\d -> Deriv (th(reify d) = code(eqn (th x) cG)))`.
   - One line via existing infrastructure.

2. **Guard line 2**:  th(Dsub(i,i)) = "sub(i,i) = j", by Th 13.
   - In BRA: unconditional. Build `Deriv (sub i i = cG)` using
     `subDef j j` + `codeCommutes` + cong arguments. Then use
     `Thm13Abstract.thm13_sub` to encode.
   - Few lines.

3. **Guard line 3**: combine 1 + 2 via internal eq-trans:
   th(x) = j ⊃ th(g(x)) = "th(x) = sub(i,i)".
   - In BRA: from Deriv (th x = cG), build Deriv (th x = sub i i)
     via axEqTrans + ruleSym + mp on Deriv (sub i i = cG).
   - Then `encode` to get the witness.
   - ~30-50 lines.

4. **Guard line 4**: from j's definition + diagonal,
   th(x) = j ⊃ th(<diagonal-instance>) = "neg(th(x) = sub(i,i))".
   - In BRA: USE THE  diagonal  PARAMETER (or Thm 11's diagonal
     re-export) to internalise the negated equation.
   - This is the SUBTLE step. Diagonal in Thm11 says: from Deriv G,
     for every y, ¬(th(reify y) = cG). We need to internalise this
     into a BRA derivation that yields `not (atomic (eqn (th x)
     (sub i i)))` from hypothesis `th x = cG`.
   - Note: from `th x = cG` alone (without Deriv G), we don't get the
     negated equation. The internalisation requires combining with
     other facts. **REREAD GUARD p.17 CAREFULLY** to see exactly how
     Guard does step 4.
   - Likely uses `axContrapos` + the meta-fact that "th(x) = j and
     not(th(x) = j)" together would be inconsistent.

5. **Guard line 5**: combine 3 + 4 via internal ex-falso (axExFalso):
   th(x) = j ⊃ th(<final-tree>) = "0 = 1".
   - In BRA: from step 3 and step 4 derivations, use axExFalso on
     the formula `eqn (th x) (sub i i)` to get a Deriv of
     `atomic (eqn O falseT)` = bot. Then `encode` for the final
     witness.

## Pre-flight prompt verification (mandatory first action)

Open guard15.pdf, read **Theorems 12, 13, and 14** (pp.15-17, including
Definition 12 on p.16), and answer:

(a) Are i and j as I described in "Naming" above? (Specifically: is
    Guard's j really `code G`, and Guard's i really `code F_pre`?)
(b) Is the hypothesis of Thm 14's chain really `th(x) = j` (Guard's
    j = code G)?
(c) Does Guard's step 4 use the diagonal property in the way
    sketched (internalising "from Deriv G, ¬(th(x) = code G)")?
(d) Does internalDiag (`¬Pr(G) → G` provable inside BRA) appear in
    Guard's argument? Or does Guard avoid it via a different closure?

Document answers in a comment at the top of the first new file.

If (a)-(c) answer YES and (d) clarifies the closure structure,
proceed with the plan. Otherwise STOP.

## Recommended commit messages

- `[BRA-godelII-step3]` — step3 implementation.
- `[BRA-godelII-step4]` — step4 (or open-question report).
- `[BRA-godelII-step5]` — step5 implementation.
- `[BRA-godelII-closure]` — internalStep5 + internalDiag + GoedelII update.

## What success looks like

- Realistic: 2-3 steps closed, 1-2 still abstract or under analysis;
  the architectural roadmap (the open question on internalDiag) is
  resolved with a clear yes/no + path forward. ~500 LoC across 2-3 files.

- Aspirational: all 5 contracts filled, `godelII : Deriv Con -> Deriv
  bot` unconditional. Probably 2 sessions.

The session's primary deliverable: **either concrete progress or a
crisp report of where the open question lands**. Both are valuable.
