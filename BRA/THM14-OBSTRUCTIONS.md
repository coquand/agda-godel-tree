# Thm 14 (Goedel II) — obstructions discovered in pre-flight

Session date: 2026-04-25 .  Branch: `main`.

This note documents the architectural obstructions to the
"3 contracts (step3 / step4 / step5) + closureToG" plan in
`BRA/NEXT-SESSION-GODELII-STEPS.md` , discovered during the
mandatory pre-flight re-reading of `guard15.pdf` Theorems 12-14
(pp.15-17, including Definition 12 on p.16).

## Update (same session): architectural refactor done

Of the three obstructions originally documented below:

  * (f) "step 5 Sigma form doesn't compose with closure" -- RESOLVED.
    The corrected contract uses meta-Pi internal-implication form:
    `(x : Term) -> Deriv ((th(x) = cG) imp (th(constr5(x)) = "0=1"))` .
    Closure is mechanical:  axContrapos + ruleInst Con + mp +
    notEqTransport + G_unfold .  All in `BRA.Thm14Abstract.GodelII` .
  * (g) "Con must be parametric" -- RESOLVED.  `Con` is now defined
    with  `var zero`  free; the closure ruleInst-s at  `constr5(var 1)` .
  * "internalDiag malformed" -- RESOLVED by deletion.  Not part of
    the new contract.
  * (e) "step 4 needs sb infrastructure" -- STILL BLOCKING the
    FILLING of  step5  (since step5's body is built from steps 1-4
    + Definition 12 mp/sb encoding).  But the contract SHAPE is now
    honest: filling it requires either (i) building sb / Definition
    12 line 2 internalisation in BRA, or (ii) finding a different
    construction of  constr5  + step5 .

Files affected by the refactor:

  * `BRA/Thm14Abstract.agda` -- rewritten, 236 LoC / 108 code, 0.33s
    cold (full transitive deps).  Single contract:  constr5 + step5 .
    Closure inlined as  closureToG .
  * `BRA/GoedelII.agda` -- simplified, 87 LoC / 27 code, 3.58s cold
    (full chain incl. ThmT 9000 LoC).  module Compose takes 2
    parameters (constr5 + step5) instead of 5.
  * `BRA/Thm14Closure.agda` -- DELETED (superseded by
    Thm14Abstract.GodelII.closureToG).
  * `BRA/Thm11Diagonal.agda` -- minor: G_norm moved out of abstract
    block (j, G, cc, G_unfold remain abstract).  Necessary so
    notEqTransport's literal output unifies with  Deriv G_norm .

The single remaining contract is the one Guard's argument actually
DEPENDS on; the chain is now mathematically honest.



## PINNED: universal-closure semantics of  not  (read this first)

In our BRA (matching Guard 1963),  Deriv P  for an open formula  P
means BRA proves the UNIVERSAL CLOSURE of P.  Consequently  not_  at
the Formula level is purely SYNTACTIC; it does NOT lift  Deriv  to
"BRA refutes P":

  * `Deriv (not P)` for open P with free var x  =  BRA proves
    "for all x, ~P(x)" .
  * It is NOT  "BRA does not derive P"  (that is meta:
    `Deriv P -> Empty`).
  * It is NOT  "there exists x such that  Deriv (not P[x])" .
  * The two formulas  `not P`  (open) and  `not (substF x t P)`
    (closed by substituting a specific t) have DIFFERENT closure
    structure, and  `Deriv (not P) ` does NOT entail
    `Deriv (not (substF x t P))`  by  ruleInst  ( ruleInst  pushes
    substitution UNDER  not , so we get the negation of the
    substituted P, which is the same shape; the issue is that going
    the other way -- closed-implies-universal -- requires
    generalisation, which Hilbert  ruleInst  does not provide).

### How Guard handles this in Thm 12-14

Guard's whole chain stays at the ENCODED LAYER -- equations between
Terms, never a  Deriv  of an open formula's "negation in the meta
sense".  Specifically:

  * **Thm 12, 13**:  every conclusion is  th(D...) = "..." .  The
    "..." is just a coded formula (a Term), not a  Deriv .  =  is
    the object-level equality.

  * **Thm 14 steps 1-5**: every line has shape
        th(x) = j  ⊃  th(...) = "..."
    -- a  Deriv  of an INTERNAL IMPLICATION between two encoded
    equations.  Both antecedent and consequent are atomic equations,
    never an open  not P .

  * **Step 4 in particular**:  Guard NEVER says "from  th(x) = j
    derive  Deriv (~(th(x) = sub(i,i)))" (that would be unsound -- it
    would amount to deriving  Deriv G  under hypothesis  Deriv (PrAtX
    x) , which combined with thm11 collapses BRA on any provable
    instance of PrAtX).  He says
        th(x) = j  ⊃  th(<some construction>) = "the code of the
                                                  formula
                                                  '~(th(x) = sub(i,i))'"
    Pure encoded data on both sides; the  ~  lives only inside
    quotation marks.

  * **Closure (p.17 last paragraph)**:  axContrapos is applied to
    step 5's INTERNAL implication.  Con ("th(y) != '0=1'", parametric
    /universally closed in y) is  ruleInst -ed at  <final x> .  The
    result  th(x) != j  (open in x) is then identified with G via
    the closed equation  j = sub(i,i) .  The universal closure of
    `(th(x) != j)`  is exactly what  `Deriv G`  means.

### What this implies for our BRA Agda port

The mismatch in the current `BRA/Thm14Abstract.agda` parameter
shapes (Sigma / meta-arrow) is a failure to mirror Guard.  The
faithful port has each step as

```
step_k :
  Deriv (atomic (eqn (ap1 th (var 0)) j)
          imp atomic (eqn (ap1 th (<construction_k> (var 0))) <coded RHS k>))
```

-- an INTERNAL implication, with the  x  encoded as a free variable
inside the formula (Hilbert-style universal closure).  No Sigma; no
meta-arrow  `Deriv H -> Deriv ...` ; no  `Deriv (not P)`  for open
P.  The closure then composes step 5 with Con (parametric in y,
also INTERNAL) via  axContrapos + ruleInst + mp .

This is the architectural correction the prompt missed.  Future
sessions resuming Thm 14 work MUST start from internal-implication
step shapes, not from meta-arrow / Sigma forms.



The plan in `NEXT-SESSION-GODELII-STEPS.md` is right about steps 1-3
of Guard's chain, the universal-closure analysis of `internalDiag` ,
and the i / j naming.  It is wrong about three things, summarised
below.  Step 3 is implemented (`BRA/Thm14Step3.agda` , 95 LoC,
0.30s cold) as proof-of-concept that the "easy" half of the chain
works.  Steps 4-5 + closure are blocked pending architectural work.

## What the prompt got right

| Prompt claim | Verified against guard15.pdf |
|---|---|
| `i` = num(code F_pre), F_pre = "th(x_1) != sub(x_0,x_0)" | YES, p.15 Thm 11 |
| `j` = num(code G), G = "th(x_1) != sub(i,i)" | YES, p.15 Thm 11 |
| `j = sub(i,i)` is BRA-derivable | YES, p.15 Thm 11 step 1) |
| Thm 14 hypothesis is `th(x) = j` | YES, p.16-17 lines 1-5 |
| Steps produce internal BRA implications | YES, p.17 lines 1-5 |
| Thm 13 collapses to `encode` (no num/cor distribution) | YES, given concrete encode |
| `internalDiag : Deriv (~Pr(G) imp G)` is malformed | YES, universal-closure mismatch |

## What the prompt got wrong

### (e) Step 4 is NOT Thm 11's diagonal

The prompt reads Guard's step 4 as

> from j's definition + diagonal,
> th(x) = j   th(<diagonal-instance>) = "neg(th(x) = sub(i,i))"

and proposes to use `Thm11Diagonal.diagonal` to internalise the
negated equation.  Re-reading Guard p.17, step 4 is

> By the definition of j ,
> 4)  th(x) = j   th(4J(J(num x,1),x)+1) = "th(x) != sub(i,i)"

The justification "by the definition of j" invokes:

  * Definition 12 line 2 (the substitution clause of th):
    `th(4y+1) = sb(KKy, IKy, th(Iy))`
  * A primitive-recursive substitution operation `sb` on coded
    formulas:  `sb(num x, 1, code G) = code(G[var 1 := num x])` .

This is the INTERNALISATION OF BRA's substitution rule on coded
derivations, NOT Thm 11's diagonal lemma.  Thm 11's diagonal is a
META conclusion ("for any y, BRA proves not (th(reify y) = cG)").
Step 4 is an INTERNAL BRA derivation under the hypothesis
`th(x) = j`.

**Implication**: step 4 needs new BRA infrastructure:

  1. A primitive-recursive `sb : Term -> Term -> Term -> Term` for
     substitution on coded formulas (analog of Guard's `sb`).
  2. An axiom `axThmTSub`:
     `Deriv (atomic (eqn (ap1 thmT (subEnc x)) (ap3 sb (num x) (numLit 1) (ap1 thmT x))))`
     for the relevant primitive-recursive `subEnc x` , internalising
     Definition 12 line 2 of th.
  3. Computational lemma:  when `ap1 thmT x = cG` , the term
     `ap3 sb (num x) (numLit 1) cG` reduces in BRA to
     `reify (codeFormula (negSubF x))` .

This is substantial -- likely a multi-file subproject by itself, on
the order of the existing CodeCommutes / Sub / SubT chain.  Since the
prompt's `step4` parameter type is wrong about the mechanism, it
cannot be filled with the prompt's intended approach.

### (f) Step 5 in Sigma form does not compose with the closure

The prompt's `step5` parameter has Sigma / meta-arrow form

```
step5 :
  (x : Term) ->
  Deriv (PrAtX x) ->
  Sigma Tree (\ d ->
    Deriv (atomic (eqn (ap1 th (reify d)) (reify (codeFormula bot)))))
```

The closure sketched in the prompt uses `axContrapos` on step 5:

> 2.  axContrapos on step 5 gives:
>     Deriv (~(th(<final x>) = code bot) imp ~(th(x) = cG)) .

But `axContrapos` is `Deriv ((P imp Q) imp ((not Q) imp (not P)))` --
its input is a Deriv of an INTERNAL implication `Deriv (P imp Q)` ,
not a meta-arrow `Deriv P -> Deriv Q` .  The Sigma-form step 5 above
is a meta-arrow; the closure cannot apply `axContrapos` to it
directly.

**Going from meta-arrow to internal implication** is the content of
the Hilbert-Bernays Deduction Theorem (DT).  DT is metatheoretically
true for our Hilbert-style BRA (since axS / axK / mp are all
present) but is NOT built as a recursive Agda function on `Deriv` .
Building it is its own subproject (Guard's lecture notes p.10
Exercise 17 sketches it, but mechanising it is non-trivial; expect
~500 LoC).

**Workaround idea**: rewrite the closure to NOT use `axContrapos` ,
and instead use meta-arrow steps + classical reasoning to internalise
the contradiction.  Specifically:

  * Assume `Deriv Con_param` where
    `Con_param = not (atomic (eqn (ap1 th (var zero)) (reify (codeFormula bot))))`
    (parametric in y; see (g) below).
  * Goal: `Deriv G` , equivalently
    `Deriv (not (atomic (eqn (ap1 th (var (suc zero))) (ap2 sub i i))))` .
  * Strategy: build `Deriv (PrAtX (var (suc zero)) imp falseT)` from
    step 5's meta-arrow + Con_param, by:
      - Apply step 5 to `(var (suc zero))` and a HYPOTHETICAL
        `Deriv (PrAtX (var (suc zero)))` , producing
        `Deriv (atomic (eqn (ap1 th (reify d)) (reify codeBot)))` .
      - Use Con_param ruleInst'd at `reify d` and combine via
        `axExFalso` to derive `Deriv falseT` .
      - Wrap the hypothetical via DT to get
        `Deriv (PrAtX (var (suc zero)) imp falseT)` .

This still uses DT.  No way around it without a serious rework of
how step 5 is stated.

**Alternative**: state step 5 directly in internal-implication form
from the outset:

```
step5_int :
  (x : Term) ->
  Sigma Tree (\ d ->
    Deriv ((atomic (eqn (ap1 th x) cG))
            imp (atomic (eqn (ap1 th (reify d)) (reify (codeFormula bot))))))
```

Then `axContrapos` composes directly.  But proving step5_int
requires DT (or an equivalent direct construction in Hilbert-style),
which has the same cost as proving DT once and reusing it.

### (g) Con must be parametric, not closed

Current `BRA/Thm14Closure.agda` defines

```
Pr : Formula -> Formula
Pr P = atomic (eqn (ap1 th (reify (codeFormula P))) (reify (codeFormula P)))

Con : Formula
Con = not (Pr bot)
```

This is the CLOSED instance "th(reify codeBot) != reify codeBot" .
The Guard closure (p.17 last paragraph) needs Con to be PARAMETRIC
in y:

```
Con_param : Formula
Con_param = not (atomic (eqn (ap1 th (var zero)) (reify (codeFormula bot))))
```

i.e., "for all y, th(y) != reify codeBot" .  The closed form is too
weak: the closure needs to instantiate Con at the specific `<final
x>` witness produced by step 5.  Closed Con cannot be ruleInst'd at
arbitrary terms.

Fixing this is small (one line in `Thm14Closure.agda` ), but it
changes the type of `closureToG` and propagates to `GoedelII.agda`
(via the `Con` re-export).  Should be done together with the closure
refactor in (f).

## Summary status

| Item | Status |
|---|---|
| Pre-flight verification | DONE; (a)-(d) match Guard, (e)-(g) are obstructions |
| `BRA/Thm14Step3.agda` | DONE; 95 LoC, 0.30s cold (Step3 + all deps); subIIeqcG factored for downstream reuse |
| step4 | BLOCKED on (e); needs sb infrastructure (multi-file subproject) |
| step5 | BLOCKED on (e) AND (f); meta-arrow doesn't compose with closure |
| closureToG refactor | BLOCKED on (f) AND (g); needs Con_param + DT or a meta-arrow closure design |
| `GoedelII.agda` plug-in | BLOCKED until step 4-5 + closure are unblocked |

Step 3 is plug-in-ready when steps 4-5 are unblocked: it has the
right Sigma type, depends only on `subDef` + `cc` , typechecks fast,
and would slot into `GoedelII.Compose` 's `step3` parameter as-is.

## Recommended next steps (next session)

The immediate question is whether the cost of the (e) sb
infrastructure + (f) DT mechanisation is worth it, or whether a
different architecture is preferable.

Options ranked by cost / payoff:

  1. **Build sb + axThmTSub + DT in BRA.**  Substantial (~1000-2000
     LoC over several sessions).  Direct port of Guard's argument.
     Each piece is mathematically clear; just needs careful
     mechanisation.

  2. **Reformulate Goedel II without internalising substitution.**
     Use the encode-based "concrete Thm 11" infrastructure plus a
     soundness-style argument.  Open question whether this is
     actually formalisable inside `--safe --without-K` Agda without
     effectively re-doing (1).

  3. **Stop at "abstract Goedel II" + concrete Goedel I.**  Keep the
     current chain (Thm14Abstract / Thm14Closure / GoedelII.Compose)
     parametric over the 5 (or 3, after the closure refactor)
     contracts, and SHIP that as the deliverable, with the
     understanding that filling those contracts is a separate
     research project requiring full sb infrastructure.

  4. **Refactor closure to need NEITHER step 4 nor full DT.**  Open
     question.  The classical-meta-arrow workaround in (f) might
     reduce DT's role to just a single instance, which could be
     done by hand for that one instance.  Worth a focused session.

The methodological principle ("small files / fast typecheck =
math is right") suggests options 3 and 4 are more aligned with the
project's character than 1 and 2.

Concrete Goedel I (`BRA/Thm/ThmT.agda` + `thm11` ) remains
unconditional and is the project's primary mechanised deliverable.
