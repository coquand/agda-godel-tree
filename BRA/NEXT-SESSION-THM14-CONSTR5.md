# Next session — finish Theorem 14 (constr5 + step5 → unconditional godelII)

## Pre-flight

Read `guard15.pdf` pages 16-17 (Theorems 11-14) before writing any code.
Verify the exact form of:
- the transitivity numeral `t` ("x₀=x₂ ⊃. x₁=x₂ ⊃ x₀=x₁") — note the
  variable order, which differs from our `axEqTrans : (a=b) imp ((a=c) imp (b=c))`.
- the ex-falso numeral `t'` ("x₀=x₁ ⊃. x₀≠x₁ ⊃ 0=1").
- the substitution chain in `f(x), g(x), h(x)` (which variable index
  gets substituted at each `+1` step, and what the substituent is).

Misreading any of these is the most common multi-session cost; budget 30
minutes for the read-check before touching Agda.

## Success criterion (single line)

A closed Agda value of the type

```agda
godelII : Deriv Con -> Deriv bot
```

exported from a new module `BRA.Thm14Final` (or absorbed into
`BRA.GoedelIIFinal`), with no postulates, no holes, no module
parameters, and no axioms outside `BRA/Deriv.agda`. The chain must run
through `BRA.GoedelII.Compose` with the concrete `(constr5, step5)`
delivered by this session.

## What's already in place (do not rebuild)

| Component | File:Line | Status |
|---|---|---|
| `thm12_F1`, `thm12_F2` (unconditional) | `BRA/Thm12.agda:106-107` | done — `module FromBridges where` is parameterless |
| `Df_thmT`, `Df_sub` extraction | `Thm12Check.agda` (sanity probe) | typechecks |
| `thm13_F1`, `thm13_F2` (concrete) | `BRA/Thm13.agda:54-81` | done |
| `BRA.Thm14.Thm14` skeleton | `BRA/Thm14.agda:109-228` | takes `(r12_th, r12_sub, constr5, step5)` and discharges everything else |
| `BRA.GoedelII.Compose` | `BRA/GoedelII.agda:56-87` | takes `(constr5, step5)` and produces `godelII` |
| `step1_l`, `step2_l` (Carneiro-lifted) | `BRA/Th14Constr5.agda:148-163` | done |
| `thmTDispMp`, `thmTDispRuleInst` | `BRA/Thm/ThmT.agda:5575, 8621` | done |
| `encode` (Thm 11 forward encoder) | `BRA/Thm/ThmT.agda` `WithDispatch` module | done |
| `subIIeqcG : Deriv (sub i i = cG)` | `BRA/Thm14Abstract.agda:100-112` (re-exported via `BRA.GoedelII`) | done |
| `axImpRefl`, `liftAxiom`, `liftThm13_F1`, `liftedRuleTrans`, `liftedCong1`, `liftedCongL`, `liftedCongR`, `B_combinator` | `BRA/Th14Constr5.agda` + `BRA/Thm/EvalHelpers.agda` | done |
| `MaxVar.pickFresh` and friends | `BRA/MaxVar.agda` | done — useful if any `ruleInst` step inherits the IfLf-style closure issue |

## Concretely instantiate the Thm 12 results

The first thing to do, once `constr5/step5` exist, is plug in:

```agda
r12_th  : Thm12_F1_Result thmT
r12_th  = BRA.Thm12.FromBridges.thm12_F1 thmT

r12_sub : Thm12_F2_Result sub
r12_sub = BRA.Thm12.FromBridges.thm12_F2 sub
```

These are now closed top-level values. Verify by calling
`agda BRA/Thm14.agda` after instantiation; `BRA.Thm14.Thm14` is the
right module to thread them through.

## The five-step chain (Guard p.17)

Notation: `K(x)` = numeral coding "th(x_)" (a one-arg formula with
`var 0` free), `M` = numeral coding "sub(i,i)", `numJ` = `num j` as a
Term (= `i`).

| Step | Guard | BRA encoding | Building block |
|---|---|---|---|
| 1 | `th(x)=j ⊃ th(Dth(x)) = "th(x_)=j"` | `step1_meta_at` (already in `BRA/Thm14.agda:169`) or `step1_l` (lifted, in `Th14Constr5.agda:148`) | `thm13_F1 thmT r12_th x cG H` |
| 2 | `th(Dsub(i,i)) = "sub(i,i)=j"` | `step2_meta` (already in `BRA/Thm14.agda:190`) or `step2_l` | `thm13_F2 sub r12_sub i i cG subIIeqcG` |
| 3 | `th(x)=j ⊃ th(g(x)) = "th(x_)=sub(i,i)"` | needs `t_term` + `g_part : Fun1` | encMp twice over t-substituted-by-K(x), M, numJ |
| 4 | `th(x)=j ⊃ th(K(x)) = "th(x_)≠sub(i,i)"` | needs `K_part : Fun1` (sb at var 1 of `j`) | one `thmTDispRuleInst` |
| 5 | `th(x)=j ⊃ th(constr5(x)) = "0=1"` | needs `t'_term`, `h_part`, `constr5 : Fun1` | encMp twice combining (3), (4), and `t'`-via-h |

## Detailed construction order

### Phase A — numeral encodings (~150 LoC)

**A.1** Build the BRA Deriv of Guard's transitivity formula at fresh
variables `(var 0, var 1, var 2)`. Note the rearrangement:
`(var 0 = var 2) imp ((var 1 = var 2) imp (var 0 = var 1))`. This is
**not** `axEqTrans` directly; it requires `ruleSym` on the second
antecedent + Carneiro-style lifting:

```agda
t_deriv : Deriv (atomic (eqn (var 0) (var 2))
                  imp (atomic (eqn (var 1) (var 2))
                        imp (atomic (eqn (var 0) (var 1)))))
```

Strategy: under hypothesis `var 0 = var 2`, lift the inner; under
hypothesis `var 1 = var 2`, derive `var 2 = var 1` via `ruleSym`-style
lifted, then `liftedRuleTrans` with the outer hyp.

**A.2** `t_term : Tree` and `t_witness : Deriv (thmT (reify t_term) = reify (codeFormula <t_deriv's formula>))` via:

```agda
(t_term , t_witness) = encode <t_deriv's formula> t_deriv
```

(`encode` returns a `Sigma Tree (\ y -> Deriv (...)).`)

**A.3** Symmetrically for `t'_deriv : Deriv ((var 0 = var 1) imp ((not (var 0 = var 1)) imp bot))` via `axExFalso`. Then `(t'_term, t'_witness) = encode _ t'_deriv`.

**Gotcha:** The encoded formula must literally match what later sb
substitutions expect. Choose variable indices `0, 1, 2` for the
transitivity antecedents and `0, 1` for ex-falso; mismatches will
manifest as failed `thmTDispRuleInst` shape obligations downstream.

### Phase B — sb-chain functors (~250 LoC)

Each "+1" step in Guard's f, g, h uses `encRuleInst` (Definition 12 sb
clause). `encRuleInst x t y_h` builds the Tree
`nd (code (var x)) (nd y_h (code t))`. We need to package this as a
**Fun1 in x** at the leaf positions where Guard substitutes `num x`
into the transitivity / ex-falso skeleton.

For `f_part : Fun1` (Guard's `f(x)` minus the outer mp's), the sb-chain
substitutes:
- at var 0 of `t_term`: substituent is "th(x_)" coded — depends on x.
- at var 1: substituent is "sub(i,i)" coded — closed.
- at var 2: substituent is `numJ = i` — closed.

The "depends on x" position uses `cor x` at the leaf and `Comp` over
the closed sb-tree skeleton. Specifically:

```agda
f_part : Fun1
f_part = Comp (sb-skeleton) cor   -- placeholder; the actual shape
                                  -- chains three encRuleInst headers
```

Concretely: build `f_skeleton : Term` (closed) with one variable hole
where `cor x` plugs in, then wrap as `f_part = ... cor ...`. The
**shape obligation** for `thmTDispRuleInst` is `Fst(reify y) = Pair O y'`
(line 8623 of ThmT). Each header `nd (code (var k)) ...` satisfies this
by `axFst` reduction; verify before composing.

Similarly:
- `g_part(x) = encMp(encMp(f_part(x), Dth(x)), Dsub(i,i))`.
- `K_part(x) = encRuleInst (suc zero) (cor x) <code j>` — one sb step on j.
- `h_part(x) = encMp(encMp(... t'-chain ..., Dth(x)), Dsub(i,i))` analogous to g.
- `constr5(x) = encMp(encMp(g_part(x), h_part(x)), K_part(x))` — outer assembly.

### Phase C — singly-lifted step5 chain (~300-500 LoC)

Each chain node is a **lifted** ruleTrans of the form

```agda
P imp atomic (eqn lhs rhs)
```

where `P = PrAtX x = atomic (eqn (thmT x) cG)`. The helpers in
`BRA/Thm/EvalHelpers.agda` (`liftAxiom`, `liftedRuleTrans`,
`liftedCong1`, `liftedCongL`, `liftedCongR`) compose these.

The chain (in lifted form):

```
step1_l x : P imp (thmT(Dth(x)) = "th(x_)=j")             [done]
step2_l x : P imp (thmT(Dsub(i,i)) = "sub(i,i)=j")        [done]

step3_l x : P imp (thmT(g_part(x)) = "th(x_)=sub(i,i)")
  -- via encMp twice + thmTDispMp_param-style lifted
  -- consume step1_l, step2_l, t_witness lifted

step4_l x : P imp (thmT(K_part(x)) = "th(x_)≠sub(i,i)")
  -- via thmTDispRuleInst on the hypothesis P (sb at var 1 of j)
  -- this is the ONLY place where the antecedent P feeds in non-vacuously

step5_inner x : P imp (thmT(...) = "th(x_)=sub(i,i) ⊃ ¬(...) ⊃ 0=1")
  -- via thmTDispRuleInst chain on t' lifted

step5_l x : P imp (thmT(constr5(x)) = code bot)
  -- via encMp(step3_l, step5_inner) then encMp(_, step4_l)
```

### Phase D — discharge step5 to GoedelII.Compose (~30 LoC)

Once `constr5 : Fun1` and `step5_l : (x : Term) -> Deriv (P imp (thmT(constr5(x)) = code bot))` are built:

```agda
module Final = BRA.GoedelII.Compose constr5 step5_l
godelII : Deriv Con -> Deriv bot
godelII = Final.godelII
```

That's the whole closure — `BRA.Thm14Abstract.Thm14.GodelII` already
threads `axContrapos` + `ruleInst Con at constr5(var 1)` + `mp` +
`notEqTransport via subIIeqcG` + `G_unfold` + `thm11`.

## Likely gotchas (in priority order)

1. **Transitivity-formula shape mismatch.** Guard's t is
   `(x₀=x₂) imp ((x₁=x₂) imp (x₀=x₁))`. Our `axEqTrans` is
   `(a=b) imp ((a=c) imp (b=c))`. They are **not** the same up to
   variable renaming; the second antecedent direction differs.
   Building `t_deriv` requires a `ruleSym`-flip on the second
   antecedent inside the implication body. Use `liftedRuleSym`-style
   wrapping under the antecedent.

2. **`thmTDispRuleInst` shape obligations.** Each `encRuleInst` use
   needs `Deriv (Fst(reify y_h) = Pair O y')`. For
   `y_h = nd (code (var k)) ...` this is `axFst` after `reify` reduction.
   Pre-build a small lemma `headShape : (a b : Tree) -> Deriv (Fst(reify (nd a b)) = Pair O (reify a))` to avoid copy-paste at every node.

3. **`thmTDispMp` shape obligations.** Same pattern; pre-build
   `mpHeadShape`. The shape input is the same `axFst`-style proof.

4. **Lifting `t_witness` under `P`.** `encode`'s output is closed
   (`Deriv (thmT(reify t_term) = reify (codeFormula t_formula))`).
   Use `liftAxiom P` to lift it. No new `ruleInst` needed.

5. **Variable-substitution alignment.** When `K_part(x)` does sb at
   var 1 of `j`, the result must be Guard's "th(x_)≠sub(i,i)".
   `outRuleInst` (BRA/Thm/Parts/RuleInst.agda) tells you the exact
   output shape; verify by computing it on a small example. The result
   is `codeFormula (substF (suc zero) (cor x) G_norm)` — and `G_norm` is
   the open form of G with var 1 free. Match this carefully.

6. **`Sigma` extraction.** `encode` returns a `Sigma Tree (\ y -> ...)`.
   Use `Sigma.fst` for the tree, `Sigma.snd` for the witness. Don't
   confuse `t_term : Tree` (the `fst`) with `reify t_term : Term` (what
   actually gets substituted into BRA).

7. **`cor` vs `num` vs `cor (var x)`.** Guard writes `num x` for "the
   numeral whose Goedel number is x"; in our codebase that's `cor x`
   (per memory `project_cor_at_sb_load_bearing`). At `step4_l`, the
   substituent is `cor x` (= num x in Guard's notation), not `x` itself.

## Recommended attack order

1. **(30 min)** Pre-flight verify guard15 p.17. Write down on paper the
   exact `t`-formula, `t'`-formula, the substitution sequence in `f`,
   `g`, `h`, and the final `constr5` shape. Confirm against
   `BRA/Th14Constr5.agda` comments and `BRA/Thm14.agda` comments.

2. **(1-2 hr) Phase A.** Build `t_deriv`, `t_term`, `t_witness`,
   `t'_deriv`, `t'_term`, `t'_witness`. Land as `BRA/Thm14Numerals.agda`.
   Sanity check: `agda BRA/Thm14Numerals.agda` typechecks. **Stop and
   commit here** — even at this checkpoint, you have closed encoded
   transitivity / ex-falso witnesses, which is reusable infrastructure.

3. **(1 hr) Phase B sketch.** Define `f_part`, `g_part`, `K_part`,
   `h_part`, `constr5` as `Fun1` values (closed expressions). Don't
   prove anything yet — just get the term-level construction
   typechecking. Land as `BRA/Thm14Constr5Final.agda` (or extend
   `Th14Constr5.agda`). Stop and commit.

4. **(2-4 hr) Phase C.** Build `step3_l`, `step4_l`, `step5_inner`,
   `step5_l` one at a time. Each is `liftedRuleTrans` over already-lifted
   pieces. **Use TaskCreate per step** so progress is visible. After
   each step commit, run `agda BRA/Th14Constr5.agda` (or wherever
   you're working).

5. **(15 min) Phase D.** Plug `constr5` and `step5_l` into
   `BRA.GoedelII.Compose`. Export `godelII`. Done.

If you stall on any phase >2 hours, write a substep-prompt for the
next session and stop. Carry forward whatever did typecheck.

## Constraints

- ASCII only.
- `{-# OPTIONS --safe --without-K --exact-split #-}`.
- No postulates, no holes, no with-abstraction, no dot patterns.
- Do not weaken any other theorem.
- No new `Deriv` constructors, no new tagged dispatchers in
  `BRA/Thm/ThmT.agda` — every primitive needed already exists.

## See also

- `BRA/Thm14.agda` — orchestrating module with steps 1+2 inline.
- `BRA/Th14Constr5.agda` — Carneiro-lifted scaffold with step1_l/step2_l.
- `BRA/Thm/EvalHelpers.agda` — singly-lifted combinators.
- `BRA/Thm/ThmT.agda:5575, 8621` — `thmTDispMp`, `thmTDispRuleInst`.
- `BRA/THM14-OBSTRUCTIONS.md` — historical pitfalls (PINNED at the top).
- `BRA/NEXT-SESSION-THM14-CARNEIRO.md` — earlier session notes; some
  pieces superseded by this session's Thm 12 closure-free landing.
- `MEMORY.md` entries beginning with `feedback_th14_*` — load-bearing
  warnings about what doesn't work.

## What to update on success

- `MEMORY.md` add: `project_godelII_unconditional.md` (the chain is
  closed; GoedelII has zero contracts).
- `BRA/THM14-OBSTRUCTIONS.md` mark all PINNED items as "RESOLVED in
  session YYYY-MM-DD".
- Delete or update `NEXT-SESSION-THM14-CARNEIRO.md` (now superseded).
- `BRA/Thm14Final.agda` (or whatever the new headline file is called)
  becomes the canonical Goedel II chain entry point.
