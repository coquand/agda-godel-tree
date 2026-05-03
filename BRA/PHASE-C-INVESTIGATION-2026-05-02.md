# Phase C blocker — investigation results 2026-05-02

## Question

Can `cor (var n) = reify (code (var n))` be derived in BRA without
new axioms?

## Answer: NO.

`cor = Rec stepCor`, definitionally `Comp2 (treeRec Z stepCor) Z I`.
Its defining equations (axRecLf / axRecNd, derived from axTreeRecLf /
axTreeRecNd) only fire when the input is structurally `O` or
`ap2 Pair a b`.  `var n` is a third constructor — neither lf nor
Pair — so no defining equation reduces it.

The only universal-quantifier rule available, `ruleIndBT`, would prove
`forall x. P(x)` from `P(O)` and `P(a) -> P(b) -> P(Pair a b)`.  But
the would-be `P(x) = (cor x = reify (code x))` cannot be expressed in
BRA's formula language: `code x` is meta-level, defined by Agda
recursion on Term, and `reify (code x)` for parametric `x` is not a
BRA Term.

`corOfReify : (t : Tree) -> Deriv (atomic (eqn (cor (reify t)) (reify (code (reify t)))))`
is the ONLY BRA-derivable `cor`-equation, and it requires a
reified-Tree input — exactly what is NOT available for `cor x` when
`x` is a variable.

**Path (A) from NEXT-SESSION-PHASE-C-BLOCKER.md is RULED OUT.**

## How Guard handles the analogous step

Read pages 12-17 of guard15.pdf.  Guard's `num` (Exercise 24 [7]) is
the analog of our `cor` — defined on numerals, not arbitrary BRA
terms.  Definition 12 introduces underline notation: ξ underlined
means `num(A_i)` substituted for `"A_i"`.

In Guard's Theorem 14 proof (p.16-17), `f(x), g(x), h(x)` are p.r.
expressions in x:

  f(x) = 4J[J("th(x)", 0), 4J[J("sub(1,1)", 1), 4J[J(num j, 2), t]+1]+1]

`num x` appears symbolically inside `"th(x)"` (which expands to
`J("th", num x)+1` by Def 11/12).  Guard NEVER structurally
decomposes `num x`.

**Why Guard's proof works without canonicalization**: Guard's modus
ponens is a primitive recursive function on numerals
(Exercise 24 [1]: `mp("P", "P ⊃ Q") = "Q"`).  This is a META-LEVEL
p.r. evaluation — a fact about numerals' Gödel-encoding structure
that holds *by p.r. computation*, NOT by a BRA-level derivation.
Guard's `th(fx) = "th(x) = j ⊃ . sub(1,1) = j ⊃ th(x) = sub(1,1)"`
is established via Theorem 13 (corollary of Theorem 12) — not by
BRA-internal canonicalization through `num x`.

## Why BRA's chain hits the blocker

In BRA, `thmTDispMp_param` requires
`Deriv (atomic (eqn (thmT y1T) (Pair tagImp (Pair pT qT))))` —
an explicit BRA-level equation exposing the Pair-shape so that
body_mp_eval_param can extract qT via Snd-Snd projections + axSnd.

This is more intensional than Guard's `mp("P", "P ⊃ Q") = "Q"`.
Guard's holds by p.r. computation (no structural-Pair-distribution
through symbolic `num x` ever needed); BRA's requires us to derive
the Pair-shape via subT-distribution lemmas, which cascade through
TreeEq comparisons — and TreeEq stalls on `cor x` because no
defining equation fires.

Concretely the dead-end is:

  TreeEq tagVarT (Pair (cor x) varCode2T)
    = axTreeEqNN
    = IfLf (TreeEq (Fst tagVarT) (cor x))
           (Pair (TreeEq (Snd tagVarT) varCode2T) (Pair O O))

`TreeEq <Pair-or-leaf> (cor x)` does not fire by any of axTreeEqLL /
LN / NL / NN.  IfLf doesn't fire either (no Pair / leaf head).

## Path forward analysis

### (A) Cor-output-shape lemma — RULED OUT

Investigated above.  Not BRA-derivable.

### (B) Chain redesign — VIABLE, ~500 LoC

Restructure `f_part` so `cor x` is substituted via a single OUTER
cong1-cor / axEqCong1-cor step (or via a fresh closed placeholder
that gets bridged at the end), avoiding any subT-distribution
through Pair structures containing `cor x`.

### (C) Generalized subT distribution — INSUFFICIENT

Even a parametric `subT_dist_param` lemma still requires deriving
`TreeEq varCode (Pair X Y) = falseT` when X contains `cor x` —
the same TreeEq dead-end appears.  This path doesn't dodge the
fundamental obstruction.

### (D) Augment thmTDispMp_param via projection — DOESN'T WORK

Trying to bind pT, qT to `Fst (Snd (thmT y1T))` and
`Snd (Snd (thmT y1T))` requires `thmT y1T` to be EXTENSIONALLY a
Pair — and BRA has no eta-rule for Pair.  Proving
extensionality requires the same canonicalization that's blocked.

### (E) Fresh approach: keep `cor x` outside subT — VIABLE, ~300-400 LoC

Mirror Guard's chain shape more directly.  Specifically:

**(E1)** Define f_part as a chain over a CLOSED transitivity body
that doesn't contain `cor x` at all.  After thmT evaluates the
sb-chain to `subT^3 (...) (reify (codeFormula t_formula))` with
ALL closed substituents, this canonicalizes cleanly via
subT_codeFormula_imp / atomic / neg cascades to a fully explicit
Pair tagImp (Pair pT_closed qT_closed) form.

**(E2)** Introduce `cor x` later — via an outer ruleInst step
that substitutes `cor x` for an additional fresh variable v in
the closed Pair-canonicalized form.  Apply `subT_codeFormula_*`
lemmas at this LAST step; the substituent (cor x) is now opaque,
but the encoded formula has already been canonicalized to Pair
form before this final substitution, so subT_dist_Pair_tagImp etc
push subT through the Pair structure WITHOUT needing TreeEq to
match against `cor x`.

The key invariant: subT(Pair varCodeV (cor x)) X distributes via
subT_dist_Pair_tagImp (head check is closed tagImp vs varCodeV;
TreeEq fires cleanly without reaching cor x).  As long as the
"target" structure X is built only from closed reified pieces and
cor x appears only as the SUBSTITUENT (the second arg of the
varCode pair), TreeEq matches are between closed Trees on both
sides, never structurally descending into cor x.

This is the architectural difference from the current chain: in
the current f_part, cor x is the OUTPUT of an early subT, then
becomes embedded INSIDE the subsequent subT's TARGET — that's
where TreeEq gets stuck.  In path (E), cor x is always the
SUBSTITUENT, never the target's content.

## ROOT CAUSE: sb-chain inverted relative to Guard

While building the projection-based fix below, I traced through the
chain to verify it dissolves the blocker.  It DOESN'T — Snd-Snd
projections still require axSnd to fire, which requires Pair-shape
extensionality, which requires canonicalization, which (one Snd past
the outermost tagImp push) hits cor x and stalls.

But the trace exposed the actual bug:

**Our `f_part` has the sb-chain inverted relative to Guard.**

Guard's f(x) (guard15.pdf p.17):
```
f(x) = 4J[J("th(x_underlined)", 0), 4J[J("sub(1,1)", 1),
                                       4J[J(num j, 2), t]+1]+1]+1
```

Reading off:
  * OUTERMOST sb (`+1` outer): `J("th(x_underlined)", 0)` — substitutes
    cor-x analog for var 0.
  * MIDDLE sb: `J("sub(1,1)", 1)` — substitutes closed sub_ii for var 1.
  * INNERMOST sb: `J(num j, 2)` — substitutes closed i for var 2,
    applied first to the closed proof index t.

Substitution order chronologically (innermost subT applied first to
codeFormula t_formula, then wrapped by the next layer):
  1. subT (vc2, i) on closed `codeFormula t_formula` — closed → closed.
  2. subT (vc1, sub_ii) on the closed canonicalized result — closed → closed.
  3. subT (vc0, cor x) on the closed canonicalized result — substitutes
     cor x at varCode0T leaves; cor x is INTRODUCED at this step but
     no further subT is applied AFTER it.

**Our current f_part** (BRA/Thm14Constr5Final.agda:174):
```
f_part_inner2 = ruleInst at var 0 (cor x)        -- INNERMOST
f_part_inner1 = ruleInst at var 1 (sub_ii)
f_part        = ruleInst at var 2 (i)             -- OUTERMOST
```

So our chronological substitution order is:
  1. subT (vc0, cor x) on closed codeFormula t_formula — INTRODUCES
     cor x as content of the result.
  2. subT (vc1, sub_ii) on a target now containing cor x → BLOCKER.
  3. subT (vc2, i) — would also blocker.

**The bug**: the constr5 builder reversed the sb-chain order relative
to Guard.  Guard does var 0 LAST (chronologically); we do var 0 FIRST.

The same bug applies to h_part (var 0 cor x is innermost in our
design; should be outermost).

## The fix

Invert f_part / h_part / etc. so that var 0 (cor x) is the OUTERMOST
ruleInst layer, matching Guard.  After inversion:

  * subT (vc2, i) and subT (vc1, sub_ii) operate on closed targets
    with no cor x — fully canonicalizable via subT_codeFormula_imp /
    atomic / neg cascades.
  * subT (vc0, cor x) operates LAST on the canonicalized closed
    target; substitutes cor x at varCode0T leaves; no further subT.

The cor-x blocker dissolves because cor x is never CONTENT of a
subT target.  The existing subT_codeFormula_imp / subT_dist_Pair_*
infrastructure suffices.

## Files to update

  * `BRA/Thm14Constr5Final.agda` — invert f_part / h_part definitions.
  * `BRA/Th14Step3.agda` — invert step3_pre's layer order
    (chronologically: vc2-first, vc1-middle, vc0-last instead of
    current vc0-first, vc1-middle, vc2-last).
  * `BRA/Th14StepHPre.agda` + `BRA/Th14HUnfolds.agda` — analogous
    inversion for h_part_pre.
  * `BRA/Th14GPartUnfolds.agda` — re-verify g_part_unfold lemmas
    are unaffected (g_part wraps f_part; just plumb through).

Estimated cost: ~150-200 LoC of mechanical updates.

## Path (F) — projection-based mp dispatch (auxiliary, already landed)

**Path (E) is supplanted.**  Re-reading `body_mp_eval_param`'s proof
(BRA/Thm/ThmT.agda:5698) shows the d1 hypothesis is doing FAR less
work than it appears.  The proof's structure:

```
body_mp ... bb  =  X(Snd bb)              -- by postSndBody_eval
                =  X(Pair tj1 tj2)        -- by distH
                =  Snd (Snd tj1)          -- by axComp + axFst
                =  Snd (Pair pT qT)       -- by d1, axSnd     <- d1 enters here
                =  qT                     -- by axSnd          <- and here
```

The first three steps are unconditional (require only distH).  The d1
hypothesis is used ONLY to bridge from `Snd (Snd (thmT y1T))` to a
pre-named `qT`.

### Guard vs BRA asymmetry, properly diagnosed

Guard's `mp("P", "P ⊃ Q") = "Q"` works because:
  * The inputs are CLOSED numerals.
  * `mp` is p.r., so the projection-to-"Q" happens INSIDE a closed
    p.r. computation — extensionality is trivial because all values
    are concrete numerals.
  * No symbolic canonicalization is needed because there is nothing
    symbolic at this stage.

BRA's `body_mp ... = Snd (Snd (thmT y1T))` is the EXACT analog at
the symbolic level — projection rather than named-qT.  We've been
imposing the d1 obligation as if `mp` should output a pre-named Q,
but Guard's `mp` actually outputs "the Snd-Snd projection of the
encoded ⊃-pair".  At Guard's level this projection IS Q by closed
numeric computation; at our symbolic level it's just `Snd (Snd ...)`
opaque.

### The fix

Define `body_mp_eval_proj` and `thmTDispMp_proj` that drop d1 and
return the Snd-Snd projection directly:

```agda
body_mp_eval_proj : (y1T y2T : Term) (bb : Term) ->
  Deriv (atomic (eqn (ap1 Snd bb)
                     (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
  Deriv (atomic (eqn
    (ap2 body_mp (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) bb)
    (ap1 Snd (ap1 Snd (ap1 thmT y1T)))))

thmTDispMp_proj : (y1T y2T : Term) (y1' x' : Term) ->
  Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
  Deriv (atomic (eqn
    (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)))
    (ap1 Snd (ap1 Snd (ap1 thmT y1T)))))
```

The original `thmTDispMp_param` becomes a thin wrapper:
`thmTDispMp_param ... d1 = ruleTrans (thmTDispMp_proj ...) (... d1 chain ...)`.

### Why this dissolves the blocker

Callers don't need `thmT y1T` to extensionally equal
`Pair tagImp (Pair pT qT)`.  They derive LOCAL equations about
`thmT y1T` (e.g., `thmT y1T = Pair tagImp Z` for opaque Z via a
single `subT_dist_Pair_tagImp` push), then apply `cong1 Snd` to get
`Snd (thmT y1T) = Snd (Pair tagImp Z) = Z`, then `cong1 Snd` again
to get the next layer.

Crucially: `Snd (Pair tagImp Z) = Z` works for ANY Z — opaque,
containing `cor x`, whatever.  We never have to descend into Z
structurally.

### Estimated cost

  * `body_mp_eval_proj` + `thmTDispMp_proj`: ~80 LoC, one-shot in
    BRA/Thm/ThmT.agda inside the existing abstract block.
  * Refactor of `body_mp_eval_param` / `thmTDispMp_param` as wrappers:
    ~30 LoC.
  * Phase C `step3_l` / `step5_l` rebuilt against the projection
    interface: ~150 LoC (replacing the canonicalization-blocked code).

**Total ~260 LoC** vs path (E)'s ~300-400.

### Concrete first-step tasks

  1. Add `body_mp_eval_proj` to BRA/Thm/ThmT.agda — copy the first
     three steps of `body_mp_eval_param`'s proof verbatim, drop the
     d1-dependent `e4 + e5` chain, return the e3 result.
  2. Add `thmTDispMp_proj` next to `thmTDispMp_param` — copy the
     dispatchOpens / skipAtTag scaffold verbatim, swap the final
     `body_mp_eval_param` for `body_mp_eval_proj`.
  3. Verify the file still typechecks.
  4. Build a one-line caller in a fresh test file showing
     `thmT (mp_step f_part D_thmT) = Snd (Snd (thmT (f_part x)))`
     for a concrete x.
  5. Then rewrite step3_l's mp dispatch using the projection
     interface; the d1-shaped canonicalization-through-Pair-of-cor-x
     drops out of the obligation entirely.
