# Next session — Theorem 14 Phase C blocker resolution

## TL;DR

Phase C's `step3_l` / `h_part_l` / `step5_l` need to derive
`thmT(y1T) = Pair tagImp (Pair pT qT)` for `thmTDispMp_param`'s d1
argument, where y1T is f_part / g_part / h_part / etc.  The
canonicalization gets stuck at deciding TreeEq with parametric `cor x`.

This session analyses the blocker and chooses ONE of three feasible
resolutions.  Read this whole file before coding — the redesign
choices are non-obvious and each has tradeoffs.

## Read first

  1. **This file** (you're reading it) — blocker analysis.
  2. `BRA/NEXT-SESSION-PHASE-C-CONTINUE-V2.md` — V2 session status
     (what's already landed: subT_codeFormula_atomic / _neg, h_part /
     g_part Pair-of-Comp2 unfolds, closed h_part_pre, step4_l_neg).
  3. `BRA/Th14SubTPushthrough.agda` — the canonicalization toolkit;
     the obstruction lives in `subT_dist_Pair_inner_via_TreeEq` 's
     Deriv obligation (line 838).
  4. `BRA/COR-AT-SB-LOAD-BEARING.md` — cor's specification & where
     it's needed.
  5. `CLAUDE.md` (project root) — ASCII-only conventions.

## The blocker, precisely

`step3_pre x` (CLOSED, no hypothesis):
```
thmT(f_part x) = subT(varCode2, i)
                      (subT(varCode1, sub_ii_subst)
                            (subT(varCode0, cor x)
                                  (reify (codeFormula t_formula))))
```
where t_formula = `(x_0 = x_2) imp ((x_1 = x_2) imp (x_0 = x_1))` .

For step3_l 's INNER mp dispatch (g_part_inner level):
  * y1T = f_part(x), y2T = D_thmT(x).
  * Need d1: thmT(f_part x) = Pair tagImp (Pair pT1 qT1) for some pT1, qT1.

To derive d1, canonicalize subT^3 on reify(codeFormula t_formula):

### Step (i): innermost subT.  WORKS.
`subT_codeFormula_imp` at n=0:
  innermost = Pair tagImp (Pair X1 Y1)
where:
  X1 = subT(varCode0, cor x)(reify (codeFormula eq02))
  Y1 = subT(varCode0, cor x)(reify (codeFormula (eq12 imp eq01)))

### Step (ii): expose X1's Pair shape.  WORKS (with `subT_codeFormula_atomic`).
X1 = Pair (subT(varCode0, cor x)(reify (code x_0)))
          (subT(varCode0, cor x)(reify (code x_2)))
   = Pair (cor x) varCode2T   -- after subT_node_match + subT distribution.

### Step (iii): outer subT(varCode1, ...) on Pair tagImp (Pair X1 Y1).  WORKS.
`subT_dist_Pair_tagImp`:
  result = Pair tagImp (subT(varCode1, sub_ii_subst)(Pair X1 Y1))

### Step (iv): inner subT(varCode1, ...) on (Pair X1 Y1).  STUCK.
For thmTDispMp_param 's d1 we need this to be a Pair (pT, qT).

`subT_dist_Pair_inner_via_TreeEq` requires a Deriv that
`TreeEq varCode1T (Pair X1 Y1) = falseT` .

By axTreeEqNN:
  TreeEq (Pair (reify tagVar) (reify (natCode 1))) (Pair (Pair (cor x) varCode2T) Y1)
  = IfLf (TreeEq (reify tagVar) (Pair (cor x) varCode2T))
         (Pair (TreeEq (reify (natCode 1)) Y1) (Pair O O))

The first IfLf-arg evaluation: by axTreeEqNN AGAIN at `Pair (cor x) varCode2T`,
  TreeEq (reify tagVar) (Pair (cor x) varCode2T)
  = IfLf (TreeEq (head-of-tagVar) (cor x))
         (Pair (TreeEq (tail-of-tagVar) varCode2T) (Pair O O))

The first IfLf-arg here: `TreeEq (some-Pair-shape) (cor x)`.

**STUCK.**  `(cor x) = ap1 cor x` is neither lf nor Pair.  None of
axTreeEqLL / axTreeEqLN / axTreeEqNL / axTreeEqNN fire.  The TreeEq
computation halts symbolically.

Even at instantiation (x := var 1 in closureToG), `cor (var 1)`
doesn't reduce: cor = Rec stepCor, and Rec only fires on lf / Pair
inputs, not var.

## Three feasible resolutions

### (A) "Cor-output-shape" lemma  [~200 LoC, no new axioms]

**Idea:** prove `Deriv (atomic (eqn (cor x) (reify (code <somet>))))`
for some t parametric in x, using cor's primitive-recursive defining
equations + structural analysis.

Specifically, for x : Term arbitrary, cor x BRA-equals
`reify (code <something-built-from-x>)` because cor IS the BRA functor
that takes a Term to its Goedel encoding (see Cor.agda's corOfReify
on closed inputs).

**Plan:**
  1. Add a derived lemma:
     `corOuterIsPair : (x : Term) -> Deriv (Or (atomic (eqn x O))
                          (Sigma Term2 (\ ab -> eqn (cor x)
                                  (Pair (encoded-tag) (encoded-rest)))))`
     -- structural analysis on x; ~6 cases (O / var / ap1 / ap2).
     For x = var n, cor x BRA-equals reify (code (var n)) =
     reify (nd tagVar (natCode n)) = Pair (reify tagVar) (reify (natCode n)).
     Etc.
  2. Use this lemma to derive
     `treeEqVarCodeOnCor : (n : Nat) (x : Term) ->
        Deriv (atomic (eqn (ap2 TreeEq varCodeNT (cor x)) someResult))`
     where someResult is computable (e.g., falseT for n's that don't
     match cor x's outer tag).
  3. Plug into `subT_dist_Pair_inner_via_TreeEq` 's hypothesis.

**Tradeoff:** requires careful case analysis on x's outer constructor.
Substantive but bounded.  ~200 LoC.

### (B) Restructure the chain  [~500 LoC, redesign]

**Idea:** redesign f_part / g_part / h_part / constr5 so parametric
cor x is NEVER substituted into a position that requires later subT
canonicalization through it.

**Plan:** instead of f_part substituting cor x at innermost via sb,
substitute a CLOSED placeholder (e.g., a fresh closed numeral encoding
"cor x" abstractly).  Then bridge from the closed-placeholder form to
the cor-x form via cong1 cor at a single OUTER step (NOT inside subT).

This requires rewriting:
  * Thm14Constr5Final.agda 's f_part_inner2 / f_part_inner1 / f_part
    (and h_part counterparts).
  * step3_pre / h_part_pre (closed prefixes).
  * Adding an OUTER cor-bridge derivation (~50 LoC).

**Tradeoff:** large redesign (~500 LoC) but produces a cleaner final
chain and avoids the TreeEq-stuck issue throughout.

### (C) Generalize subT distribution  [~300 LoC, new lemma]

**Idea:** derive a parametric distribution lemma
`subT_dist_param : (n : Nat) (tT : Term) (X Y : Term) ->
   <X has known outer shape (Pair _ _)> ->
   <Y is closed reify> ->
   Deriv (subT(p)(Pair X Y) = Pair (subT(p)X) (subT(p)Y))`
where the hypothesis is on X / Y 's structure (not on TreeEq).

The proof would NOT route through TreeEq.  Instead, it would use
axRecPNd directly + the structural assumption to compute the IfLf
result.

**Tradeoff:** requires careful axiomatization of "X has outer Pair
shape parametrically".  Fits into existing toolkit.  ~300 LoC.

## Recommendation

**Start with (A)**.  The cor-output-shape lemma is the most natural —
cor's range is precisely "encoded Trees", which always have the
correct outer shape for TreeEq-mismatch.  The proof is structural
analysis on the input (4 cases via Or).

If (A) hits a sub-blocker, fall back to (C).  (B) is reserved for
last-resort.

## Concrete first-step task

Build `BRA/CorOutShape.agda` with:

```agda
corOuterShape : (x : Term) ->
  Deriv (atomic (eqn (cor x) <some-canonical-form-on-x>))
```

For each case of x's outer constructor:
  * x = O: cor O = O (axRecLf on stepCor + axZ).
  * x = var n: cor (var n) STUCK; need an axiom or bridge.  HERE LIES
    THE SUB-BLOCKER -- cor is Rec, doesn't reduce on var.  Maybe use
    cor (var n) = reify (code (var n)) as a META-assumed property
    (or accept that Goedel II's closure operates at  x := var 1
    where var 1 IS a variable, requiring this clause).

NOTE: this specific sub-blocker is fundamental — cor as a BRA Fun1 is
not  TOTAL on Terms (only on reified Tree inputs).  The closure
treats `cor (var 1)` symbolically.  Resolution may require:
  * An explicit `cor_at_var : (n : Nat) -> Deriv (cor (var n) = reify (code (var n)))`
    derived  axiom (provable IF cor's Theorem 12 result is available).
  * OR redesigning the chain to avoid `cor (var 1)` symbolic appearance.

## Status of work landed before this session

(All Phase C V2 deliverables.  See NEXT-SESSION-PHASE-C-CONTINUE-V2.md.)

  * `BRA/Th14SubTPushthrough.agda` (1043 LoC, 0.14s) — full subT toolkit.
  * `BRA/Th14Step4Canonical.agda` (185 LoC, 0.67s) — step4_l_neg.
  * `BRA/Th14HUnfolds.agda` (261 LoC, 0.67s) — h_part Pair unfolds.
  * `BRA/Th14StepHPre.agda` (135 LoC, 0.67s) — closed h_part_pre.
  * `BRA/Th14GPartUnfolds.agda` (111 LoC, 0.69s) — g_part Pair unfolds.
  * `BRA/GoedelII.agda` — re-exports G_unfold.

All typecheck under 1s solo with cache.  No postulates / holes / dot
patterns / with-abstraction / new Deriv constructors.

## Constraints (unchanged)

  * ASCII only.
  * `--safe --without-K --exact-split` everywhere.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * No new Deriv constructors.
  * Per-file solo typecheck under 1s with cache.

## Open question for the next session

Can `cor (var n) = reify (code (var n))` be derived in BRA without
new axioms, using:
  * cor = Rec stepCor (definition).
  * The fact that `var n` is not a reified Tree input.
  * Some structural identity?

If YES: option (A) is viable end-to-end.
If NO: option (C) or (B) becomes necessary.

This is the FIRST thing to investigate.  ~30 minutes of focused work
will tell.
