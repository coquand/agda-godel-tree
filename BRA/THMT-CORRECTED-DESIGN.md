# thmT corrected design: outer-shape check + stored conclusion

**This document supersedes `BRA/THMT-EQUATIONS.md` and the obstruction
reports** (`BRA/THM14-STEP4-OBSTRUCTION.md`, the V3 plan's Option-A
discussion).  It captures the user-proposed design after the
correction that thmT must enumerate only theorems.

This is **architectural background** for an eventual rewrite.  No
code changes here.  The purpose is to verify, informally but in
detail, that the design supports Theorems 11, 12, 13, 14 of
guard15.pdf.

## Design summary

```
thmT y  =  if outerShapeOk y then Fst y else code(0=0)
```

i.e., thmT does an **outer-shape check** (closed-tag dispatch) at the
top.  On match, it returns `Fst y` (= the conclusion **stored** by the
encoding constructor).  On mismatch, it returns `code(0=0)` — a
default theorem code.

Encoding constructors compute the rule's conclusion **at construction
time** and store it in the `Fst` slot.  Sub-proof contributions appear
in the stored conclusion as symbolic `ap1 thmT (subproof)`
expressions.

## thmT definition

```
defaultConclusion : Term
defaultConclusion = reify (codeFormula (atomic (eqn O O)))   -- code "0 = 0"

-- shapeCheck y returns O when y has form  Pair _ (Pair tagT _)
-- with tagT one of the 40 recognised tags; otherwise returns Pair O O.
-- Built from IfLf + axTreeEq cascade on Fst (Snd y).
shapeCheck : Fun1

thmT : Fun1
thmT = ... combinator that reduces (parametrically in y) to:

  ap1 thmT y  =  ap2 IfLf (ap1 shapeCheck y)
                          (ap2 Pair (ap1 Fst y) defaultConclusion)
```

Concretely the reduction equation, combining `axIfLfL` and `axIfLfN`:

  * If `shapeCheck y = O`: `ap1 thmT y = ap1 Fst y`.
  * If `shapeCheck y = Pair O O`: `ap1 thmT y = defaultConclusion`.

For closed `y` not of recognised shape: shapeCheck reduces to `Pair O
O`, so thmT defaults to `code(0=0)`.

For closed `y` of recognised shape: shapeCheck reduces to `O`, so
thmT projects `Fst y`.

For `y` with KNOWN outer structure `Pair _ (Pair tagT _)` for closed
tagT (i.e., for any encoding-constructor output): shapeCheck reduces
to `O` parametrically (the closed `tagT` drives the cascade).  So
thmT reduces to `Fst y` parametrically.

For an **open Term variable** `x` (e.g., `var 1`): shapeCheck on `x`
is stuck (`Fst (Snd x)` doesn't reduce).  thmT(x) is symbolic.  This
is fine — **the closure never reduces thmT(open variable)**, it only
uses thmT-applications symbolically inside formulas.

## Encoding constructors

One per BRA rule.  Each constructor takes Term-level arguments
(possibly open) and returns a Term-level encoding.  The Fst slot
stores the rule's conclusion, computed using `ap1 thmT (sub-proof)`
for sub-proof contributions.

### Group A — leaf axioms (combinator defining equations)

For axI:
```
encAxI : Term -> Term
encAxI t = ap2 Pair (concAxI t) (ap2 Pair tagAxIT t)
   where concAxI t = reify (codeFormula (atomic (eqn (ap1 I t) t)))
                     -- = closed Term parametric in t, computed from t's structure
```

(Analogously for axFst, axSnd, axConst, axComp, axComp2, axLift,
axPost, axFan, axKT, axRecLf, axRecNd, axRecPLf, axRecPNd, axIfLfL,
axIfLfN, axTreeEqLL/LN/NL/NN, axGoodstein, axRefl, axEqTrans/Cong*,
axK, axS, axNeg, axExFalso, axContrapos.  Each takes the relevant
parameters as Term arguments and produces a closed-conclusion
encoding.)

### Group B — recursive rules

Each computes its conclusion from sub-proofs' stored conclusions, via
`ap1 thmT subProof` (= the sub-proof's stored conclusion when that
sub-proof is itself a constructed encoding):

**ruleSym** (1 sub-proof):
```
encRuleSym : Term -> Term
encRuleSym p = ap2 Pair (ap1 sym_codeF1 (ap1 thmT p))
                        (ap2 Pair tagRuleSymT p)
   where sym_codeF1 :: takes code (eqn t u), returns code (eqn u t)
```

**ruleTrans** (2 sub-proofs):
```
encRuleTrans : Term -> Term -> Term
encRuleTrans p q = ap2 Pair (ap2 trans_codeF2 (ap1 thmT p) (ap1 thmT q))
                            (ap2 Pair tagRuleTransT (ap2 Pair p q))
```

**cong1** (1 sub-proof + functor f as parameter):
```
encCong1 : Fun1 -> Term -> Term
encCong1 f p = ap2 Pair (cong1_codeF f (ap1 thmT p))
                        (ap2 Pair tagCong1T (ap2 Pair (codeF1T f) p))
```

(Similarly congL, congR.)

**mp** (2 sub-proofs):
```
encMp : Term -> Term -> Term
encMp pAnt pImp = ap2 Pair (ap2 mp_codeF2 (ap1 thmT pAnt) (ap1 thmT pImp))
                           (ap2 Pair tagMpT (ap2 Pair pAnt pImp))
```

**`mp_codeF2` MUST have safe defaults** (this was a bug in an
earlier version of this doc — see "Safe-default obligation" below).
Naive `Post (Comp Snd Snd) (Post Snd Pair)` makes Con refutable.
Correct definition:
```
mp_codeF2 a b
  =  if (Fst b == tagImp  AND  Snd (Fst (Snd b)) == a)
     then Snd (Snd b)        -- extract Q from a valid code(a ⊃ Q)
     else code(0=0)          -- safe default on malformed input
```
Both checks are TreeEq on closed structural data; reduce on closed
inputs and on the specific parametric-in-x codes that step 5's chain
produces (where outer tagImp is closed and the antecedent matches by
construction); only stay stuck on entirely-open Term variables that
don't arise in the chain anyway.

**ruleInst** (1 sub-proof + var index n + substituent t):
```
encRuleInst : Nat -> Term -> Term -> Term
encRuleInst n t p =
  ap2 Pair (ap2 sb (ap2 Pair t (reify (natCode n))) (ap1 thmT p))
           (ap2 Pair tagRuleInstT
                (ap2 Pair (reify (code (var n))) (ap2 Pair p t)))
```

**ruleIndBT** (3 sub-proofs):
```
encRuleIndBT : Term -> Term -> Term -> Term
encRuleIndBT p_base p_step p_ind =
  ap2 Pair (indBT_codeF (ap1 thmT p_base) (ap1 thmT p_step))
           (ap2 Pair tagRuleIndBTT (ap2 Pair p_base (ap2 Pair p_step p_ind)))
   -- indBT_codeF computes the conclusion from the base/step conclusions
```

**ruleF** (Schema F): similar.

### Specific encodings used by Goedel II step 4 / step 5

**Step 4's witness:**
```
constr5_step4 : Term -> Term
constr5_step4 x = encRuleInst 1 (ap1 cor x) x
                = ap2 Pair (ap2 sb (...) (ap1 thmT x))                   -- conclusion
                           (... encoding payload ...)
```

By the parametric defining equation:
```
ap1 thmT (constr5_step4 x) = ap2 sb (ap2 Pair (ap1 cor x) (reify (natCode 1)))
                                    (ap1 thmT x)
```

— this is exactly the sb-clause Goedel II step 4 needs.  Provable
parametrically in `x` by `axIfLf*` (closed tag) + `axFst`.

**Step 5's witness:** combines step 4's witness with a step 3 witness
and an `encMp` outer wrapper.  All three encoding constructors
(encRuleInst, encRuleInst, encMp) compose; thmT reduces parametrically
on each via outer-shape checks.

## Verification of Theorems 11, 12, 13, 14

### Theorem 11 (Goedel I)

Two ingredients:

* **`encode P deriv`**: structural recursion on the BRA `deriv`,
  building an encoding tree by applying the appropriate constructor
  at each step.  For each rule, the constructor stores the conclusion
  using `ap1 thmT (sub-encoding)`.  For closed sub-encodings (= what
  `encode` produces), `ap1 thmT (sub-encoding)` reduces to its stored
  conclusion (= `codeFormula sub-conclusion`).  By structural
  induction, `Fst (encode P deriv) = codeFormula P`, so
  `ap1 thmT (encode P deriv) = codeFormula P` (parametric in nothing
  — it's a closed equation, but follows from the parametric defining
  equation specialised to closed inputs).

* **`diagonal y deriv_G`**: identical to current `BRA/Thm11Diagonal.agda`.
  Uses `ruleInst` on hypothetical `Deriv G` + the closed equation
  `sub(i, i) = j`.  Never inspects thmT's definition.  **Unchanged.**

`thm11`: combine encode + diagonal exactly as currently done.
**Goedel I survives.** ✓

### Theorem 12

`thm12sing : (f : Fun1) (x : Term) -> Sigma Tree (\ d -> Deriv (atomic (eqn (ap1 thmT (reify d)) (codeFTeq (ap1 f x) (ap1 f x)))))`

In `BRA/Thm12Abstract.agda` this collapses to one line:
```
thm12sing f x = encode (atomic (eqn (ap1 f x) (ap1 f x))) (axRefl (ap1 f x))
```

With the new `encode`: produces the encoding tree of `axRefl (f x)`,
which is `encAxRefl (ap1 f x)`.  By the parametric defining equation
of thmT for tagAxRefl, `ap1 thmT (reify (encAxRefl (ap1 f x))) =
codeFormula (atomic (eqn (ap1 f x) (ap1 f x)))`.  ✓ Same result, same
shape.

(Analogously thm12bin.)  **Theorem 12 survives.** ✓

### Theorem 13

```
thm13sing f x y H = encode (atomic (eqn (ap1 f x) y)) H
```

Same one-line use of `encode`.  The encoding tree witnesses the
required equation.  **Theorem 13 survives.** ✓

### Theorem 14 (Goedel II)

The abstract chain in `BRA/Thm14Abstract.agda` takes `(thmT,
thClosed, codeF1Th_noVar, encode)` plus the new closure parameter
`(constr5, step5)`.  With the new design:

* `thClosed`: `substF1 x r thmT = thmT`.  Still needed (the closure
  uses `ruleInst` on Con and substitution on thmT must vanish on the
  closed combinator).  Holds for the new thmT iff `thmT`'s
  combinator definition contains no free variables — which is
  arrangeable (same as the current setup).
* `codeF1Th_noVar`: similar — substitution on the **code of** thmT
  vanishes.  Same property, same status.
* `encode`: rebuilt against the new constructor scheme, as described.
* `constr5` and `step5`: provided concretely.

**`step4` derivation** (parametric in `x : Term`):
```
A = atomic (eqn (ap1 thmT x) cG)                       -- hypothesis
B4 = atomic (eqn (ap1 thmT (constr5_step4 x))
                  (... code of "th(<x_>) ≠ sub(i,i)" ...))
```

By the parametric defining equation of thmT:
```
   ap1 thmT (constr5_step4 x)
 = ap2 sb (Pair (cor x) (numCode 1)) (ap1 thmT x)         -- Definition 12 line 2 parametrically
```

Under hypothesis A (`ap1 thmT x = cG`):
```
   ap2 sb (Pair (cor x) (numCode 1)) (ap1 thmT x)
 = ap2 sb (Pair (cor x) (numCode 1)) cG                   -- by congruence with A
 = code(G[x_1 := num x])                                  -- by sbForOutRuleInst
 = code "th(<x_>) ≠ sub(i,i)"                              -- by definition of G
```

Step 4 internal-implication: `Deriv (A imp B4)` is built from
parametric defining equation + sbForOutRuleInst + axEqCong + standard
propositional combinators.  ✓ Mechanical.

**`step5` derivation**: analogous, combining step-3 (via Thm 13),
step-4, and `encMp` twice.  Parametric defining equations of thmT for
both `tagRuleInst` (sb-clause) and `tagMp` (mp-clause) are used.
Each reduction is parametric by the outer-shape-check + axFst
mechanism.  ✓ Mechanical.

**`closureToG`**: unchanged from current form — uses `step5_at1`,
`axContrapos`, `ruleInst Con`, `mp`, `notEqTransport`, `eqSubst`
G_unfold.  Propositional-only; doesn't depend on thmT's internal
structure.  ✓

**Goedel II survives.** ✓

## Safe-default obligation on auxiliaries

Guard's `mp(P, P⊃Q) = Q` (Exercise 24 [1]) is a **partial**
specification.  It tells us what mp does on *valid* `(P, P⊃Q)`
inputs, and is silent on malformed cases.  The same holds for `sb`,
`ind`, `ax` — Exercise 24's specifications are partial.

A naive implementation of `mp_codeF2` as `Snd ∘ Snd` of the second
argument refutes Con immediately: for the closed junk tree
```
y_bad = Pair (mp_codeF2 anything (encode-of-(anything imp 0=1)))
             (Pair tagMpT garbage)
       = Pair code(0=1) (Pair tagMpT garbage)
```
shapeCheck passes (closed tagMpT recognised), thmT routes to `Fst
y_bad = code(0=1)`, BRA proves `thmT(y_bad) = code(bot)` via
`axFst`, contradicting Con.  Goedel II becomes vacuous.

**Fix:** every code-level auxiliary (`mp_codeF2`, `sb`, `sym_codeF1`,
`trans_codeF2`, `cong*_codeF`, `indBT_codeF`, `ax_codeF1`) MUST route
malformed inputs to a safe theorem code (e.g., `code(0=0)`).
Concretely:

* `mp_codeF2 a b`: check `Fst b = tagImp` AND `Snd(Fst(Snd b)) = a`;
  on success return `Snd(Snd b)`, else `code(0=0)`.
* `sb a b P`: check `P` has formula-code outer shape (tagAtom /
  tagNeg / tagImp); on success do codedSubst, else `code(0=0)`.
* Similarly for the other auxiliaries.

This is **a design constraint Guard implicitly assumes** but does
not spell out.  Any honest formalisation has to make it explicit;
implementation cost is small (an `IfLf`-on-closed-tag wrapper around
each auxiliary's body).

The safe-default check on `mp_codeF2` does not break parametric step 5
reasoning, because in the actual chain the codes flowing in have
**closed outer structure** (parametric-in-x codes whose outermost
tag is `tagImp` — a closed value) and **antecedents that match by
construction**, so both checks reduce parametrically (TreeEq on
syntactically-equal parametric-in-x codes is reflexive, parametric).

## thmT enumerates exactly the theorems

Guard's stated property — *"th(0), th(1), … enumerates the Gödel
numbers of all and only the theorems of BRA"* — re-checked:

* **All theorems**: for every `Deriv P`, `encode P deriv` produces a
  tree `y` with `ap1 thmT (reify y) = codeFormula P`.  By construction.

* **Only theorems**: every value of thmT is a theorem code.
  Verified by cases:
  * Outer-shape mismatch ⟹ thmT returns `code(0=0)` — a theorem. ✓
  * Outer-shape match ⟹ thmT returns `Fst y`.  Provided every
    auxiliary has safe defaults (above), the stored `Fst` slot
    can only be a theorem code: each constructor produces either
    a real theorem code (when sub-proofs are valid) or `code(0=0)`
    (when an auxiliary's safety check fires on malformed sub-proof
    output).  By induction over encoding construction.  ✓

So thmT's range = theorem codes.  **Guard's property holds**, given
the safe-default obligation.  Without it, Con is refutable and
Goedel II vacuous — for both Guard's BRA and any faithful port.

## On "Agda meta-equality vs BRA-internal Deriv"

A clarifying note on a subtle framing question.

The parametric defining equations have the shape

  `Deriv (atomic (eqn (ap1 thmT (constr5 x)) (ap2 sb (...) (ap1 thmT x))))`

— a BRA-internal `Deriv`, parametric in `x : Term`.  This is **not**
the same as an Agda propositional equality `Eq (ap1 thmT (constr5 x))
(ap2 sb (...) (ap1 thmT x))`: Agda Eq between two `ap1` Term
expressions does not hold definitionally, since `ap1` is a Term
constructor and `thmT` is a Fun1 constant — neither reduces in
Agda's term language.

What the corrected design buys is that the BRA-internal Deriv is
provable from **standard primitive axioms already in
`BRA/Deriv.agda`** (`axFst` + `axIfLfL`/`axIfLfN` + `axTreeEq*`),
parametric in `x`.  No new BRA axioms needed; no Definition 12
extension.  In contrast, the existing `Rec O stepProto` thmT only
admits the parametric Deriv via dispatch lemmas that fail on open
Term variables — hence the obstruction.

So the substantive insight stands: **no foundation extension is
required**.  The framing should be "the parametric defining
equations follow trivially from `axFst` once the encoding stores
the conclusion", not "the equations live at Agda meta-level".

Agda-level `eqSubst` does help glue Deriv chains together (e.g.,
when transporting along `thClosed` in the closure step), but the
parametric defining equations themselves are BRA-Deriv objects.

(Caveat: the soundness of code-level operations on theorem-code
inputs is itself meta-level reasoning, not a BRA-internal claim.
This matches Guard's situation: "th enumerates only theorems" is a
meta-claim, not BRA-derivable.)

## Detail: handling the symbolic `ap1 thmT (subProof)` in stored conclusions

When an encoding stores `ap1 thmT subProof` (e.g., `encMp pAnt pImp`
stores `mp_codeF2 (ap1 thmT pAnt) (ap1 thmT pImp)`), the question is
what this evaluates to:

* For closed `subProof = reify y` where `y` is a valid encoding tree:
  `ap1 thmT (reify y)` reduces via outer-shape-check to
  `Fst (reify y)` = the stored conclusion of `y` = a closed Term
  representing a theorem code.  Composition gives a closed theorem
  code as the stored conclusion of the new encoding. ✓
* For closed `subProof = reify y` where `y` is junk (no recognised
  shape): `ap1 thmT (reify y)` reduces to `code(0=0)`.  Composition
  via `mp_codeF2`/`sb`/etc. produces some closed Term — a theorem
  code if the operation is sound on theorem-code inputs (and `code(0=0)`
  is a theorem code, so the input *is* a theorem code, so the output
  is a theorem code by the operation's soundness).  ✓
* For open `subProof = x` (a Term variable, used in step-4-style
  parametric reasoning): `ap1 thmT x` does **not** reduce — it
  remains symbolic.  The stored conclusion is a Term containing
  `ap1 thmT x` symbolically.  The parametric defining equation of
  thmT reads `ap1 thmT (encT x) = ... ap1 thmT x ...` — both sides
  are well-typed Terms, and the equation is BRA-derivable
  parametrically (by `axIfLf*` + `axFst`).  ✓

## Concerns / open questions

1. **shapeCheck combinator**.  Built from `IfLf` + 40-way `TreeEq`
   cascade on `Fst (Snd y)`.  For closed `Fst (Snd y) = tagT` (closed
   tag), the cascade reduces.  For open `y`, doesn't reduce — which
   is fine, because we never need thmT(open y) to reduce.  But:
   shapeCheck must itself be a Fun1.  Building a 40-step cascade as a
   Fun1 is straightforward (mirrors stepProto's existing structure).

2. **`encode`'s structural recursion** on `Deriv P`.  Each rule has
   its own constructor; the recursion mechanically descends.  No new
   primitives needed.  Workload comparable to the current
   `BRA/Thm/ThmT.agda`'s 40 dispatch lemmas, but each lemma's
   *content* is dramatically simpler (no IfLf cascade unfolding —
   just construct the tree, the equation follows by `axFst`).

3. **`thClosed` and `codeF1Th_noVar`**.  Need to be re-verified for
   the new thmT's combinator definition.  thmT now uses IfLf, Pair,
   shapeCheck.  As long as none of these have the substituted
   variable free (closed primitives only), thClosed holds.  Should be
   the case — same situation as current thmT.

4. **Auxiliary code-level operations** (`mp_codeF2`, `sym_codeF1`,
   `cong1_codeF`, `indBT_codeF`, `sb`).  Need to be defined as actual
   combinators.  `sb` is already done.  `mp_codeF2 = Post (Comp Snd
   Snd) (Post Snd Pair)`.  Others are similar projections /
   combinations of existing primitives.  Expected workload: ~50–100
   LoC of definitions.

5. **`Goedel I encode` reproof**.  Estimated 500-1500 LoC: one
   constructor per BRA rule (~30-50 LoC each, including the
   defining-equation lemma per rule).  But each is structurally
   trivial — no IfLf cascade or shape proofs, just tree construction.
   This is *much smaller* than the current 9000 LoC `BRA/Thm/ThmT.agda`.

6. **Old `BRA/Thm/ThmT.agda` deletion?**  The current 9000-LoC file
   becomes obsolete in this design.  Could be retained as a
   historical artifact or deleted.  Goedel I + thm11 would be re-derived
   with the new encode, ~1000 LoC total.

7. **Is the outer-shape check Pair O O / O encoding correct?**  In
   our BRA, `O` denotes leaf and `Pair O O` denotes the boolean
   `false` (per `BRA/Deriv.agda`'s `falseT = ap2 Pair O O`).
   `axIfLfL` and `axIfLfN` dispatch on `O` vs `Pair _ _` in the first
   argument.  So shapeCheck-returns-`O` correctly takes the Fst
   branch, shapeCheck-returns-`Pair _ _` takes the default branch.
   Matches the existing IfLf semantics.  ✓

## What this design changes vs. what it preserves

**Preserved:**
* `BRA/Sb.agda`, `BRA/SbAxiom.agda` — the sb infrastructure.
* `BRA/Thm11Diagonal.agda` — diagonal lemma is propositional.
* `BRA/Thm14Abstract.agda` — contract surface unchanged
  (constr5/step5 with the same internal-implication shape).
* `BRA/GoedelII.agda` — Compose module unchanged.
* All foundation primitives in `BRA/Deriv.agda` — no new axioms.

**Replaced/rewritten:**
* `BRA/Thm/ThmT.agda` — the 9000-LoC concrete thmT and its 40
  dispatch lemmas.  Becomes a much smaller file with the new
  thmT definition + 40 encoding constructors + their parametric
  defining equations (each a one-liner via axIfLf* + axFst).

**Added:**
* The new encoding-constructors module (one per BRA rule).
* Auxiliary code-level operations (`mp_codeF2` etc., minus already-
  built `sb`).

**Newly enabled:**
* Parametric defining equations of thmT — by axFst on the stored
  conclusion, with the outer-shape-check ensuring valid inputs reach
  the Fst branch.
* Goedel II step 4 and step 5, mechanically.

## Remaining check before commitment

The user asked for a careful informal verification that this design
supports Theorems 12-14.  Items requiring further scrutiny:

* **Ind-rule's `indBT_codeF`**: its precise specification (what code
  does it produce from the base/step sub-proofs' codes?).  Should
  match Guard's `ind` from Definition 12 line 4.
* **Schema F's encoding**: same; the encoding for `ruleF` (uniqueness
  of Rec) needs a concrete code-level operation.  May or may not be
  needed for Goedel II (Thm 14 doesn't seem to use Schema F directly,
  per Guard's argument).
* **Concrete realisation of `concAxRefl`, `concAxK`, `concAxS`**,
  etc.: each axiom's code-level "instance" (= the conclusion code as
  a function of the axiom's parameters).  Standard projections /
  reify-of-codeFormula expressions.
* **Verifying `thClosed` and `codeF1Th_noVar`** against the new thmT:
  if shapeCheck and the IfLf wrapping don't introduce free Term
  variables, holds.  Quick check.

If all these check out, the design is ready to implement.

---

**Provisional verdict.** The design appears to support Theorems 11–14
correctly:

* Goedel I: existing `diagonal` works unchanged; `encode` is rebuilt
  but follows the same structural-recursion pattern.
* Goedel II step 4 and step 5: mechanically derivable from the
  parametric defining equations (`axIfLf*` + `axFst`) plus already-
  built `Sb` infrastructure.
* "thmT enumerates only theorems": holds, with the explicit `code(0=0)`
  default on outer-shape mismatch and the soundness of code-level
  operations on theorem-code inputs (by induction).

The implementation cost is moderate.  Realistic breakdown:

  * New thmT definition + shapeCheck combinator: ~100 LoC, 1 short
    session.
  * 40 encoding constructors with stored conclusions: ~50–100 LoC
    each, totaling 2000–4000 LoC, ~2–3 sessions of mechanical work.
  * Safe-default auxiliaries (`mp_codeF2`, `sb` augmented, `ax`,
    `ind`, structural rules' code-level operations): ~300–500 LoC,
    1 session.
  * Re-derive `encode` + `thm11` (Goedel I): ~500–1000 LoC, 1 session.
  * Build `step4`, `step5`, `closureToG` instantiation (Goedel II):
    ~500–1000 LoC, 1–2 sessions.

Total: **~3000–5000 LoC**, **5–7 sessions** for a thorough job.
Replaces the 9000 LoC current `BRA/Thm/ThmT.agda` with cleaner code.
Foundation unchanged; existing `Sb` / `SbAxiom` / `Thm14Abstract` /
`GoedelII` / `Thm11Diagonal` infrastructure all preserved.

Worth proceeding once the four "remaining check" items above are
informally satisfied.
