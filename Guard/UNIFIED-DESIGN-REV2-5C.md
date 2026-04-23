# [unify-5c] Gödel II chain on the hyp-free stack

Detailed design for the [unify-5c] step of the Option G / REV2
unification plan.  See UNIFIED-DESIGN-REV2.md for background and
[unify-5a], [unify-5b] commit messages for the preceding work.

## Prerequisites (all shipped as of commit 9298b61)

- `Guard.DerivF`                   — hyp-free Deriv over Formula.
- `Guard.ThFunTForHF`              — hyp-free `thmT : Fun1` with
                                     `codeTrueT` sentinel.
- `Guard.ThFunTForV3DefsUnify`     — reduction machinery on HF.
- `Guard.ThFunTForV3PassUnify`     — HF passthrough chains.
- `Guard.ProofEncUnify`            — all axiom/rule encoders without
                                     hCode, except `encRuleHyp`
                                     (removed).
- `Guard.ProofEncFormula`          — formula-level encoders
                                     (encAxK/S/Neg/Mp) without hCode.
- `Guard.SubstTForPrecompClassicalUnify` — gsCR, cGSCR, templateCodeCR,
                                     crTCCR ready to use.  Note:
                                     `diagFTargetCR` is NOT yet ported
                                     to the hyp-free Unify stack; see
                                     STEP 1 of the current handoff.

## Goal

Prove Gödel II constructively as

```agda
godelIIHF : Prov conHFEq -> Prov botEq
```

where

```agda
Prov : Formula -> Set
Prov P = Sigma (e : Term) (Deriv (atomic (eqn (ap1 thmT e)
                                             (reify (codeFormula P)))))

conHFEq : Formula
conHFEq = atomic (eqn (ap2 TreeEq (ap1 thmT (var v1)) codeBotT) falseT)
-- internal consistency: for all var 1, thmT(var 1) != codeBotT
-- (uses var 1 to keep out of gsCR's proof slot at var 0)

botEq : Formula
botEq = atomic (eqn O falseT)   -- "0 = 1"
```

The proof factorizes via Guard's Theorem 11 (Gödel I) as:

```
godelIIHF = godelI ∘ chainConToGs
chainConToGs : Prov conHFEq -> Prov gsCR
godelI       : Prov gsCR    -> Prov botEq
```

No `Consistent` assumption, no `Empty` conclusion; the classical form
falls out as contrapositive at the consumer site.

## Architecture invariants

Carried over from REV2:

- `thmT` stays a VALIDATOR (malformed input -> `codeTrueT`, not O).
- No hyp, no hCode, no ruleHyp, no case26, no thm14EV3 recursor.
- Everything stays in equation-level form (`atomic (eqn …)`); Guard's
  formula-level `~` is avoided — equational manipulation via
  `treeEqSelfReify` closes the self-application directly.
- All encoders compose; encoded proofs built **in parallel** with
  Deriv proofs, never extracted by a Deriv-generic recursor.

## Variable correspondence with guard15.pdf

| guard15 | ours (SubstTForPrecompClassicalUnify) |
|---------|---------------------------------------|
| `x₀`    | `var 1` (diagonalized away by `substEq v1 (reify templateCodeCR)`) |
| `x₁`    | `var zero` — the remaining free variable, the **proof slot** |
| `i`     | `reify (codeEqn templateCR)` (roughly — more precisely the `templateCodeCR` combined with `cor`) |
| `j`     | `reify cGSCR` |
| `th`    | `thmT : Fun1` |
| `sub`   | `substOp : Fun2` |
| `Df`    | `D1 f : Fun1` (to define in Guard.Thm13) |
| `Dg`    | `D2 g : Fun2` (to define in Guard.Thm13) |

## Components

### (1) Guard.Thm13  [~800 lines]

Mutually-recursive encoder functors for arbitrary Fun1/Fun2, and
their correctness lemmas.

#### Signatures

```agda
D1 : Fun1 -> Fun1
D2 : Fun2 -> Fun2

thm13Fun1 : (f : Fun1) (xC yC : Term) ->
  Deriv (imp (atomic (eqn (ap1 f xC) yC))
             (atomic (eqn (ap1 thmT (ap1 (D1 f) xC))
                          (reify (codeFormula (atomic (eqn (ap1 f xC) yC)))))))

thm13Fun2 : (g : Fun2) (x1C x2C yC : Term) ->
  Deriv (imp (atomic (eqn (ap2 g x1C x2C) yC))
             (atomic (eqn (ap1 thmT (ap2 (D2 g) x1C x2C))
                          (reify (codeFormula (atomic (eqn (ap2 g x1C x2C) yC)))))))
```

#### Cases

**Fun1 constructors to handle:**
- `I`      — base case, Deriv reduces `I(x) = x` via axI; encoder emits `encAxI`.
- `Fst`    — axFst; `encAxFst`.
- `Snd`    — axSnd; `encAxSnd`.
- `KT t`   — axKT; `encAxKT`.
- `Comp f g`   — inductive: combine `D1 f` and `D1 g`.
- `Comp2 h f g` — inductive: combine `D2 h`, `D1 f`, `D1 g`.
- `Rec z s`    — axRecLf + axRecNd base cases + inductive.
- `RecP s`     — axRecPLf + axRecPNd.

**Fun2 constructors to handle:**
- `Pair`   — base; `encAxPair`? (axiom for Pair is… identity-like; needs encoder).
- `Const`  — axConst; `encAxConst`.
- `Lift f` — axLift; combines with `D1 f`.
- `Post f h` — axPost; combines with `D1 f` and `D2 h`.
- `Fan h1 h2 h` — axFan; combines with `D2 h1, D2 h2, D2 h`.
- `IfLf`   — axIfLfL + axIfLfN base cases.
- `TreeEq` — axTreeEqLL + axTreeEqLN + axTreeEqNL + axTreeEqNN base cases.

**Inductive step pattern** (sketch for `Comp f g`):

```
D1 (Comp f g) = (Fun1 built from D1 f, D1 g, and encoded axComp and encMp)
```

The implementation of `D1 (Comp f g)` is a Fun1 expression that, when
applied to xC, produces a Term that encodes the proof
```
  Comp f g (x) = f (g x)                    [axComp]
  g(x) = y1                                  [subproof]
  f(y1) = y                                  [subproof]
  ---------------------                      [transitivity]
  Comp f g (x) = y
```
This is encRuleTrans composed with encoded axComp and the sub-proofs
from `D1 g` (for `g x = y1`) and `D1 f` (for `f y1 = y`), with
appropriate instantiations.

**Mutual recursion:** `D1 (Comp2 h f g)` uses `D2 h` and `D1 f`, `D1 g`.
`D2 (Post f h)` uses `D1 f` and `D2 h`.  Etc.  The mutual structure
matches Guard's Thm 12 meta-induction on functor length.

#### Scope discipline

- `Guard.Thm13` imports `Guard.ProofEncUnify` and `Guard.ProofEncFormula`.
- No new Deriv axioms.  All work done via existing encoders +
  `Guard.DerivF` rules.
- Correctness lemmas use `encRuleTransCorr`, `encMpCorr`, etc.

### (2) Prov predicate + combinators  [~200 lines]

New module `Guard.Prov`.

```agda
Prov : Formula -> Set
Prov P = Sigma (e : Term) (Deriv (atomic (eqn (ap1 thmT e)
                                             (reify (codeFormula P)))))

provMp    : Prov (imp P Q) -> Prov P -> Prov Q
provInst  : (x : Nat) (t : Term) (P : Formula) ->
            Prov P -> Prov (substForm x t P)
provTrans : Prov (atomic (eqn a b)) -> Prov (atomic (eqn b c)) ->
            Prov (atomic (eqn a c))
provSym   : Prov (atomic (eqn a b)) -> Prov (atomic (eqn b a))
provCongL : (g : Fun2) (x : Term) ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap2 g t x) (ap2 g u x)))
provCongR : (g : Fun2) (x : Term) ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap2 g x t) (ap2 g x u)))
-- and similar wrappers around existing encoder lemmas
```

Implementations use `encMp`, `encRuleInst`, `encRuleTrans`,
`encRuleSym`, `encCongL`, `encCongR` from ProofEncUnify.  Each
combinator bundles the Term-level encoder output with the
Deriv-level correctness witness.

### (3) Guard.GodelI  [~150 lines]

```agda
godelI : Prov gsCR -> Prov botEq
```

Construction:
1. Let `(e_G, d_G) : Prov gsCR`.  So
   `d_G : Deriv (atomic (eqn (ap1 thmT e_G) (reify cGSCR)))`.
2. `provInst zero e_G (atomicForm gsCR) (e_G, d_G)` — instantiate the
   proof slot at e_G itself.  Result:
   `(e_inst, d_inst) : Prov (substForm zero e_G (atomicForm gsCR))`.
   After substitution, the atomic form becomes:
   ```
   atomic (eqn (ap2 TreeEq (ap1 thmT e_G) (reify cGSCR)) falseT)
   ```
3. Build `Prov (atomic (eqn (ap2 TreeEq (ap1 thmT e_G) (reify cGSCR)) O))`
   via `provCongL TreeEq (reify cGSCR) (e_G, d_G)` composed with
   encoded-treeEqSelfReify applied to cGSCR.
4. `provTrans` of step 3 (symmetric) and step 2:
   `Prov (atomic (eqn O falseT))` = `Prov botEq`.

Key subtlety: `treeEqSelfReify` needs to be available in
encoded/Prov form.  Either:
- Wrap it as `provTreeEqSelfReify : (t : Tree) -> Prov (atomic (eqn (ap2 TreeEq (reify t) (reify t)) O))`.
- Implementation: induction on `t` using encAxTreeEqLL /
  encAxTreeEqNN + encCong + encRuleTrans — mirroring the existing
  `treeEqSelfReify` proof.  ~50 lines.

### (4) Guard.GodelII  [~300 lines]

```agda
chainConToGs : Prov conHFEq -> Prov gsCR
godelIIHF    : Prov conHFEq -> Prov botEq
godelIIHF conPf = godelI (chainConToGs conPf)
```

Implementation of `chainConToGs`:

Steps 1-5 from guard15.pdf p.17, each producing a Prov.

**Step 1** (Thm13Fun1 at `f = thmT`, `yC = reify cGSCR`):
```
step1Prov : Prov (imp (atomic (eqn (ap1 thmT (var 0)) (reify cGSCR)))
                      (atomic (eqn (ap1 thmT (ap1 (D1 thmT) (var 0)))
                                   (reify (codeFormula (atomic (...step1RHS...)))))))
```
Obtained by wrapping `thm13Fun1 thmT (var 0) (reify cGSCR)` with Prov.

**Step 2** (Thm13Fun2 at `g = substOp`, closed args):
Requires discharging the Thm13Fun2 LHS hypothesis via `diagFTargetCR`:
```
step2Deriv : Deriv (atomic (eqn (ap2 substOp argL argR) (reify cGSCR)))
step2Deriv = diagFTargetCR    -- already shipped

step2Prov : Prov (atomic (eqn (ap1 thmT (ap2 (D2 substOp) argL argR))
                              (reify (codeFormula ...step2RHS...))))
step2Prov = provMp (thm13Fun2 substOp argL argR (reify cGSCR)) (diagFTargetCRProv)
```
where `argL = reify crTCCR` and `argR = reify templateCodeCR`.

**Step 3** (combine via encoded ax(4) + encMp):
```
step3Prov : Prov (imp (atomic (eqn thmT_x cGSCR))
                      (atomic (eqn (ap1 thmT gx)
                                   (reify (codeFormula "thmT x = substOp(argL, argR)")))))
```
`gx` is a specific Term: `encMp (encMp encTrans4 step1-hx) step2-hx`
or similar, where encTrans4 = encoded axiom `x₀ = x₂ ⊃ x₁ = x₂ ⊃ x₀ = x₁`.

Note: axiom ax(4) (Guard's transitivity) is derivable in our DerivF
from ruleTrans + propositional encoders.  Need to establish
`encTrans4` as a specific encoded proof term, ~30 lines.

**Step 4** (rewrite RHS by definition of cGSCR):
```
step4Prov : Prov (imp (atomic (eqn thmT_x cGSCR))
                      (atomic (eqn (ap1 thmT hx)
                                   (reify (codeEqn gsCR)))))
```
Since `reify cGSCR = reify (codeEqn gsCR)` by definition (cGSCR
literally IS codeEqn gsCR), step 4 is essentially step 3 with a
rewrite.  May be a no-op in our equational formulation.

Wait — cGSCR IS `codeEqn gsCR`, not `codeFormula (atomic gsCR)`.
These differ by a tag for `atomic`.  So step 4 needs a small bridge
`codeEqn e = codeFormulaUnderAtomic e` or similar.  TBD once we
look at the actual `codeFormula` vs `codeEqn` relationship.

**Step 5** (combine step 3 and step 4 via encoded ax(t') + encMp):
Axiom t' = `x₀ = x₁ ⊃ x₀ ≠ x₁ ⊃ 0 = 1`.  In equational form we
don't need this as a separate axiom — from `thmT(hx) = codeOf(gsCR)`
and from `thmT(var 0) = cGSCR`, combined with `treeEqSelfReify` on
cGSCR, we get `codeOf(TreeEq (thmT hx) cGSCR = falseT)` via the
gsCR-instantiation argument.

Actually — step 5 in equational form is:
```
step5Prov : Prov (imp (atomic (eqn (ap1 thmT (var 0)) (reify cGSCR)))
                      (atomic (eqn (ap1 thmT φx) codeBotT)))
```
where φx combines step 3's hx, step 4's continuation, and encoded
treeEqSelfReify + encoded TreeEq-falseT axiom.  Roughly:
```
φx = (specific composition of encMp applied to encoded transitivity,
      step 3/4 encoded sub-proofs, and encoded treeEq-self)
```

**Final step — chainConToGs**:

Assume `(e_conH, d_conH) : Prov conHFEq`.

- From conHFEq: provInst at var 1 := φx gives a Prov of
  `atomic (eqn (TreeEq (ap1 thmT φx) codeBotT) falseT)`.
- From step5Prov: under hypothesis `thmT(var 0) = cGSCR`, we have
  `thmT(φx) = codeBotT`.
- Combined via encMp and equational transitivity:
  `Prov (atomic (eqn (TreeEq (ap1 thmT (var 0)) (reify cGSCR)) falseT))`
  = Prov gsCR (the equational form).

This IS Prov gsCR.  Return it.

### (5) Compose

```agda
godelIIHF : Prov conHFEq -> Prov botEq
godelIIHF conPf = godelI (chainConToGs conPf)
```

## Ordering and commits

Suggested commit sequence:

1. `[unify-5c-thm13-fun1]` — D1 and thm13Fun1 for Fun1.  Base cases
   first (I, Fst, Snd, KT), then inductive (Comp, Rec, RecP,
   Comp2 — the last depends on D2 so may need stub).
2. `[unify-5c-thm13-fun2]` — D2 and thm13Fun2 for Fun2.  Mirrors
   above.
3. `[unify-5c-thm13-mutual]` — close the mutual recursion between
   Comp2, Post, Fan, etc.  Final typecheck of Guard.Thm13.
4. `[unify-5c-prov]` — Prov predicate + combinators.
5. `[unify-5c-prov-treeeqself]` — encoded treeEqSelfReify in Prov form.
6. `[unify-5c-godel1]` — Prov gsCR -> Prov botEq.
7. `[unify-5c-chain-step1to3]` — chain steps 1-3.
8. `[unify-5c-chain-step4to5]` — chain steps 4-5.
9. `[unify-5c-chainContoGs]` — final assembly.
10. `[unify-5c-godel2]` — godelIIHF by composition.

Each step typechecks independently.  No postulates, no holes.

## Scope NOT in [unify-5c]

- Deleting legacy modules (Step, Provable, BRA, GodelIIBRAv2, the
  non-Unify ThFunTForV3 chain, old ProofEnc) → that's [unify-5d].
- Renaming -Unify → final names → also [unify-5d].
- Classical Gödel I (`Consistent -> Deriv gsCR -> Empty`) → out of
  scope; requires thm14EV3-style recursor.  Consumers who want the
  classical form compose `godelIIHF` with their own Consistent
  hypothesis: `Consistent = ~Prov botEq`, so the contrapositive
  `Consistent -> ~Prov conHFEq` follows directly.

## Open questions to resolve during implementation

1. **codeEqn vs codeFormula:** our `cGSCR = codeEqn gsCR` codes an
   Equation; `codeFormula (atomic gsCR)` codes the wrapped Formula.
   These differ by the `atomic` tag.  Need a small equational bridge
   or restatement — easiest to establish early.

2. **Prov instantiation boilerplate:** for each `provInst` call we
   need `substForm` to produce the right Term.  Establish
   `provInstAtomic : (x : Nat) (t : Term) (a b : Term) -> Prov (atomic (eqn a b)) -> Prov (atomic (eqn (subst x t a) (subst x t b)))` as a convenience wrapper.

3. **`D1 thmT` explicit form:** `thmT` is itself `Rec O thmTStep`.
   `D1 (Rec z s)` needs special handling since the recursion-structure
   case is non-trivial.  May need to treat `D1 thmT` as a primitive
   abbreviation with its own correctness lemma, rather than deriving
   it from the generic Rec case.

4. **Axioms ax(4) and ax(t') in encoded form:** these are classical
   propositional axioms in guard15 but in our DerivF formulation
   they may be either (a) primitive Deriv rules or (b) derivable from
   encAxK/S/Neg + existing constants.  Sketch the derivations before
   committing to a module structure.

## Fresh-session bootstrap

If this work is resumed in a fresh session:

1. Read this document.
2. Read `UNIFIED-DESIGN-REV2.md`.
3. Read `~/.claude/projects/-Users-coquand-CHWISTEK/memory/project_unified_hypfree.md`.
4. Skim `Guard.ThFunTForHF`, `Guard.ProofEncUnify`,
   `Guard.SubstTForPrecompClassicalUnify` for type signatures.
5. Check recent commits: `git log --oneline -20` should show
   [unify-5b-substprecomp] as the most recent Option-G commit
   (commit 9298b61).
6. Start on Guard.Thm13 base cases (I, Fst, Snd, KT) first — these
   are simplest, exercise the encoder machinery, and surface any
   codeEqn/codeFormula bridging issues early.
7. Typecheck with `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split Guard/Thm13.agda`.
