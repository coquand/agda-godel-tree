# Soundness push — Step 1 audit findings (do NOT execute the previous prompt verbatim)

This file supersedes `BRA/NEXT-SESSION-SOUND-THMT.md` for one cycle.
The previous prompt's design has three architectural mismatches that
were not visible until a careful read of `BRA/SoundMpProto.agda` against
the consumer call sites. None can be fixed by retrying — each demands
either a re-architecture or a deliberate widening of scope.

These are not "fast typecheck" violations. The Guard mathematics is
light and the proof never relies on heavy normalization; that rule is
about runtime, not design. The three blockers below are plain
structural defects: a buggy combinator (Blocker 1), a signature that
does not match consumer reality (Blocker 2), and missing
infrastructure (Blocker 3). They would surface as `type mismatch` /
`unsolved goal` — not as slow files — and they need to be fixed
before any integration into `Thm/ThmT.agda` can typecheck at all.

No code was changed in this audit cycle. `BRA/Thm/ThmT.agda` (1.5s
cached) and `BRA/GoedelIIFull.agda` (1.3s cached) typecheck at
unchanged baseline.

## Blocker 1 — `body_mp_v` in SoundMpProto reads from `a`, not from `b`

`BRA/SoundMpProto.agda:71–95` builds `body_mp_v` using `Lift get_head`
etc., where `get_head = Comp Fst (Comp Fst Snd)`. By
`axLift : ap2 (Lift f) a b = ap1 f a` (Deriv.agda:69), this evaluates
`get_head` on the *first* argument `a`, not the second argument `b`.

But the prototype's accompanying comment says `thmT y1T = Fst (Snd b)`.
That requires accessing `b` (the IH-distributed argument carrying
`thmT(...)` images), not `a` (the syntactic encoded payload carrying
the raw `y1T`/`y2T`). With the current `Lift`-based extractors,
`outer_check` reduces to `TreeEq (Fst y1T) tagImp` — a check on the
raw proof-index Term, not on the encoded formula `thmT y1T`. That is
not the soundness check we want.

**Fix.** Mirror the *original* `body_mp` pattern (ThmT.agda:339):

```
body_mp = Post (Comp (Comp Snd (Comp Snd Fst)) (Comp Snd Snd)) Pair
```

`Post f Pair` evaluates `f` on `(ap2 Pair a b)` (axPost), so a single
`Fun1` extracts from both via `Fst`/`Snd` of the synthesized pair.
The corrected verifying body is `Post verifier_F1 Pair` where
`verifier_F1` builds the IfLf nest internally, with extractors
expressed as deeper `Comp Snd ...` chains over the synthesized
`(Pair a b)`. SoundMpProto needs to be rewritten to that shape before
its `_eval` proof is meaningful.

## Blocker 2 — Inner-check hypothesis is unlifted; consumer witnesses are lifted

The proposed `thmTDispMp_param` signature (from the previous prompt):

```
Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->     -- NEW: inner check (UNLIFTED)
```

Every consumer call site in `BRA/Th14Step3.agda` and `BRA/Th14Step5.agda`
already builds the dispatcher result *unlifted* and applies
`liftAxiom (PrAtX x)` only at the very end (Th14Step5.agda:305).
For the new third hypothesis, the candidate witnesses are:

| Outer / Inner mp call | Required `thmT y2T = pT` witness | Current form |
|--|--|--|
| Th14Step3 inner (line 577) | `thmT (D_thmT x) = codeFTeq1Hyp thmT x cG` | `step1_l x` — **lifted** under `PrAtX x` |
| Th14Step3 outer (line 625) | `thmT (D_sub_at_ii x) = codeFTeq2Hyp sub i i cG` | `step2_l x` — lifted, but its body is `liftAxiom P (thm13_F2 ...)` so an **unlifted** witness exists |
| Th14Step5 inner (line 260) | `thmT (g_part x) = (encoded_th_x_at x, encoded_sub_ii)` | `step3_l x` — **lifted** |
| Th14Step5 outer (line 297) | `thmT (K_part x) = neg_P` | `K_part_l x` — **lifted** |

The previous prompt's claim "K_part_l x is exactly the new third
hypothesis" is wrong: `K_part_l : Deriv (PrAtX x imp atomic ...)`
cannot be passed where `Deriv (atomic ...)` is expected.

The lifting is *essential* for three of the four witnesses:

* `step1_l` uses `axImpRefl P` (ImpT-trick: `P = atomic(eqn(thmT x) cG)`)
  to bridge `thmT x = thmT x` into `thmT x = cG`. Without `PrAtX`
  there is no Deriv of `thmT x = cG`.
* `step3_l` is built atop `step1_l` (so inherits the same dependency).
* `K_part_l` reduces `thmT(K_part x)` to a form involving `cG` only
  because the underlying `step4_l` uses the same `axImpRefl P` trick
  (Th14Step4.agda:192–204).

So this is not a plumbing oversight; the witnesses *cannot* be
unlifted without redoing the underlying chain.

**Two viable fixes**:

1. **Lifted dispatcher variant.** Add
   ```
   thmTDispMp_param_l :
     (P : Formula) (y1T y2T : Term) (y1' x' : Term) (pT qT : Term) ->
     Deriv (P imp atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
     Deriv (P imp atomic (eqn (ap1 thmT y1T) (Pair (reify tagImp) (Pair pT qT)))) ->
     Deriv (P imp atomic (eqn (ap1 thmT y2T) pT)) ->
     Deriv (P imp atomic (eqn (ap1 thmT (Pair tagCode_mp (Pair y1T y2T))) qT))
   ```
   built from the unlifted `thmTDispMp_param` plus the existing
   `liftAxiom`/`liftedRuleTrans`/`liftedCong*` helpers in
   `BRA/Thm/EvalHelpers.agda`. The unlifted dispatcher is still used
   for closed-Tree call sites (`Thm14SubLemma`, `Th12Z`, etc.); the
   lifted variant takes over `Th14Step3.agda` and `Th14Step5.agda`.
   Restructure `step3_l` and `step5_l` to use lifted bridges
   throughout (no `liftAxiom` at the end). Estimated ~400 LoC of new
   helpers + ~200 LoC of consumer rewrites.

2. **Push lifting into the consumers' unlifted half.** Build
   `step1_l_pre`, `step3_l_pre`, `K_part_l_pre` that are unlifted but
   whose RHS is the *pre-bridge* form (e.g.
   `step1_l_pre x : Deriv (atomic (eqn (thmT (D_thmT x)) (codeFTeq1 thmT x)))`
   — the canonical Theorem 12 output, no `cG`). Use those as the
   inner-check; bridge the dispatcher's *output* to the `cG` form
   under `PrAtX` afterward. Smaller code change but harder to make
   typecheck cleanly because the dispatcher's `qT` then carries
   intermediate (non-`cG`) shapes that must be canonicalized later.

Recommendation: option (1). It also generalizes naturally to Step 2
(soundifying the seven other premise-consuming dispatchers), since
they all face the same unlifted-vs-lifted mismatch.

## Blocker 3 — `body_mp_v_eval_pass` needs parametric `TreeEq t t = O`

The verifying body's "inner check" is `TreeEq (thmT y2T) pT`. The
`_eval_pass` proof must derive
`Deriv (atomic (eqn (ap2 TreeEq pT pT) O))` for an arbitrary `Term`
`pT` (the `thmT y2T = pT` hypothesis collapses both arguments to
`pT`).

The codebase's `treeEqRed : (a b : Tree) -> Deriv ...`
(`BRA/SubT.agda:52`) only handles `Tree`-level inputs (where `a`/`b`
are concrete inductive trees). For a free `Term` `pT`, no such helper
exists. Building one requires `ruleIndBT` (binary-tree induction at
`Deriv` level, `BRA/Deriv.agda:228`):

```
treeEqRefl_param : (t : Term) -> Deriv (atomic (eqn (ap2 TreeEq t t) O))
```

Estimated ~80–120 LoC, plus a careful `_param`-style let-binding
strategy because nested `axTreeEqNN` -> `axIfLf` reductions don't
reduce cleanly inside `ruleIndBT`'s motive without `eqSubst` shims.

This is a real piece of new infrastructure, not just a chain of
existing lemmas.

## Resulting plan

The previous prompt's "Step 1 of 2" implicitly assumed all three
blockers were trivial. They are not. A revised Step 1 should be:

1. **Step 1A** (this session, deferred to next): rewrite
   `BRA/SoundMpProto.agda`'s `body_mp_v` to use `Post _ Pair` style
   (Blocker 1). Add `treeEqRefl_param` in a small standalone file
   `BRA/TreeEqReflParam.agda` (Blocker 3). Prove
   `body_mp_v_eval_pass` in a sidecar file `BRA/SoundMpVProof.agda`
   for the closed-`Formula` case
   (`Deriv (atomic (eqn (ap2 body_mp_v ...) (reify (codeFormula Q))))`).
   No changes to `ThmT.agda` or any consumer. Per-file budget <1s
   solo. This validates the soundness combinator end-to-end.

2. **Step 1B**: extend the lifted dispatcher infrastructure
   (`thmTDispMp_param_l`, Blocker 2 fix (1)). Build it in
   `BRA/Thm/ThmT.agda` after the existing `thmTDispMp_param`, reusing
   the unlifted result and `liftAxiom`/`liftedRuleTrans`. Mirror for
   `thmTDispRuleInst_param_l` if its consumers also need lifting.

3. **Step 1C**: replace `body_mp` with `body_mp_v` in the abstract
   block (since it has the same `Fun2` type, `skipAtTag` references
   in non-mp dispatchers are unaffected). Wire the inner-check
   hypothesis through `body_mp_v_eval_pass`. Update
   `body_mp_eval`/`body_mp_eval_param`/`body_mp_eval_proj` signatures
   to take the new hypothesis. Same for
   `body_ruleInst`/`body_ruleInst_v`.

4. **Step 1D**: rewrite `Th14Step3.agda`/`Th14Step5.agda` to use
   `thmTDispMp_param_l` with `step1_l`/`step3_l`/`K_part_l` directly
   as inner-check witnesses. Remove the `liftAxiom` at the tail of
   `step5_l`/`step3_l`.

5. **Step 1E**: smoke-test `BRA/GoedelIIFull.agda`.

Total estimated effort: ~3–5 sessions, not one.

## What this session changed

Nothing under `BRA/`. Only this findings document was added.
`BRA/Thm/ThmT.agda`, `BRA/GoedelIIFull.agda`, all consumer files, and
`BRA/SoundMpProto.agda` are untouched.

## Next session — recommended starting point

Pick up Step 1A as scoped above. Concretely:

1. Read this file and `BRA/SoundMpProto.agda` for the corrected
   combinator design.
2. Read `BRA/SubT.agda:52` (`treeEqRed`) for the `Tree`-level
   recursion pattern; mirror with `ruleIndBT` for the parametric
   version.
3. Check `BRA/FromBaseAndPair.agda` for the `ruleIndBT` wrapping
   pattern; `treeEqRefl_param` follows the same template.
4. Write `BRA/TreeEqReflParam.agda` (~120 LoC) and verify <1s solo.
5. Rewrite `BRA/SoundMpProto.agda`'s `body_mp_v` to `Post _ Pair`
   style (~30 LoC change).
6. Write `BRA/SoundMpVProof.agda` containing
   `body_mp_v_eval_pass_closed` (closed-`Formula` version) using the
   new combinator + `treeEqRefl_param`. Estimate ~250 LoC, target
   <1s solo.
7. Check `time /opt/homebrew/bin/agda BRA/SoundMpVProof.agda` is
   under 1s.
8. Hand off to a follow-up session for Step 1B onward.

If any of those steps slows past 1s solo, that is the canonical
"stop and re-architect" moment per the methodology rule.
