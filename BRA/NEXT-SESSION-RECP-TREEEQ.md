# Next session: finish Theorem 12 (Rec, RecP, ruleIndBT2, TreeEq)

## Mission

Finish the remaining 3 primitive functors of Theorem 12 in BRA. After this
session: D : Fun1 → Fun1 and D2 : Fun2 → Fun2 polymorphic Theorem 12 will be
buildable for arbitrary Fun1/Fun2, which is what Theorem 14 needs to construct
D_th and D_sub for Gödel II.

## Status going in

12 of 15 primitive functors have schematic Theorem 12 (single `Deriv P` with
free vars). See `BRA/Th12{I,Z,Fst,Snd,Pair,Const,IfLf}.agda` for atomic cases
and `BRA/Th12{Comp,Comp2,Lift,Post,Fan}.agda` for structural composers (the
latter are thin wrappers over `BRA/Thm12/Parts/{Comp,Comp2,Lift,Post,Fan}.agda`'s
meta-Pi correctness lemmas).

Remaining cases:
- `Rec z s` (Fun1) — recursive on input.
- `RecP s` (Fun2) — recursive on second input.
- `TreeEq` (Fun2) — 4-way shape dispatch on both inputs.

## Plan (4 phases)

### Phase 1: Th12Rec (no new primitives)

**File**: `BRA/Th12Rec.agda` (new).

**Pattern**: similar to `BRA/Th12Fst.agda`'s schematic structure — fromBaseAndPair
on var 0, but **using ruleIndBT directly** (not fromBaseAndPair) because the
Pair-case genuinely uses the IHs at v_a, v_b.

**Substituent count**: axRecNd z s a b has 2 vars (a, b). At Pair-case
(v_a, v_b), substitute these via **sbt2** (already in `BRA/Sb2.agda`).

**Df_F1_Rec_zs construction**: an IfLf-dispatching Fun1 (like Df_F1_Fst), with
- lf-case proof code = encoded `axRecLf z s` (closed Tree).
- Pair-case proof code = combination of `axRecNd z s (var v_a) (var v_b)` +
  IHs at v_a, v_b + Theorem 12 for `s` (the step functor) — encoded via
  ruleTrans proof codes.

**Schematic statement**:
```agda
P_Th12_Rec_zs : Formula
P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 Df_F1_Rec_zs (var zero)))
                             (codeFTeq1Asym (Rec z s) (var zero)))
Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs
```

**Caveat**: the Pair-case proof needs Theorem 12 for `s` (the step functor)
as an INPUT parameter. So `Th12RecCase` is parametric over (z, s, Df_s, D_correct_s).

**Key references**:
- `BRA/Thm12/Parts/Rec.agda` and `RecV2.agda` already have partial constructions
  (`D_Rec_zs`, `D_correct_Rec_NN_pt`). Salvage what's there.
- `BRA/Th12Fst.agda` for the IfLf-dispatch + `thmTDispRuleInst2_param` pattern.
- `BRA/FromBaseAndPair.agda` is NOT what we want (it discards IHs); use
  `ruleIndBT` directly with the IH-using step.

**Estimate**: ~700 LoC. ~30 min hands-on per ~150 LoC = ~2 hours.

### Phase 2: Th12RecP (no new primitives)

**File**: `BRA/Th12RecP.agda` (new).

**The variable-naming trick (load-bearing)**: ruleIndBT inducts on var 0 only.
For RecP s at args (p, x), we want to induct on x (the tree). Convention-flip
the schematic statement to put x at var 0:

```agda
P_Th12_RecP_s : Formula
P_Th12_RecP_s = atomic (eqn (ap1 thmT (ap2 Df_F2_RecP_s (var (suc zero)) (var zero)))
                             (codeFTeq2Asym (RecP s) (var (suc zero)) (var zero)))
```

— i.e., the SECOND arg of `Df_F2_RecP_s` and `RecP s` is `var 0` (the recursion
variable for ruleIndBT), the FIRST arg is `var 1` (= p, the parameter).

**Substituent count via encoding-trick**: axRecPNd s p a b has 3 vars (p, a, b).
But:
- Encode with p at the SAME var index as the outer schematic's parameter (var 1).
- Encode a, b at fresh inner indices (var 0 of inner = var v_a of Pair-case).
- Then only a, b need substituting at the Pair-case → **sbt2 suffices**.

(This avoids needing sbt3.)

**Df_F2_RecP_s construction**: similar IfLf-dispatch on the recursion variable.
Lf-case = encoded axRecPLf. Pair-case = encoded axRecPNd + IHs + Theorem 12 for
`s`.

**Estimate**: ~700 LoC.

### Phase 3: Add ruleIndBT2 as new Deriv primitive

**File modifications**:
- `BRA/Deriv.agda`: new constructor `ruleIndBT2`. Signature:
  ```agda
  ruleIndBT2 : (P : Formula) (v1 v2 v3 v4 : Nat) ->
               -- 4 base cases:
               Deriv (substF (suc zero) O (substF zero O P)) ->                                         -- (O, O)
               Deriv ((substF (suc zero) (var v3) P) imp                                                -- (O, Pair):
                      ((substF (suc zero) (var v4) P) imp                                                --   IHs at v3, v4
                       substF (suc zero) (ap2 Pair (var v3) (var v4)) (substF zero O P))) ->
               Deriv ((substF zero (var v1) P) imp                                                      -- (Pair, O):
                      ((substF zero (var v2) P) imp                                                      --   IHs at v1, v2
                       substF (suc zero) O (substF zero (ap2 Pair (var v1) (var v2)) P))) ->
               -- 4-way step (genuinely 2D):
               Deriv (full 4-IH-implications for (Pair, Pair) case) ->
               Deriv P
  ```
  Get the exact signature from re-deriving the 2D induction principle. (~50 LoC.)

- `BRA/Thm/Tag.agda`: `tagRuleIndBT2 = suc tagRuleInst2`.
- `BRA/Thm/Parts/RuleIndBT2.agda` (new): `encRuleIndBT2`, `outRuleIndBT2`. (~70 LoC.)
- `BRA/Thm/ThmT.agda`: extend the abstract block with body_ruleIndBT2,
  checkTag_ruleIndBT2, branch_ruleIndBT2, next_axIfLfNL chain extension (or
  keep ruleIndBT2 at the END after ruleInst2 — the existing chain already has
  branch_ruleInst2 fall through to fbBody, change to next_ruleInst2).
- Also: thmTDispRuleIndBT2 (~150-300 LoC for the dispatch chain).

**Estimate**: ~430 LoC.

**Note**: ruleIndBT2 is a logical extension (it's a derived rule in classical
metatheory but BRA has no first-order quantifiers so we can't derive it
internally). Adding as primitive is the clean path.

### Phase 4: Th12TreeEq (uses ruleIndBT2 + sbt2-twice)

**File**: `BRA/Th12TreeEq.agda` (new).

**Df_F2_TreeEq construction**: 4-way IfLf dispatch on the shapes of var 0 (= x)
and var 1 (= v):
- (O, O): proof code for axTreeEqLL.
- (O, Pair w_c w_d): proof code for axTreeEqLN (needs sbt2 substitution at w_c, w_d).
- (Pair w_a w_b, O): proof code for axTreeEqNL (needs sbt2 at w_a, w_b).
- (Pair w_a w_b, Pair w_c w_d): proof code for axTreeEqNN, which has 4 vars
  a1, a2, b1, b2.
  - **Sequential sbt2 trick**: encode axTreeEqNN with 4 inner vars. First sbt2
    substitutes (a1, a2) := (var w_a, var w_b). Second sbt2 substitutes (b1, b2)
    := (var w_c, var w_d). The two sbt2's are nested, with the inner one
    producing a runtime proof code that the outer one operates on.
  - This avoids needing sbt4.

**Schematic statement**:
```agda
P_Th12_TreeEq : Formula
P_Th12_TreeEq = atomic (eqn (ap1 thmT (ap2 Df_F2_TreeEq (var zero) (var (suc zero))))
                             (codeFTeq2Asym TreeEq (var zero) (var (suc zero))))
Th12_F2_TreeEq : Deriv P_Th12_TreeEq
```

The proof uses ruleIndBT2 with the 4 cases.

**Estimate**: ~1000-1200 LoC.

## Backup: if sequential sbt2 hits problems

If at Phase 2 (RecP) or Phase 4 (TreeEq) the sequential / encoding-trick
sbt2 approach hits definitional reduction issues OR proof obligations that
sbt2 alone can't discharge cleanly, the backup is:

### Sbt3 / Sbt4 infrastructure

- **sbt3** (3-way simultaneous substitution):
  - `BRA/Sb3.agda` (~900 LoC): subT3 = RecP stepSubT3 (3-way IfLf dispatch),
    codedSubst3 (Tree-valued), codedSubstT3 (Term-valued), reify lemma,
    subTDef3, subTDef_term3.
  - `BRA/Thm/Parts/RuleInst3.agda` (~50 LoC): encRuleInst3 + outRuleInst3.
  - `BRA/Thm/Tag.agda`: tagRuleInst3 = suc tagRuleIndBT2 (after Phase 3).
  - `BRA/Thm/ThmT.agda` extension (~700 LoC): body_ruleInst3, dispatch chain
    extension, body_ruleInst3_eval, thmTDispRuleInst3 (44+ skip cascade),
    body_ruleInst3_eval_param, thmTDispRuleInst3_param.

- **sbt4** (4-way): analogous, ~750 LoC.

Total backup cost: ~2400 LoC if BOTH are needed. Still manageable but
substantial — only invoke if blocked.

## Conventions

- Module names: `BRA.Th12X` for the schematic Theorem 12 wrapper for X.
- Outputs: `Df_F1_X` / `Df_F2_X`, `Th12_F1_X` / `Th12_F2_X`, `P_Th12_X`.
- For composers parametric on prior Theorem 12, use a parametric module
  pattern (see `BRA/Th12Lift.agda`, `Th12Comp.agda` etc.).
- Typecheck after each phase. Each piece should typecheck within seconds.
- ThmT.agda should still typecheck within ~10s after extensions; if it
  blows up, investigate before adding more.
- No postulates, no holes, --safe --without-K --exact-split.

## Files to consult before starting

- `BRA/Th12Fst.agda`, `BRA/Th12Snd.agda` — pattern for IfLf-dispatch + sbt2.
- `BRA/Th12Pair.agda`, `BRA/Th12Const.agda` — pattern for Fun2 with no shape dispatch.
- `BRA/Th12IfLf.agda`, `BRA/Th12Lift.agda` — wrapper patterns.
- `BRA/Sb2.agda` — sbt2 infrastructure (study before doing sbt3 backup).
- `BRA/Thm/ThmT.agda` lines ~12550-12700 (thmTDispRuleInst2) and
  ~12500-12700 (body_ruleInst2_eval, body_ruleInst2_eval_param,
  thmTDispRuleInst2_param) — pattern for adding new dispatch lemmas.
- `BRA/Thm12/Parts/Rec.agda`, `RecV2.agda`, `RecP.agda` — partial existing
  constructions to salvage / mirror.
- `BRA/Thm12/Parts/IfLf.agda` — has the 2D ruleIndBT (via nested ruleIndBT
  hacks) at lines 800-960; study to understand whether ruleIndBT2 might
  actually be derivable (memo claims not).
- `guard15.pdf` pages 12-17 — the original Theorem 12 / 14 statements.

## Memory records to read

- `project_th12_fst_done.md` — pattern for atomic Pair-case proofs.
- `project_th12_snd_done.md` — Snd mirror.
- `project_thmt_ruleinst2_stages_1_4.md` — sbt2 / thmTDispRuleInst2 design.
- `feedback_treeeq_needs_indBT2.md` — the prior conclusion that ruleIndBT2 is
  needed (note: that memo claimed "likely derivable" but the analysis we did
  this session concluded otherwise — see this file).
- `feedback_thm12_must_be_schematic.md` — schematic = single Deriv P, not
  meta-Pi.
- `feedback_thm12_sb_is_enough.md` — context on substitution machinery.

## Specifically AVOID

- **Don't try to derive ruleIndBT2 from ruleIndBT** without quantifiers / variable
  swap — the analysis showed it's not derivable in BRA's current substitution
  language. Time-box any attempt to ~30 min, then add as primitive.
- **Don't add sbt3 / sbt4 prematurely.** First try the encoding-trick (RecP)
  and sequential-sbt2 (TreeEq) approaches. Only fall back to sbt3/4 if
  blocked.
- **Don't forget thClosed bridges.** Whenever using `substF zero t (...thmT...)`
  in formula contexts, you'll likely need eqSubst with thClosed.

## Commit cadence

- After each phase: typecheck + commit. Standalone commits per phase.
- Commit messages: descriptive, mention LoC totals + typecheck times.
- Update memory file `project_th12_status.md` after final phase.

## Definition of done

After this session:
- All 15 primitive functors have `Th12_F1_X` or `Th12_F2_X` schematic Theorem 12
  in some form (concrete or parametric module).
- The polymorphic D : Fun1 → Fun1 and D2 : Fun2 → Fun2 of `BRA/Thm12.agda`
  can be instantiated to produce schematic Theorem 12 for ANY Fun1/Fun2.
- BRA/Th12.agda's `FromBridges` module's bridges are dischargeable from the
  per-case Th12X.agda files.
- Theorem 14's needs for D_th and D_sub are unblocked.

If any phase falls short, document precisely what's missing in a follow-up
NEXT-SESSION doc and commit progress.
