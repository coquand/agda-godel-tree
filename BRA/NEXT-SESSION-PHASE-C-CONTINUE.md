# Next session — Theorem 14 Phase C continuation

## Read first (in order)

  1. **This file** (you're reading it) — current state + work plan.
  2. `BRA/NEXT-SESSION-PHASE-C.md` — the original Phase C plan.  Items
     marked "DEFERRED" or "still needs..." in the doc below are the
     ones to tackle.
  3. `BRA/COR-AT-SB-LOAD-BEARING.md` — cor's role at sb-substitution
     sites.  Open this when you reach step (B).
  4. `CLAUDE.md` (project root) — ASCII-only / explicit-arg conventions.

Optional context (only if needed):
  * `BRA/NEXT-SESSION-THMT-PARAMETRIC-DONE.md` — structural fix that
    made `thmTSubLemma` shape-free.

## Status (2026-05-02 session — Opus 4.7 1M)

Phase C of `BRA/NEXT-SESSION-PHASE-C.md` is **partially landed**.  The
reusable infrastructure is in; the canonicalization for codeFormula's
imp case is in; the canonicalization for atomic / not + the chain
assembly remain.

**Strict invariant:** `BRA/GoedelII.agda` and the 4 new files below
**all typecheck in under 1 second solo** (with cache).  Any new file
should hit the same bar; if it goes over, something is wrong (typically
a non-canonical KT or a bad subT-target shape — see Pitfall 1).

## Delivered this session

  1. **`BRA/Thm/ThmT.agda` (~+150 LoC, inside abstract block)** —
     parametric mp dispatch:
       * `body_mp_eval_param` (parametric in y1T, y2T, pT, qT — Term-valued).
       * `thmTDispMp_param`   (full parametric mp dispatch, mirrors
         `thmTDispRuleInst_param`'s pattern but for the mp tag chain).
     Located right after the closed-form `thmTDispMp` (around line 5685).
     `BRA/GoedelII.agda` and all existing files still typecheck.

  2. **`BRA/Thm14Constr5Final.agda`** — `sub_ii_subst` redefinition.
     Was: `sub_ii_subst = ap1 cor (ap2 sub i i)` (non-canonical: KT
     reduces to Z under the `KT (ap1 f t) = Z` clause, breaking
     `constTermF1 sub_ii_subst`).
     Now: `sub_ii_subst = reify (code (reify (codeFormula G)))`
     (canonical reify-of-Tree; KT works via the reify-of-nd clause).
     Added `G` to the GoedelII import.

  3. **`BRA/Th14Step4.agda` (~200 LoC, 0.6s solo)** — Phase C step 4
     done unconditionally:
     ```
     step4_l : (x : Term) ->
       Deriv (PrAtX x imp
               atomic (eqn (ap1 thmT (ap1 K_part x))
                           (ap2 subT (ap2 Pair varCode1T (ap1 cor x)) cG)))
     ```
     Built via `K_part_unfold` (Comp2 Pair tower → Pair-tag-payload form)
     + `thmTSubLemma` at proof-index x + lifted-congR for the hypothesis-
     substitution.

  4. **`BRA/Th14Step3.agda` (~370 LoC, 0.6s solo)** — Phase C step 3's
     3-sb-step prefix done (closed; no hypothesis required):
     ```
     step3_pre : (x : Term) ->
       Deriv (atomic (eqn
         (ap1 thmT (ap1 f_part x))
         (ap2 subT (ap2 Pair varCode2T i)
               (ap2 subT (ap2 Pair varCode1T sub_ii_subst)
                     (ap2 subT (ap2 Pair varCode0T (ap1 cor x))
                                (reify (codeFormula t_formula)))))))
     ```
     Built via `f_part_inner2_unfold`, `f_part_inner1_unfold`,
     `f_part_unfold` (Comp2 Pair towers) + three `thmTSubLemma`
     applications threaded through cong1 thmT bridges.  Uses
     `t_witness` (closed, from `Thm14Numerals.agda`) at the base.

  5. **`BRA/Th14SubTPushthrough.agda` (~400 LoC, 0.1s solo)** — the
     subT-canonicalization core lemmas:
       * `subT_leaf` — `subT(p, reify lf) = reify lf` via `axRecPLf`.
       * `subT_node_unfold` — structural unfold of `subT(p, reify (nd a
         b))` to the IfLf-Pair form (parametric in `p`).
       * `subT_node_match` — `subT(Pair varCodeT tT) (reify (code (var
         n))) = tT` via match dispatch.
       * `subT_node_no_match` — at non-matching `nd a b`, distributes
         recursively to `Pair (subT(p)(reify a)) (subT(p)(reify b))`.
       * `treeEq_codeVar_tagImpHead/tagNegHead/tagAp1Head/tagAp2Head`
         (refl helpers) — establishing treeEq mismatch with tagged
         formula heads.
       * `subT_preserves_tagImp` — `subT(p)(reify tagImp) = reify tagImp`
         (passthrough for closed tag-trees containing no var-n subtree).
       * **`subT_codeFormula_imp`** (the canonicalization headline):
         ```
         subT (Pair (reify (code (var n))) tT)
              (reify (codeFormula (P imp Q)))
           = Pair (reify tagImp)
                  (Pair (subT (...) (reify (codeFormula P)))
                        (subT (...) (reify (codeFormula Q))))
         ```
         This is the EXACT form `thmTDispMp_param` needs — its hypothesis
         `thmT(y1T) = Pair (reify tagImp) (Pair pT qT)` lands here
         directly, with `pT, qT` being recursive `subT(...)` calls.
       * **`subT_dist_Pair_tagImp`** (nested-subT distribution):
         ```
         subT (Pair (reify (code (var n))) tT)
              (Pair (reify tagImp) (Pair X Y))
           = Pair (reify tagImp) (subT (...) (Pair X Y))
         ```
         Distributes through a Pair-tagImp shape (not necessarily
         reify-of-tree).  Uses `axTreeEqNN` + `treeEqRed` + `axIfLfN`
         to verify the TreeEq mismatch parametrically in X, Y.
       * **`subT_dist_Pair_inner_via_TreeEq`** (caller-supplied TreeEq
         witness): given a Deriv that `TreeEq varCodeT (Pair X Y)`
         evaluates to falseT, distributes subT through (Pair X Y) to
         (Pair (subT X) (subT Y)).
       Together these handle the nested-subT case that step5_l needs
       when the canonicalization chain exposes Pair-tagImp shapes
       between subT layers.

## What is left for `step5 : Deriv Con -> Deriv bot` to compose

### Concrete target RHS shapes (the goal posts)

Let `P := ap2 Pair (ap1 cor x) sub_ii_subst` (the encoded "cor x =
sub_ii_subst" — a Pair-shape Term, NOT reify-of-codeFormula).

After full canonicalization, the chain should land at these literal
Term-level RHSs:

  * **`step3_l x`** RHS: `P`  (= `Pair (cor x) sub_ii_subst`).
    Derivation: `thmT(g_part x) = P` under hypothesis `PrAtX x`.
    The "encoded 'th(cor x) = sub(i,i)'" is precisely this Pair-shape;
    semantically Guard's "th(cor x) = sub(i,i)" but at our Term level
    `sub_ii_subst = reify (code cG)`, so `P` IS the Tree-level encoding
    of the equation "(cor x) = sub_ii_subst" (the substituted t-formula
    third atomic).

  * **`step4_l_canonical x`** RHS: `ap2 Pair (reify tagNeg) P`
    (= encoded "not (cor x = sub_ii_subst)").  Derivation:
    `thmT(K_part x) = Pair (reify tagNeg) P` under `PrAtX x`.
    Bridging step4_l's existing `subT (Pair varCode1T (cor x)) cG`
    via `subT_codeFormula_neg` + `subT_codeFormula_atomic`.

  * **`h_part_l x`** RHS: `ap2 Pair (reify tagImp) (ap2 Pair P
    (ap2 Pair (reify tagImp) (ap2 Pair (ap2 Pair (reify tagNeg) P)
    (reify (codeFormula bot)))))`.  This is encoded
    "P imp ((not P) imp bot)" with the substituted P.  No hypothesis
    needed (h_part's chain is closed under the substitutions; no var
    involvement after the 2 subT layers).  But for uniformity, deliver
    as `PrAtX x imp ...`.

  * **`step5_l x`** RHS: `reify (codeFormula bot)`.  Two outer
    `thmTDispMp_param` dispatches collapse h_part_l + step3_l +
    step4_l_canonical to bot's code.

### Big-picture chain (existing pieces)

  * `step3_pre x` (done) gives  `thmT (f_part x) = subT^3 (reify (codeFormula t_formula))`.
  * `step4_l x` (done) gives  `thmT (K_part x) = subT (Pair varCode1T (cor x)) cG`.
  * `h_part_pre x` (TODO — mirror of step3_pre) will give
    `thmT (h_part x) = subT^2 (reify (codeFormula t'_formula))`.
  * `step5_l x` combines all via two `thmTDispMp_param` dispatches +
    canonicalization bridges.

### Substantive missing infrastructure

The CORE subT-canonicalization is now done (item 5 above).  What
remains is its application to specific shapes: distribution through
`reify (codeFormula (atomic (eqn a b)))` and a few cor-bridge details.

#### (A) `subT_codeFormula_atomic` + `subT_codeFormula_neg`  [~150 LoC]

Mirror of `subT_codeFormula_imp` (in `BRA/Th14SubTPushthrough.agda`)
for atomic equations and negations.

For `atomic (eqn a b)` with a, b : Term, `codeFormula (atomic (eqn a
b)) = nd (code a) (code b)`.  So `reify (codeFormula (atomic (eqn a
b))) = ap2 Pair (reify (code a)) (reify (code b))`.  subT distributes:
```
subT_codeFormula_atomic : (n : Nat) (tT : Term) (a b : Term) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT)
              (reify (codeFormula (atomic (eqn a b)))))
    (ap2 Pair (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify (code a)))
              (ap2 subT (ap2 Pair (reify (code (var n))) tT) (reify (code b))))))
```

Proof: one `subT_node_no_match` application with the TreeEq-mismatch
witness derived by case-splitting on `a`'s outer constructor (the
helper `codeFormula_pair_no_var` in the existing file — make a similar
`code_a_pair_no_var` for the eqn case, four refl clauses).

For `not P`: codeFormula (not P) = nd tagNeg (codeFormula P).
```
subT_codeFormula_neg : (n : Nat) (tT : Term) (P : Formula) ->
  Deriv (atomic (eqn
    (ap2 subT (ap2 Pair (reify (code (var n))) tT)
              (reify (codeFormula (not P))))
    (ap2 Pair (reify tagNeg)
              (ap2 subT (ap2 Pair (reify (code (var n))) tT)
                         (reify (codeFormula P))))))
```

Proof: `subT_node_no_match` with `treeEq_codeVar_tagNegHead` + a
`subT_preserves_tagNeg` analog of `subT_preserves_tagImp` (literally
copy the body with tagImp -> tagNeg; only ~20 LoC).

#### (B) `cor`-bridge at the parametric substituent slots  [~50 LoC]

When (A)'s output has `subT(...) (reify (code a))` for `a = ap1 cor
x` or similar, we need to evaluate further.  The cor-bridge says
(per `BRA/COR-AT-SB-LOAD-BEARING.md`):

  * Under hypothesis `Deriv (atomic (eqn x (reify v)))` for some Tree
    v, `Deriv (atomic (eqn (ap1 cor x) (reify (code (reify v)))))`.
  * This is `cong1 cor` of the hypothesis composed with `corOfReify v`
    (in `BRA/Cor.agda`).

In the closure (`BRA.Thm14Abstract.GodelII.closureToG`), `step5_l` is
applied at `x := var (suc zero)` — but at THAT point we're in the
internal-implication chain, not in a meta-hypothesis context.  So the
cor-bridge in our setting is purely the inner `corOfReify` step
applied at constant arguments where applicable.  In step3_l / step4_l
the substituent at var 0 is `cor x` (open); the cor-bridge does NOT
reduce it under x parametric; rather we leave `cor x` as-is in the
final RHS form.  Practically: the "cor-bridge" need is minimal — only
needed when we CAN reduce, and we mostly cannot for var-parametric x.

If you find you need cor-bridge work, look at `BRA/Cor.agda:125`
(`corOfReify`) and `BRA/CorOfPair.agda` for the closed-tree analog.

#### (C) Chain assembly — DETAILED ORDER

Once (A) and (B) are in place, work through these in order.  Each step
should land in a separate file (`BRA/Th14Step{3,5}.agda` etc.) and
typecheck solo in <1s.

##### (C1) `step3_l` — file `BRA/Th14Step3.agda` (extend existing)

The existing file has `step3_pre x` (closed, gives the 3-deep subT
chain).  Add a lifted version:

```
step3_l : (x : Term) ->
  Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 g_part x)) <RHS>))
```

where `<RHS>` is the canonicalized encoded "th(cor x) = sub(i,i)" form.
By tracing the chain:

  1. Lift `step3_pre x` under `PrAtX x` via `liftAxiom`.
  2. Apply `subT_codeFormula_imp` and `subT_dist_Pair_tagImp` 3 times
     (innermost first) to expose t_formula's outer imp structure as
     `Pair (reify tagImp) (Pair pT1 qT1)` where pT1, qT1 are nested
     subT applications.
  3. The "`g_part_inner` mp": apply `thmTDispMp_param` at y1T = f_part(x),
     y2T = D_thmT(x).  `d1` is the canonicalized form from step 2 (= Pair
     tagImp shape).  Output: `thmT(g_part_inner x) = qT1`.
  4. Bridge `thmT(g_part_inner x)` to `thmT(g_part_inner x)` via
     `cong1 thmT (g_part_inner_unfold x)` (write the `_unfold` lemma
     analogous to `f_part_unfold` already in Th14Step3.agda).
  5. The "`g_part` mp": apply `thmTDispMp_param` at y1T = g_part_inner(x),
     y2T = D_sub_at_ii(x).  Need `thmT(g_part_inner x) = Pair tagImp
     (Pair pT2 qT2)`.  By step 3's output, qT1 = subT^3 applied to
     (codeFormula ((x_1 = x_2) imp (x_0 = x_1))).  Apply `subT_codeFormula_imp`
     + `subT_dist_Pair_tagImp` again — this exposes the inner imp.
  6. Output: `thmT(g_part x) = qT2 = subT^3 (codeFormula (x_0 = x_1))`.
     This is the encoded "th(cor x) = sub(i,i)" — apply
     `subT_codeFormula_atomic` to expose the eqn-Pair form.

Note: the parametric mp dispatch `thmTDispMp_param` does not USE the
y2T's thmT-image (drops it).  But for the LIFTED form, you'll need
step1_l's / step2_l's output threaded as a side condition for the mp
to be VALID at the proof level.  In practice the dispatch fires
unconditionally on the proof code; the validity is implicit.

Use `liftAxiom` to lift each closed step under `PrAtX x`, then
`liftedRuleTrans` to chain.

##### (C2) `step4_l_canonical` — file `BRA/Th14Step4.agda` (extend existing)

Existing `step4_l` gives RHS `subT (Pair varCode1T (cor x)) cG`.  Need
to bridge to encoded "th(cor x) != sub(i,i)".

  1. Recall `cG = reify (codeFormula G)` where G = `not (atomic (eqn
     (ap1 thmT (var 1)) (ap2 sub i i)))` (after diagonal substitution).
  2. Apply `subT_codeFormula_neg` to expose `Pair (reify tagNeg) (subT
     ... (reify (codeFormula <inner atomic>)))`.
  3. Apply `subT_codeFormula_atomic` on the inner atomic.
  4. Resolve subT on `code (ap1 thmT (var 1))` and on `code (ap2 sub i
     i)` via a few `subT_node_no_match` steps (the codeF1 / codeF2 +
     code-of-Term head shapes mismatch tagVar uniformly).

##### (C3) `h_part_pre` + `h_part_l` — file `BRA/Th14StepH.agda` (new)

Mirror `BRA/Th14Step3.agda`'s `step3_pre` for h_part on t'_term:
  * `h_part_inner1_unfold`, `h_part_skel_unfold`, `h_part_thxLayer_unfold`,
    `h_part_unfold` (Comp2 Pair tower unfold lemmas).
  * `h_part_pre x` — 2-sb-step closed prefix (vs step3_pre's 3-sb).
  * `h_part_l x` — lifted version with mp dispatches threading
    `step1_l` and `step2_l`, similar to step3_l.

##### (C4) `step5_l` — file `BRA/Th14Step5.agda` (new)

Combine `step3_l + step4_l_canonical + h_part_l` via two outer
`thmTDispMp_param` dispatches.  The outer mp's at constr5 are:

  * Inner: y1T = h_part(x), y2T = g_part(x).  Need
    `thmT(h_part x) = Pair tagImp (Pair P (Pair tagImp (Pair (Pair
    tagNeg P) (reify (codeFormula bot)))))` (= encoded "(P) imp ((not
    P) imp bot)" with P = "th(cor x) = sub(i,i)").  Output: `thmT(...)
    = Pair tagImp (Pair (Pair tagNeg P) (reify (codeFormula bot)))`.
  * Outer: y1T = constr5_inner(x), y2T = K_part(x).  Need
    `thmT(constr5_inner x) = Pair tagImp (Pair (Pair tagNeg P) (reify
    (codeFormula bot)))`.  Output: `thmT(constr5 x) = reify (codeFormula
    bot)`.

##### (C5) Plug-in — extend `BRA/GoedelII.agda`

```agda
module Final =
  BRA.GoedelII.Compose
    (Th14Constr5Final.constr5 r12_th r12_sub)   -- existing
    (Th14Step5.Th14Step5.step5_l r12_th r12_sub) -- new

godelIIUnconditional :
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub) ->
  Deriv Con -> Deriv bot
godelIIUnconditional r12_th r12_sub = Final.godelII
```

Note: this is parametric over `r12_th` and `r12_sub` (the Thm 12
results) — those are independently witnessed in `BRA/Thm12.agda`'s
`FromBridges` module if/when their inputs are supplied.

## Pitfalls (LEARNED THIS SESSION — read before coding)

  1. **`KT` only reduces on `reify <closed-tree>`.**  `KT (ap1 f t)`,
     `KT (ap2 g a b)`, `KT (var n)` all collapse silently to `Z`.
     `constTermF1 c = KT c` requires `c` to be `reify (codeT)` for
     some Tree `codeT` — see `feedback_kt_canonical_only` (memory).
     If you introduce new constants and `KT` of them silently fails,
     this is why.

  2. **Don't change the abstract block in `BRA/Thm/ThmT.agda` unless
     necessary.**  All `body_*` and `thmT*Disp*` definitions need to
     live inside the abstract block (around lines 121-10880).  Adding
     a new dispatch lemma: insert near similar lemmas (e.g., near
     `thmTDispMp` at ~line 5685 or `thmTDispRuleInst_param` at ~8830).

  3. **When `subT` doesn't reduce, check the second-arg shape.**
     `subT` requires its second arg to be `O` or `ap2 Pair X Y` for
     `axRecPLf`/`axRecPNd` to fire.  If you have a generic Term as
     second arg, the recursion is stuck.

  4. **The internal-implication form needs `axImpRefl` for self-
     hypotheses.**  When `step4_l` derives a sub-step that uses
     `PrAtX x` directly as a hypothesis, encode it as
     `axImpRefl (PrAtX x) : Deriv (P imp P)` — see existing `step4_l`
     body for the pattern.

  5. **Check files solo with `agda --safe BRA/<file>.agda`.**  Solo
     timing for the new files: < 1s.  If a file takes 5s+, the type
     is asking Agda to evaluate too much — restructure with helper
     lemmas or `let`-bound subterms.

## Estimated effort (revised after this session)

  * (A) `subT_codeFormula_atomic` + `subT_codeFormula_neg` analogs:
    ~150 LoC, structurally identical to `subT_codeFormula_imp` but for
    `atomic (eqn a b)` and `not P` codeFormulas.
  * (B) `cor`-bridge derivation (corOfReify under hypothesis): ~50 LoC.
  * (C) chain assembly:
      - h_part_pre (analog of step3_pre on t'_term): ~300 LoC.
      - step3_l (lifted, 2 thmTDispMp_param dispatches): ~250 LoC.
      - step4_l_canonical (bridging step4_l's RHS to encoded form): ~100 LoC.
      - step5_l (combining via 2 outer mp dispatches): ~250 LoC.
      - Plug into BRA.GoedelII.Compose: ~10 LoC.

Total: ~1100 LoC remaining; 2 focused sessions.

**The canonicalization tools now in place** (`subT_codeFormula_imp`,
`subT_dist_Pair_tagImp`, `subT_dist_Pair_inner_via_TreeEq`,
`subT_node_match`, `subT_preserves_tagImp`) are the substantive
infrastructure.  The remaining work is mechanical chain assembly +
two more codeFormula cases; it does NOT involve novel mathematical
content.

## Files NOT touched (pre-existing breakage; unrelated)

The files listed in `BRA/NEXT-SESSION-THMT-PARAMETRIC-DONE.md` 'Files
NOT touched' section remain in their pre-session state.

## Constraints honoured

  * ASCII only.
  * `{-# OPTIONS --safe --without-K --exact-split #-}` everywhere.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * No new Deriv constructors.
  * Per-file solo typecheck under 1s with cache.

## Done when

`BRA/GoedelII.agda` exports a top-level
```
godelIIUnconditional :
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub) ->
  Deriv Con -> Deriv bot
```
that does not take any Thm 14 contracts.  Run
`agda --safe BRA/GoedelII.agda` and it succeeds.

(`r12_th` / `r12_sub` are independently witnessed by
`BRA.Thm12.FromBridges.thm12_F1 thmT` and similar — their gathering
is a separate Phase D concern, not part of Phase C.)

## See also

  * `BRA/COR-AT-SB-LOAD-BEARING.md` — analysis of cor's specification
    use sites in Theorem 14.
  * `BRA/NEXT-SESSION-PHASE-C.md` — original Phase C plan (consumed).
  * `BRA/NEXT-SESSION-THMT-PARAMETRIC-DONE.md` — structural fix that
    enabled `thmTSubLemma` to be shape-free, which Phase C uses.
  * `BRA/Thm/ThmT.agda:5685` — `body_mp_eval_param` /
    `thmTDispMp_param` (the new infrastructure).
  * `BRA/Th14Step3.agda` / `BRA/Th14Step4.agda` /
    `BRA/Th14SubTPushthrough.agda` — partial Phase C deliverables.
  * `BRA/Th14Constr5Final.agda` — `f_part`, `g_part`, `K_part`,
    `h_part`, `constr5` definitions.
  * `BRA/Thm14Numerals.agda` — `t_term`, `t_witness`, `t'_term`,
    `t'_witness`.
  * `BRA/Th14Constr5.agda` — `step1_l`, `step2_l` (already lifted
    Theorem 13 instances threaded through PrAtX x).
