# Next session — Theorem 14 Phase C (`step3_l..step5_l` chain)

## Read first

Three documents, in order:

1. **`BRA/NEXT-SESSION-THMT-PARAMETRIC-DONE.md`** — what just landed
   (the structural fix that unblocks this session's work).
2. **`BRA/NEXT-SESSION-THM14-PHASE-C.md`** — the original Phase C plan.
   **Outdated in one place**: any mention of `thmTSubLemma` requiring
   an `xShape` precondition is wrong now.  `thmTSubLemma` in
   `BRA/Thm14SubLemma.agda` is **shape-free** — it takes only
   `Deriv (atomic (eqn (ap1 thmT y) codeP))` and produces the encoded
   sb-equation without any obligation on `y`.
3. **`BRA/COR-AT-SB-LOAD-BEARING.md`** — `cor`'s defining equations
   are used 4× in this chain (at sb-substitution sites).  Keep this
   file open.

## Goal

Deliver `step5_l : (x : Term) -> Deriv (PrAtX x imp ...)`, the single
contract that `BRA.GoedelII.Compose` consumes.  After this lands,
`godelII : Deriv Con -> Deriv bot` is unconditional.

`PrAtX x = atomic (eqn (ap1 thmT x) cG)` (from `BRA.Thm14Abstract`).
`step5_l x` should produce a `Deriv` of the internal implication
`PrAtX x ⊃ atomic (eqn (ap1 thmT (ap1 constr5 x)) (reify (codeFormula bot)))`.

The `constr5 : Fun1`, `f_part`, `g_part`, `K_part`, `h_part` are already
defined in `BRA/Thm14Constr5Final.agda` (parametric over
`r12_th : Thm12_F1_Result thmT` and `r12_sub : Thm12_F2_Result sub`).
The numerals `t_term`, `t'_term` and their witnesses are in
`BRA/Thm14Numerals.agda`.

## Strategy (mechanical now)

Build, in order, in a new file `BRA/Th14Phase C.agda` (or split across
`BRA/Th14Step3.agda`, `BRA/Th14Step4.agda`, `BRA/Th14Step5.agda` if
the file gets large):

  * **`step3_l x`** — encoded `th(cor x) = sub(i,i)` under hypothesis
    `th(x) = j`.  Three sb-applications of the transitivity numeral
    `t_term`, threaded with `r12_th(x)` and `r12_sub(i,i)`.  Each
    sb-step uses `thmTSubLemma` (shape-free) with the proof-index
    being whatever proof-tree was just produced; substituents are
    `cor x`, `sub_ii_subst`, `i` in turn.

  * **`step4_l x`** — applies `K_part(x)`'s sb-step at the diagonal
    numeral `i` (= code G), under hypothesis `th(x) = j`.  Single
    sb-step (`thmTSubLemma` at proof-index `x`), substituent `cor x`,
    var index 1.

  * **`step5_l x`** — combines `step3_l(x)` + `step4_l(x)` + `h_part(x)`
    via two outer mp-steps to derive
    `th(constr5(x)) = code(bot)`.  Encode the meta-implication via
    `axK`/`axS` to package the result as the required internal
    implication `PrAtX x ⊃ ...`.

  * **`step5 : (x : Term) -> Deriv (...)`** — the final contract.
    Wraps `step5_l` to match `BRA.GoedelII.Compose`'s expected type.

Then plug `(constr5, step5)` into `BRA.GoedelII.Compose` to obtain
unconditional `godelII`.

## Likely-needed lemmas (already in the codebase)

  * `BRA.Thm14SubLemma.thmTSubLemma`        — sb-step at proof-index y
  * `BRA.Thm.ThmT.thmTDispMp_param`          — mp-step
  * `BRA.Thm.ThmT.thmTDistrib_param`         — Pair distribution (closed Fst)
  * `BRA.Cor.cor` + its defining equations   — see COR-AT-SB-LOAD-BEARING.md
  * `BRA.Thm14Numerals.{t_term, t'_term, t_witness, t'_witness}`
  * `axK`, `axS`, `axContrapos`, `mp`, `ruleTrans` from `BRA.Deriv`

## Constraints

  * ASCII only, `{-# OPTIONS --safe --without-K --exact-split #-}`.
  * No postulates, no holes, no with-abstraction, no dot patterns.
  * Each paper step = one named Agda lemma with abstract signature
    (cf. `feedback_one_lemma_per_paper_step`).  Don't write 200-line
    let-bodies.
  * Type-check incrementally (each step in its own file or its own
    top-level definition); the cache is your friend.

## How to start

1. Open `BRA/Thm14Constr5Final.agda` and re-read the comments on
   `f_part`, `g_part`, `K_part`, `h_part`.  These give the exact
   encoded structure each chain step has to land at.
2. Sketch `step3_l`'s body on paper: three sb-steps + two mp's.
3. Open `BRA/SbRuntime.agda` for a worked example of an sb-step in
   the new layout.  `Df_F1_I_runtime` is the template.
4. Start writing `step3_l` as a new top-level lemma.  Get it
   typechecking before moving to step4_l.

## Done when

`BRA/GoedelII.agda` exports a top-level `godelII : Deriv Con -> Deriv bot`
that does **not** take any further parameters — the `Compose` module
is fully instantiated.  Run `agda BRA/GoedelII.agda` and it succeeds.
