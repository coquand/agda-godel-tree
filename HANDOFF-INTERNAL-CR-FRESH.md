# HANDOFF — internal Church-Rosser for the FULL closed-term p.r. calculus

## Goal (this session)

Finish **internal CR** (BRA-internal Church-Rosser) for the full closed-term
primitive-recursive calculus, with NO `E(f)` formulae in the CR proof itself
(functional / free-variable-schema only; `E` is reserved for the final
`Con(Eq)` / `Con(T0)` interpretation layer, per Thierry).

The single substantive remaining theorem is the **opaque triangle**

```
triPresObjOpaque (p : Term) :
  Deriv (imp (validity p = O)
             (conj3 p = O))
  where conj3 p bundles:
    (V) wfRed (triF p) = O                         -- validity preserved
    (S) srcF (triF p)  = tgtF p                    -- src endpoint
    (T) tgtF (triF p)  = devF (srcF p)             -- tgt endpoint
```

universal in the (opaque) step code `p`, by COURSE-OF-VALUES induction on `p`
(`bigC` / `ruleIndNat`-on-K). Then strip/confluence over coded reduction chains
(free-var schema) gives internal CR.

**There is NO remaining math wall.** The one genuine obstacle (surjective
pairing for compound carried funs) was found and RESOLVED this session by
`T4.PrFunValid` (decidable funcode validation). What remains is mechanical
assembly at the scale of the toy's `TriPresDispatch` stack, plus a few opaque
eqs and their imp-form lifts.

## Build / discipline

- Compiler: `~/.cabal/bin/agda-2.9.0 --safe T4/X.agda` (pipe through `grep`;
  never `cd …>file` or `$()`/`${}` in Bash).
- Header on every file: `{-# OPTIONS --safe --without-K --exact-split #-}`.
- No holes / postulates / `red`. ONLY benign warning allowed: `RuleInst3:328`
  "Unreachable clauses" (appears whenever `lookup_op` / the opaque harness is
  used — harmless).
- Checkpoint `project_t4_internal_cr_files.md` after each green file; commit at
  milestones. End commit messages with the Co-Authored-By trailer.

## What is GREEN (this work; see memory PARTs 23–28)

The whole pipeline is over the SAME applicative coding. ‼ **Scope truth**: the
BRA primitive algebra is `Fun1={s,o,u,C}`, `Fun2={v,R}` ONLY (everything else —
I/Z/Fst/Snd/Const/Lift/Fan/Post — is DEFINED, not a rule). The 6 closed-term
rules are `o,u,v,C,Rb,Rs`. The handoff that called for 14 rules was WRONG.

### Coding + functors (all green)
- `T4.PrCodeObj` — applicative TERM coding: `tmO`, `tmAp1 f t`, `tmAp2 g a b`;
  funcodes `cSuc/cZero/cId/cComp g h1 h2/cProj/cRec g h1 h2`; tags `tgO..tgRec`
  = `natCode 0..8`; projectors `hd=Fst`, `ar=Snd` + all projection eqs.
- `T4.PrDerCode` — DERIVATION coding (binNode/binLeaf), 9 tags
  `dgReflO..dgRs = natCode 0..8`. LABEL = `Pair tag bundle` (Fst=tag, Snd=inert
  carried funcodes). Builders `derLeaf / ap1c f d / ap2c g d1 d2 / derO / derU /
  derV / derC g h1 h2 d / derRb g h1 h2 d / derRs g h1 h2 d1 d2`. Meta shadow
  `DerM` + `codeDer` + `derWf`.
- `T4.PrDev` — `devF` complete development (6 rules). `+ T4.PrDevRcong.devF_R_cong`.
  Modules `Ap1(f t)`, `Ap2(g a b)`, `Rec(g0 h1 h2 a b)` (NP plumbing, generic).
- `T4.PrSrc` / `T4.PrTgt` — `srcF` / `tgtF` endpoint functors (9 tags each).
- `T4.PrTri` / `T4.PrTri2` — `triF` triangle map (15 eqs incl depth-2 ap2c-cRec).

### Shadow CR core (all green) — the SCHEMATIC headline
- `T4.PrTriShadow` — refined shadow `DerM` (mutual funcode shadows
  `Fun1M`/`Fun2M`) + `triMeta` + `triShadowU : triF(codeDer d)=codeDer(triMeta d)`.
- `T4.PrTriPres` — `src_tri` / `tgt_tri` (the triangle COMMUTES) by induction
  on the shadow via `triShadowU` (chains srcF/tgtF/devF eqs).
- `T4.PrDiamond` — `objDiamondU` (internal diamond, meta `RedU`/`Join1U`).
- `T4.PrConfl` — `RedsU`/`stripU`/`conflU` (confluence).
- `T4.PrClash` — `convClashU : ConvU tmO (tmAp1 cSuc tmO) -> Deriv(eqF (ap1 s O) O)`
  = SCHEMATIC `Con(Eq)` (`ConvU`/`RedsU` are META data types — inconsistency
  transfer; this is exactly the toy `DerClash` status).

### Object (opaque) layer (all green) — the INTERNAL upgrade in progress
- `T4.PrWfRed` — object validity `wfRed:Fun1`, base-reject (`wfRed O=s O`),
  9-tag dispatch on `derTagIdx=Fst(label)` + reject default. `wfRed p=O` iff `p`
  is a genuine derivation TREE (does NOT yet validate carried funcodes).
- `T4.PrWfRedShadow` — `wfRed(codeDer d)=O` (validity soundness).
- `T4.PrSrcUOpaque` / `T4.PrTgtUOpaque` — opaque `srcF`/`tgtF` eqs over arbitrary
  `p` via `OpaqueHarness.H (stepOf leaf node)`; recover children with `lookup_op`,
  carried funs as projections `funP p=Snd(dtag p)`, tag-test on `Fst(dtag p)`.
- `T4.PrWfRedUOpaque` — opaque `wfRed` eqs (+ `wfRed_op_reject`); `HBase rejectCell`.
- `T4.PrDevByHead` — ‼ KEY SIMPLIFICATION: `devF` is applied to BUILT srcF-results
  `tmAp1 (funP p)(..)`, so devF opaque = SCHEMATIC-IN-FUN eqs dispatching on
  `Fst f` (`devF_ap1_{o,u,s,C}_h`, `devF_ap2_{v,Rb,Rs,Rcong}_h`). NO harness.
- `T4.PrTriUOpaque` — opaque `triF` eqs, 12 cases (reflO; ap1c_{o,u,s,C} via
  funhead sub-dispatch; ap2c_v; redex O/U/V/C/Rb/Rs). depth-2 ap2c-cRec DEFERRED.
  ‼ The `ap1c-C` residual and `Rs` reconstructed-R are stated with the OPAQUE
  bundle (`Snd(funP p)` / `Pair(natCode 8)(funP p)`), NOT reconstructed components.
- `T4.PrFunValid` — ‼ THE WALL-BREAKER: `recon f` reconstructs a funcode from
  `Fst f`; `funValid f = eqDecO f (recon f)`; `funValid_{s,o,u,C,v,R} :
  funValid f=O & Fst f=natCode k => f = canonical(k)` (e.g.
  `f = cComp (cG f)(cH1 f)(cH2 f)`, `cG f=Fst(Snd f)`). DECIDABLE, no surj-pairing.

## THE OBSTACLE AND ITS FIX (read before assembling)

In the conj3 of an `ap1c`-congruence carrying a COMPOUND fun (head `C`/`R`):
- `(T)` tgt conjunct `tgtF(triF p)=devF(srcF p)` is FINE — both sides use the
  carried fun's PROJECTIONS (`Fst(Snd f)` …) consistently (`PrDevByHead` matches
  `PrTgt`'s `tgtF_rC`).
- `(S)` src conjunct `srcF(triF p)=tgtF p` needs `srcF(derC..)=tmAp1(cComp recon)(..)`
  to equal `tgtF p=tmAp1 (funP p)(..)`, i.e. `cComp(Fst(Snd f)..) = f` =
  RECONSTRUCTION = surjective pairing. **Resolved by `funValid_C f .. : f =
  cComp(cG f)(cH1 f)(cH2 f)`** — feed this from validity.
- REDEX tags `derC/derRb/derRs` are unaffected (bundle = `bun3 g h1 h2`
  directly, components via `axFst`/`axSnd`, no reconstruction).

So: the validity hypothesis fed to the triangle must imply `funValid (funP p)=O`
for the ap1c/ap2c congruence tags.

## REMAINING STEPS (in order; each is a green file)

### STEP 1 — integrate funcode validation into validity
The object `RedU` must use FULL validity = tree + funcodes. Cleanest:
`wfRedFull p = pi (wfRed p) (wfFunRec p)` where `wfFunRec : Fun1` is a binRec
fold over the derivation tree that, at each ap1c/ap2c node, checks
`funValid (carried fun)=O` AND recurses on children. (Mirror `PrWfRed`'s cell
structure; ap1c/ap2c cells = `pi (funValid bundle) (wfFunRec child…)`; redex/leaf
cells just recurse.) Prove `wfFunRec_shadow : wfFunRec(codeDer d)=O`
(needs `funValid(codeF1 fm)=O` — every shadow funcode validates; prove a small
`funValid_codeF1/2` by induction on `Fun1M`/`Fun2M`). Opaque eqs `wfFunRec_op_*`
(harness, same as `PrWfRedUOpaque`) extracting `funValid(funP p)=O` + child
`wfFunRec`. ALTERNATIVE if simpler: keep `wfRed` as tree-validity and thread
`funValid (funP p)=O` as a SEPARATE per-node antecedent derived in the
cov-dispatch from a `wfFunRec p=O` conjunct. Pick whichever keeps the dispatch
cleanest; the RedU relation = `And (wfRed p=O)(And (wfFunRec p=O)(...endpoints))`.

### STEP 2 — depth-2 `triF_op_ap2c_cRec` (mirror PrTri2 onto PrTriUOpaque)
`ap2c` with `Fst(funP p)=8` (R): sub-dispatch on the RIGHT child `pR p`:
- `pR p` is a leaf (`Fst(pR p)=natCode 1`) => `triF p = derRb`-shaped.
- `pR p` is `ap1c`-cSuc (`Fst(dtag(pR p))=dgAp1c` AND `Fst(Snd(dtag(pR p)))=tgSuc`)
  => `triF p = derRs`-shaped, grandchild via `triF_op_ap1c_s (pR p)`.
- else => `ap2c`-cong residual (uses `Pair(natCode 8)(funP p)` opaque, like Rs).
Recover `pR p`'s sub-projections via the harness `op_pR` + further Fst/Snd.
This is the hardest opaque eq (depth-2 + grandchild); see `PrTri2` for the
shadow-level structure to mirror.

### STEP 3 — imp-form opaque eqs
The cov-dispatch (caseElim on `Fst p=1` leaf/node, then on `Fst(dtag p)` 9-way,
then funhead, then depth-2) exposes `ne (p≠O)`, `nl`, `htag`, `funhead`,
`funValid` as ANTECEDENTS (object logic has no λ; can't apply a meta-fn under an
imp). So re-prove each opaque eq in IMP-FORM `imp Γ (eq)` where Γ bundles the
hypotheses, using `T4.GammaCtx` (`Cnj A B = neg(imp A(neg B))` coded conjunction
with `cnjL/cnjR/cnjPair/cnjCurry/cnjUncurry` = internalized deduction theorem,
all green). Template = the toy's `DerTriUOpaqueImp` / `DerSrcUOpaqueImp` etc.
(thread the harness's `ne`-antecedent via `OpaqueHarnessImp.Himp` only where a
child unfold needs `ne` bare — most use `ne` already-bare from `caseElim` of
`Fst p=1`). For the BUILT eqs applied to `triF p`'s known structure, no harness
needed (they're schematic).

### STEP 4 — bundled qcheck/conj3 + per-tag GLUE + dispatch + induction
Follow `T4.QCheckU` / `CRGlueU` / `TriPresDispatch` / `TriPresObj` (toy, green)
and `T4.QCheckProjU` / `BoundedConj`(bigC) / `BoundedConjProj`(bigCLe) (GENERIC
in the property, reuse directly):
- `conj3 : Fun1` = `C sigma (compose1U wfRedFull triF) (C sigma srcEqF tgtEqF)`,
  `srcEqF = compose1U eqDecO-ish (C natEqF (compose1U srcF triF) tgtF)`, etc.
  (use `eqDecO` for the endpoint equalities). `qcheckU = C condFork (C pi Z conj3)
  wfRedFull`. `qcheckU_sound`/`qcheckU_complete` (copy `T4.QCheckU`).
- per-tag GLUE: under `PhiK (=bigC qcheckU O var0=O)` + `A (=wfRedFull sK=O)`,
  build `conj3 sK=O`. For each tag: opaque-destructure `sK` (`srcF_op_X`,
  `tgtF_op_X`, `triF_op_X`, `wfRed_op_X` imp-form), apply BUILT eqs
  (`srcF_ap1c`/`tgtF_ap1c`/`wfRed_ap1c`/`devF_*_h`) to `triF sK`'s KNOWN built
  structure, use IH `conj3(child)=O` (children `pL/pR sK <= var0` via
  `pLValueBound`/`pRValueBound` => `bigCLe` => `qcheckU_sound` => `conj3 child=O`),
  and for ap1c/ap2c-cong funs apply `funValid_C/R` (from the `wfFunRec` conjunct)
  to rewrite the reconstructed `cComp`/`cRec` to `funP sK` so `srcF(triF sK)=tgtF
  sK`. Mirrors `PrTriPres` (shadow) but opaque-destructures at the top.
- DISPATCH: nested `caseElim` (leaf/node, 9-way `Fst(dtag sK)`, funhead, depth-2,
  reject via `wfRed_op_reject => sO=O => exfalso`). Convert `imp A (conj3 sK=O)
  -> imp PhiK (qcheckU sK=O)` via `qcheckU_complete` + `sigBoth`.
- `ruleIndNat 0 {P=PhiK}`: base `Q O` (triF O=derLeaf etc.), step = dispatch.
  Extract `triPresObjOpaque` at free `p` via `bigCLe qcheckU` + `qcheckU_sound`.

### STEP 5 — object chains => internal CR => Con(Eq)
Port `T4.PrDiamond`/`PrConfl`/`PrClash` to OBJECT predicates over coded
reduction chains (`T4.CodedList`): `RedO(p,a,b) = wfRedFull p=O & srcF p=a &
tgtF p=b` (object, opaque-witnessed); `RedsO`/`Join`/`ObjJoin` as coded-list
folds; strip/confl by the free-variable schema consuming `triPresObjOpaque`
(NOT the meta `objDiamondU`). Clash: object head-stability (port `PrClash`'s
`headStabO`/`headStabSuc` using `srcF_op`/`tgtF_op` imp-form) => internal
`Con(Eq)` as the Π⁰₁ free-var schema. Then `Con(T0)` via the `E`-interpretation
(`[t=u] := E(join_{t,u})`; atomic rules = E-intro from a concrete certificate;
cong = congruence-lift; trans = internal confluence; sym/refl trivial; MP/⇒/¬
transfer verbatim since BRA's `Deriv` has `axK/axS/axNeg/mp` over `E`-atoms —
NO cut-elimination needed, per Thierry).

## GOTCHAS (cost real time last session)

- `v`, `u`, `s` are RESERVED (Fun ctors) — NEVER use as pattern/let vars (use
  `vt`, etc.). `C`, `R` are PairAlgebra/Fun ctors — don't bind as vars (use `Cf`).
- `axRefl` needs its explicit term arg: `axRefl t`.
- `compose1U Snd Snd z = Snd(Snd z)` (two applications).
- `Eq.cong` not in scope here — define a local `sucCong`.
- `binNode n l r ≡ tmAp2 n l r` DEFINITIONALLY (reuse `mkAp2_val` to build
  derivation nodes).
- cascade order in `devF`/`PrDev`: ap1 tests 4(o)->5(u)->3(s)->6(C); s FIRES at
  lvl2 (not skip-6).
- import `binNode` from `T4.BinTree`, `ap2c` from `T4.PrDerCode`, `tgO/tgAp1/
  tgSuc` from `T4.PrCodeObj` as needed.
- opaque-eq files emit the benign `RuleInst3:328` "Unreachable clauses" warning
  (from `lookup_op`) — that is FINE.
- The opaque harness `H sbf = HBase Z sbf`; for `wfRed` (base=rejectCell) use
  `HBase rejectCell wfStepU`. `sbf = stepOf <leafcell> <nodecell>`.
- Generic deps that work on ANY binNode coding: `dtag/pL/pR` (DerCodeS =
  Fst(Snd)/Fst(Snd Snd)/Snd(Snd Snd)), `lookup_op` (OpaqueLookup),
  `pLValueBound/pRValueBound`/`argValueBound` (WfRedExtract), `get_tag`
  (ProgParse), `bigC`/`bigCLe` (BoundedConj/BoundedConjProj), `GammaCtx`,
  `EqDecO`, `idxTest_fire/idxTest_skip` (PrDev), `fork_true_to_fst/
  fork_false_to_snd` (DerSrc).

## Honest scope

This is a multi-session grind (STEP 4 alone is `TriPresDispatch`-scale). But
every per-tag content is proven, the funcode wall is broken, and there is no
remaining mathematical obstacle — it is pure transcription volume. The current
SCHEMATIC `Con(Eq)` (`PrClash.convClashU`) is already a real headline; STEPs 1–5
upgrade it to the fully-internal object Π⁰₁ `Con(Eq)`, then `Con(T0)`.
