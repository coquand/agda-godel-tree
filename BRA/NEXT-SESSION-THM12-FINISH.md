# Next session: finish Theorem 12 (atomic shapes + restructure + glue)

## Context (READ FIRST)

Theorem 12 must be unconditional for **f = thmT** (the th-functor) and **g = sb**
(substitution).  See guard15.pdf p.15 for the th definition (`th(4y) = ax(y);
th(4y+1) = sb(KKy, IKy, th(Ly)); th(4y+2) = mp(th(Ky), th(Ly)); th(4y+3) =
ind(th(Ky), th(Ly))`).  Both th and sb use the FULL Fun1/Fun2 grammar
internally (Rec, Comp2, Pair, etc.), so Theorem 12 must work for every Fun1
constructor.  No shortcut.

**HARD CONSTRAINT** — `ih_s_bra` (BRA-Deriv form `mkAp2T sT (cor a)(cor b) =
cor(s a b)`) is NOT generally derivable for arbitrary `s` and was the
blocker.  The TreeEq pattern dissolves it: embed `Df_F2_s` as Fun2
sub-component in chain Df, use `Th12_F2_s` (encoded form) at bridge step.

## What's done (delivered, all typecheck)

### Refactored `BRA/Thm12.agda` (247 LoC, 0.7s)
Mutual structural recursion `thm12_F1 : (f : Fun1) -> Thm12_F1_Result f` and
`thm12_F2 : (g : Fun2) -> Thm12_F2_Result g` inside `module FromBridges`.
Records currently have `Df` and per-x `proof` fields (no `closed` yet —
that's a remaining task).  14 module parameters (Rec/RecP NN bundles +
universal lifts + shape suppliers).

### `BRA/Th12RecCloseS*.agda` (940 LoC across 4 files, 0.7s fresh)
Universal Theorem 12 for `Rec(z, s)`, parametric in `(z, s, z_corLemma,
z_closed, s_closed, Df_F2_s, Df_F2_s_closed, Th12_F2_s)`:

- `Th12RecCloseSNNFun.agda` — chain Fun1 `D_Rec_NN_fun_chain = Comp2 Pair
  (KT tagCode_ruleTrans) inner_dispatch` with `inner_dispatch = Comp2 Pair
  y1_emitter y2_emitter`.  Key: `y2_emitter = Comp2 Df_F2_s I recPair`
  where `recPair = Comp2 Pair (Comp recF Fst)(Comp recF Snd)` and
  `recF = Rec z s`.  At runtime `ap1 y2_emitter (Pair v1 v2) = ap2 Df_F2_s
  (Pair v1 v2) (Pair (recF v1)(recF v2))`.  Closure proofs use
  `KT_reify_substF1_closed` (define inline by Tree induction).

- `Th12RecCloseSNNReduce.agda` — `D_Rec_NN_fun_chain_at_Pair v1 v2`
  proves the BRA reduction.  Pure axComp2 + axKT + axI + axComp + congL/R
  chain.

- `Th12RecCloseSBasePP.agda` — `Th12_F1_Rec_NN_pt v1 v2` is the
  pointwise correctness at Pair input.  Uses `thmTDispRuleTrans_param`
  to dispatch the chain, `parDispAxRecNd` for y1, `Th12_F2_s` for y2,
  `corOfPair` ruleSym to bridge encoded Pair to cor(Pair), and
  `cong1 cor (ruleSym (axRecNd z s v1 v2))` to bridge u4 to
  `cor((Rec z s)(Pair v1 v2))`.  All this as ruleTrans of three pieces:
  `s_thmT_reduce`, `disp`, `bridge_pair`.

- `Th12RecCloseS.agda` — top-level: instantiates
  `BRA.Thm12.Parts.Rec.Construction` with `D_Rec_NN_fun_chain` and
  `Th12_F1_Rec_NN_pt`.  Proves `D_Rec_zs_closed` structurally
  (treats `parEncAxRecLf zT sT` as `reify (nd (natCode tagAxRecLf)
  (nd (code z) (codeF2 s)))` and applies `KT_reify_substF1_closed`).
  Lf-case uses `D_correct_Rec_zs_O`; Pair-case uses
  `D_correct_Rec_zs_Nd` (which is `Th12_F1_Rec_NN_pt` after
  `D_Rec_zs_reduce_Nd` bridge).  Aligns to substF form via three
  eqSubst's (thClosed, D_Rec_zs_closed, codeFTeq1Asym_subst_eq).
  ruleIndBT lifts the two cases; basePair_imp absorbs IHs via
  `axK` twice.  Output: `Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs`
  where `P_Th12_Rec_zs = atomic (eqn (ap1 thmT (ap1 D_Rec_zs (var 0)))
  (codeFTeq1Asym (Rec z s) (var 0)))`.

### `BRA/Th12RecPCloseS*.agda` (989 LoC across 4 files, 0.7s fresh)
Universal Theorem 12 for `RecP(s)`, parametric in `(s, s_closed, Df_F2_s,
Df_F2_s_closed, Th12_F2_s)`.  Mirrors Th12RecCloseS exactly with binary
adjustments:

- **Variable convention** (CRITICAL TRAP): `P_Th12_RecP_s` uses
  `var (suc zero) = p` (param, fresh) and `var zero = x` (recursion var).
  This is OPPOSITE the standard `Thm12_F2_Result.proof : (x v : Term) -> ...`
  where x = first arg (= p in RecP), v = second arg (= x in RecP).
  When wiring into Thm12.agda the result needs `ruleInst` to swap.
- Chain Fun2 `D_RecP_NN_fun_chain = Fan (Lift (KT tagCode_ruleTrans))
  inner_dispatch Pair`.  `y2_emitter = Fan Pair recP_pair Df_F2_s`.
  `recP_first = Fan (Lift I) fstX recPF` where `fstX = Post Fst (Post
  Snd Pair)` extracts `Fst x` from `(p, x)` input.
- BasePP: `Th12_F2_RecP_NN_pt p v1 v2` uses `thmTDispAxRecPNd_param`
  (already in BRA.Thm.ThmT) for y1, `Th12_F2_s` at `(Pair p (Pair v1 v2),
  Pair rec_v1 rec_v2)` for y2.  Note `cf2 = reify (codeF2 (RecP s))`
  unfolds to `ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT`
  definitionally — match `recP_head` in parOutAxRecPNd.
- Top-level: `Th12_F2_RecP_s : Deriv P_Th12_RecP_s` via ruleIndBT on var 0.

## Mental model (READ BEFORE PROCEEDING — corrected per user feedback)

`thm12_F1 : (f : Fun1) -> Deriv (P_Th12 f)` is a function defined by mutual
structural recursion on Fun1 and Fun2 syntax.  Each constructor case is
LITERALLY a one-liner pointing at an already-existing proof:

```agda
thm12_F1 I        = Th12_F1_I       -- from BRA.Th12I
thm12_F1 Fst      = Th12_F1_Fst     -- from BRA.Th12Fst
thm12_F1 Snd      = Th12_F1_Snd     -- from BRA.Th12Snd
thm12_F1 Z        = Th12_F1_Z       -- from BRA.Th12Z
thm12_F1 (Comp f g)    = <use Th12CompCase with thm12_F1 f, thm12_F1 g>
thm12_F1 (Comp2 h f g) = <use Th12Comp2Case with thm12_F2 h, thm12_F1 f, thm12_F1 g>
thm12_F1 (Rec z s)     = <use Th12RecCloseS_Case with thm12_F2 s>

thm12_F2 Pair    = Th12_F2_Pair     -- from BRA.Th12Pair
thm12_F2 Const   = Th12_F2_Const    -- from BRA.Th12Const
thm12_F2 IfLf    = Th12_F2_IfLf     -- from BRA.Th12IfLf
thm12_F2 TreeEq  = Th12_F2_TreeEq   -- from BRA.Th12TreeEqClose
thm12_F2 (Lift f)      = <use Th12LiftCase with thm12_F1 f>
thm12_F2 (Post f h)    = <use Th12PostCase>
thm12_F2 (Fan h1 h2 h) = <use Th12FanCase>
thm12_F2 (RecP s)      = <use Th12RecPCloseS_Case with thm12_F2 s>
```

To make these clauses literally typecheck as `Deriv (P_Th12 f)`, define
the unified statement via:

```agda
Df_of : Fun1 -> Fun1
Df_of I        = Df_F1_I
Df_of Fst      = Df_F1_Fst
Df_of Snd      = Df_F1_Snd
Df_of Z        = Df_F1_Z
Df_of (Comp f g)    = <Comp's witness Fun1, structural over Df_of f, Df_of g>
Df_of (Comp2 h f g) = <similarly>
Df_of (Rec z s)     = <D_Rec_zs from Parts/Rec.Construction>

Dg_of : Fun2 -> Fun2
... (analogous)

P_Th12 : Fun1 -> Formula
P_Th12 f = atomic (eqn (ap1 thmT (ap1 (Df_of f) (var zero)))
                       (codeFTeq1Asym f (var zero)))

P_Th12_F2 : Fun2 -> Formula
P_Th12_F2 g = atomic (eqn (ap1 thmT (ap2 (Dg_of g) (var zero) (var (suc zero))))
                          (codeFTeq2Asym g (var zero) (var (suc zero))))
```

Then `Th12_F1_Fst : Deriv P_Th12_Fst` typechecks as `Deriv (P_Th12 Fst)`
because `Df_of Fst = Df_F1_Fst` is definitional and `P_Th12 Fst`
unfolds to `P_Th12_Fst`.

**The result type of `thm12_F1` is just `Deriv (P_Th12 f)` — no record,
no shape field, no closure field.**  Auxiliary properties (shape /
closure) needed by particular cases (Comp2, Fan, Rec, RecP internally)
are defined as SEPARATE functions on the syntax, also one-liner per case.
For example:

```agda
shape_of_Df : (f : Fun1) -> (x : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap1 (Df_of f) x)) (ap2 Pair x' y')))))
shape_of_Df I       x = <derive from Df_F1_I structure>
shape_of_Df Fst     x = <derive from Df_F1_Fst's IfLf-dispatch + D_Fst_reduce_O / _Pair>
...
```

These auxiliaries are needed only by the few cases that consume them
internally.  They are NOT a "task" separate from the recursion.

**Remaining work is purely plumbing**: write Df_of (15 clauses), thm12_F1 /
thm12_F2 (15 clauses), and any auxiliary recursions needed by composite /
recursor cases.  No new mathematics.

## What's left (estimated ~600–900 LoC plumbing, 1 session)

### Task A: Define `Df_of`, `Dg_of`, `P_Th12_F1`, `P_Th12_F2`

NO records.  `thm12_F1` returns just `Deriv (P_Th12_F1 f)`.

```agda
Df_of : Fun1 -> Fun1
Df_of I             = Df_F1_I             -- BRA.Th12I
Df_of Fst           = Df_F1_Fst           -- BRA.Th12Fst
Df_of Snd           = Df_F1_Snd           -- BRA.Th12Snd
Df_of Z             = Df_F1_Z             -- BRA.Th12Z
Df_of (Comp f g)    = ?                   -- structural over Df_of f, Df_of g
Df_of (Comp2 h f g) = ?                   -- via Th12Comp2Case's D_Comp2_hfg
Df_of (Rec z s)     = ?                   -- D_Rec_zs from Th12RecCloseS_Case

Dg_of : Fun2 -> Fun2
Dg_of Pair    = Df_F2_Pair                -- BRA.Th12Pair
Dg_of Const   = Df_F2_Const               -- BRA.Th12Const
Dg_of IfLf    = Df_F2_IfLf                -- BRA.Th12IfLf
Dg_of TreeEq  = D_TreeEq                  -- BRA.Th12TreeEqClose
Dg_of (Lift f)      = ?
Dg_of (Post f h)    = ?
Dg_of (Fan h1 h2 h) = ?
Dg_of (RecP s)      = ?                   -- D2_RecP_s from Th12RecPCloseS_Case

P_Th12_F1 : Fun1 -> Formula
P_Th12_F1 f = atomic (eqn (ap1 thmT (ap1 (Df_of f) (var zero)))
                          (codeFTeq1Asym f (var zero)))

P_Th12_F2 : Fun2 -> Formula
P_Th12_F2 g = atomic (eqn (ap1 thmT (ap2 (Dg_of g) (var zero) (var (suc zero))))
                          (codeFTeq2Asym g (var zero) (var (suc zero))))
```

Each `Df_of` clause for an atomic constructor is a one-liner pointing at
the existing `Df_F1_X` / `Df_F2_X`.  For composite cases, `Df_of` is the
witness Fun1 / Fun2 produced by the corresponding parametric module
(CompCase, Comp2Case, etc.) instantiated with `Df_of f` / `Dg_of g`
recursively — i.e., `Df_of (Comp f g) = D_Comp_f'g` from
`Th12CompCase f g (Df_of f) (Df_of g) (proof_of f) (proof_of g)`.

Auxiliary functions (`shape_of_Df`, `closure_of_Df`) needed internally by
some composite cases are SEPARATE recursions on the syntax, also one-liner
per case, NOT bundled with the proof.  Define them only when a downstream
case actually needs them.

### Task B: Auxiliary `shape_of_Df` recursion (only if Comp2 / Fan cases need it)

If `Comp2` and `Fan` cases internally need `Df_shape (Df_of f)`, write it as
a separate recursion:

```agda
shape_of_Df : (f : Fun1) (x : Term) ->
  Sigma Term (\ y' -> Sigma Term (\ x' ->
    Deriv (atomic (eqn (ap1 Fst (ap1 (Df_of f) x)) (ap2 Pair x' y')))))
shape_of_Df I        x = ...   -- from D_F1_I_reduce
shape_of_Df Fst      x = ...   -- per-x case via D_Fst_reduce_O / _Pair
shape_of_Df Snd      x = ...
shape_of_Df Z        x = ...
shape_of_Df (Comp f g)    x = ...   -- via D_Comp_reduce + tagCode_ruleTrans head
shape_of_Df (Comp2 h f g) x = ...
shape_of_Df (Rec z s)     x = ...

shape_of_Dg : (g : Fun2) (x v : Term) -> ...
```

Each clause one-liner-ish, ~10–50 LoC.  No "~450 LoC" — that figure was
from a universal-uniform-witness version (witness independent of x), a
DIFFERENT and harder problem than what Comp2 / Fan actually consume.

### Task C: Restructure Thm12.agda (~250 LoC)

Replace the `FromBridges` module with a leaner one that takes ONLY:

```agda
module FromBridges
  -- Closure suppliers: caller asserts that all (z, s) appearing in
  -- Rec(z, s) and RecP(s) sub-expressions are closed at the syntactic
  -- level.  In practice this holds for th, sb (z = O, s closed combinators).
  (z_closed_supplier : (z : Term) (n : Nat) (r : Term) -> Eq (subst n r z) z)
  (s_closed_supplier : (s : Fun2) (n : Nat) (r : Term) -> Eq (substF2 n r s) s)

  -- Per-z corollary: cor z = reify (code z).  For closed Tree-shaped z
  -- (e.g. z = O via axRecLf O stepCor; z = reify t via corOfReify).
  (z_corLemma_for : (z : Term) -> Deriv (atomic (eqn (ap1 cor z) (reify (code z)))))

  -- Atomic shape suppliers (from Task B).
  (shape_D_Fst   : ShapeF1 D_Fst)
  (shape_D_Snd   : ShapeF1 D_Snd)
  (shape_D_IfLf  : ShapeF2 D_IfLf)
  (shape_D_TreeEq : ShapeF2 D_TreeEq_NN_fun)
  -- Plus shape lemmas for Comp/Comp2/Lift/Post/Fan/Rec/RecP results
  -- (built recursively from sub-shapes).
```

Inline Rec case using `Th12RecCloseS_Case`:
```agda
thm12_F1 (Rec z s) = record { Df = R.D_Rec_zs ; closed = R.D_Rec_zs_closed ; proof = ... }
  where
    rs = thm12_F2 s
    Df_s = Thm12_F2_Result.Dg rs
    Df_s_closed = Thm12_F2_Result.closed rs
    Th12_F2_s_per_xv = Thm12_F2_Result.proof rs  -- (x v : Term) -> Deriv (per-(x,v))
    -- z is a Term; use z_closed_supplier z and z_corLemma_for z.
    module R = BRA.Th12RecCloseS.Th12RecCloseS_Case
                 z s (z_corLemma_for z) (z_closed_supplier z)
                 (s_closed_supplier s) Df_s Df_s_closed Th12_F2_s_per_xv
    -- Universal Th12_F1_Rec_zs : Deriv P_Th12_Rec_zs at (var 0).
    -- Convert to per-x via ruleInst zero x + closure bridges.
    proof : (x : Term) -> Deriv (atomic (eqn (ap1 thmT (ap1 R.D_Rec_zs x)) (codeFTeq1 (Rec z s) x)))
    proof x = ... -- ruleInst chain (see Task D for the conversion pattern)
```

Inline RecP case using `Th12RecPCloseS_Case` — similar, **PLUS a var swap**
because RecP convention is (var 1 = p, var 0 = x) and standard is
(var 0 = first arg, var 1 = second arg):
```agda
thm12_F2 (RecP s) =
  let rs = thm12_F2 s
      ...
      module R = BRA.Th12RecPCloseS.Th12RecPCloseS_Case s ...
      -- R.Th12_F2_RecP_s : Deriv at (var 1, var 0)
      -- Want: per-(p, x) form.
      proof : (p x : Term) -> Deriv ...
      proof p x =
        let r1 = ruleInst (suc zero) p R.Th12_F2_RecP_s  -- substitute p at var 1
            r2 = ruleInst zero x r1                       -- substitute x at var 0
        in eqSubst-bridge-via-closures r2  -- align to per-(p, x) form
  in record { Dg = R.D2_RecP_s ; closed = R.D2_RecP_s_closed ; proof = proof }
```

For the other 13 cases, use existing Thm12.Parts.X.D_correct(_2)_X (per-x
form) plus closure proofs derived from sub-results' closures + KT_reify
helpers.

### Task D: Per-(x, v) conversion helper (~100 LoC)

Generic helper for atomic Fun2 (IfLf, TreeEq) where universal form is
available but per-(x, v) requires conversion:

```agda
universal_to_per_xv :
  (g : Fun2) (Dg : Fun2)
  (Dg_closed : (n : Nat) (r : Term) -> Eq (substF2 n r Dg) Dg)
  (proof_univ : Deriv (atomic (eqn (ap1 thmT (ap2 Dg (var 0) (var 1)))
                                    (codeFTeq2 g (var 0) (var 1)))))
  -> (x v : Term) -> Deriv (atomic (eqn (ap1 thmT (ap2 Dg x v)) (codeFTeq2 g x v)))
universal_to_per_xv g Dg Dg_closed proof_univ x v =
  let r1 = ruleInst zero x proof_univ      -- Deriv (substF zero x P)
      r2 = ruleInst (suc zero) v r1        -- Deriv (substF (suc zero) v (substF zero x P))
  in eqSubst-chain-using-closures-and-substF-reductions r2
```

The substF reduction for `codeFTeq2 g (var 0)(var 1)` involves substituting
into `cor (var 0)`, `cor (var 1)`, `ap2 g (var 0)(var 1)`, `reify (codeF2 g)`.
Closures: thClosed, Dg_closed, refl for codeF2 (closed at type level for
fixed g), structural for cor.

### Task E: Glue file (~200 LoC)

`BRA/Thm12Final.agda` (or rename existing) instantiates `FromBridges` with:
- z_closed_supplier: works at z = O (refl); use `subst-O-closed` lemma
  (probably `\ z n r -> refl` if all uses pass closed Trees).  In practice
  all Rec sub-expressions in th, sb have z = O.
- s_closed_supplier: derive structurally from Fun2 syntax (closed at
  Fun2 syntax level → refl).
- z_corLemma_for: at z = reify t use `corOfReify` (already in Cor.agda).
- Shape suppliers: from Task B.

Then `thm12_F1 thmT : Thm12_F1_Result thmT` and `thm12_F2 sb :
Thm12_F2_Result sb` — Theorem 12 unconditional.

### Task F: Verify

Build `Thm12Final.agda`.  Confirm `thm12_F1 thmT` and `thm12_F2 sb` typecheck.
Save memory: `project_thm12_universal_done.md`.

## Critical traps (don't rediscover)

1. **`KT (reify T)` closure** — `substF1 n r (KT (reify T)) = KT (reify T)`
   is NOT refl in general.  Define
   ```agda
   KT_reify_substF1_closed : (T : Tree) (n : Nat) (r : Term) ->
     Eq (substF1 n r (KT (reify T))) (KT (reify T))
   KT_reify_substF1_closed lf       n r = refl
   KT_reify_substF1_closed (nd a b) n r =
     eqCong2 (\ a' b' -> Comp2 Pair a' b')
       (KT_reify_substF1_closed a n r)
       (KT_reify_substF1_closed b n r)
   ```
   For closures involving `parEncAxRecLf zT sT`, treat it as
   `reify (nd (natCode tagAxRecLf) (nd (code z) (codeF2 s)))` and apply
   `KT_reify_substF1_closed` directly.  See
   `Th12RecCloseS.parEncAxRecLf_tree`.

2. **RecP variable convention** — Th12RecPCloseS uses `var 1 = p, var 0 = x`
   internally because ruleIndBT inducts on var 0 and the recursion var must
   be at var 0.  When wiring into Thm12_F2_Result (standard convention
   `(x v : Term) -> ap2 Dg x v` where x = first arg), apply two ruleInst
   in sequence: first `ruleInst (suc zero) p` then `ruleInst zero x`.

3. **`thmTDispRuleTrans_param` does NOT enforce u2 = u3** — it
   syntactically pulls u1 from d1's RHS and u4 from d2's RHS.  The chain's
   semantic validity is the caller's responsibility, but the dispatcher
   produces `Pair u1 u4` regardless.  This is what makes the TreeEq
   pattern work without `ih_s_bra`.

4. **`mkAp2T cf2_recPs ...` matches `parOutAxRecPNd`'s LHS slot** —
   `cf2 = reify (codeF2 (RecP s)) = ap2 Pair (reify (natCode 33)) sT`
   (33 is the Rec tag).  And `parOutAxRecPNd` uses `Pair (reify (leftT
   (codeF2 (RecP IfLf)))) sT`.  These ARE definitionally equal; both
   reduce to the same Pair.

5. **`cong1 cor (ruleSym (axRecNd z s v1 v2))`** is the bridge from
   `cor (s pairT pairR)` to `cor ((Rec z s)(Pair v1 v2))`.  No IH needed —
   axRecNd is a BRA primitive axiom.  Same for `axRecPNd s p v1 v2`.

6. **Shape obstruction for D_Fst, D_Snd** — Shapes.agda comments say
   ~450 LoC each via ruleIndBT.  Worth checking whether the shape is
   actually needed at arbitrary x or only at fixed shapes — Parts/Comp2
   and Parts/Fan call shape at runtime at the actual D-output, which is
   one specific Term per call.  If we can prove shape only at the inputs
   actually used, much smaller.

## Starting commands for next session

```bash
cd /Users/coquand/CHWISTEK

# 1. Verify the starting state typechecks (Rec + RecP closures + current Thm12.agda):
agda BRA/Th12RecCloseS.agda    # 0.7s, expected EXIT 0
agda BRA/Th12RecPCloseS.agda   # 0.7s, expected EXIT 0
agda BRA/Thm12.agda            # 0.7s, current FromBridges form (will be replaced)

# 2. Check existing universal Th12 proofs for the 8 atomic-ish cases:
grep -n "^Th12_F1_\|^Th12_F2_" BRA/Th12I.agda BRA/Th12Z.agda BRA/Th12Fst.agda BRA/Th12Snd.agda \
                                BRA/Th12Pair.agda BRA/Th12Const.agda BRA/Th12IfLf.agda \
                                BRA/Th12TreeEqClose.agda

# 3. Read the design — the unified statement uses codeFTeq1Asym / codeFTeq2Asym.
#    Verify all 8 atomic Th12_F[12]_X already use this form (they do):
grep -n "codeFTeq1Asym\|codeFTeq2Asym" BRA/Th12I.agda BRA/Th12Fst.agda BRA/Th12Pair.agda \
                                        BRA/Th12IfLf.agda BRA/Th12TreeEqClose.agda

# 4. Then start writing BRA/Thm12.agda's replacement, using
#    Df_of / Dg_of / P_Th12_F1 / P_Th12_F2 + thm12_F1 / thm12_F2 as outlined.
```

## Memory pointers (update / read)

- `project_thm12_recclose_done.md` — Rec closure delivered.
- `project_thm12_recpclose_done.md` — RecP closure delivered.
- `feedback_no_thm12_route_was_wrong.md` — earlier shortcuts rejected.
- `feedback_th14_needs_strict_thm12.md` — Theorem 14 needs unconditional Theorem 12.
- `feedback_pre_flight_guard15.md` — verify guard15.pdf statements before starting.
- `feedback_treeeq_needs_indBT2.md` — TreeEq pattern reference (the template Rec/RecP follow).
- `project_th12_treeeq_close_done.md` — TreeEq universal pattern (the template).

## File map

```
BRA/Thm12.agda                             247  current FromBridges (REPLACE in Task C)
BRA/Th12RecCloseS.agda                     252  top-level Rec closure
BRA/Th12RecCloseSBasePP.agda               258  Rec NN-pt
BRA/Th12RecCloseSNNFun.agda                233  Rec chain Fun1 + closure
BRA/Th12RecCloseSNNReduce.agda             197  Rec BRA reduction at Pair
BRA/Th12RecPCloseS.agda                    248  top-level RecP closure
BRA/Th12RecPCloseSBasePP.agda              248  RecP NN-pt
BRA/Th12RecPCloseSNNFun.agda               249  RecP chain Fun2 + closure
BRA/Th12RecPCloseSNNReduce.agda            244  RecP BRA reduction at (p, Pair)

BRA/Thm12/Parts/I.agda           D_I, D_correct_I            — used as-is in Task C
BRA/Thm12/Parts/Z.agda           D_Z, D_correct_Z
BRA/Thm12/Parts/Fst.agda         D_Fst, D_correct_Fst
BRA/Thm12/Parts/Snd.agda         D_Snd, D_correct_Snd
BRA/Thm12/Parts/Pair.agda        D2_Pair, D_correct2_Pair
BRA/Thm12/Parts/Const.agda       D2_Const, D_correct2_Const
BRA/Thm12/Parts/IfLf.agda        D_IfLf, D_correct2_IfLf_univ (universal form), D_correct2_IfLf (per-(x,v) with closures)
BRA/Thm12/Parts/Comp.agda        Th12CompCase parametric module
BRA/Thm12/Parts/Comp2.agda       Th12Comp2Case (uses Df_shape, Dg_shape)
BRA/Thm12/Parts/Lift.agda        Th12LiftCase
BRA/Thm12/Parts/Post.agda        Th12PostCase
BRA/Thm12/Parts/Fan.agda         Th12FanCase (uses D2_h_shape's)
BRA/Thm12/Parts/Rec.agda         Construction module — INSTANTIATED in Th12RecCloseS.agda
BRA/Thm12/Parts/RecP.agda        Construction module — INSTANTIATED in Th12RecPCloseS.agda
BRA/Thm12/Parts/TreeEq.agda      ConstructionBase — INSTANTIATED in Th12TreeEqClose.agda
BRA/Thm12/Shapes.agda            Closed shapes for I, Z, D2_Pair, D2_Const + parametric
                                 ShapesComp/ShapesLift/ShapesPost.  Missing: D_Fst, D_Snd, D_IfLf, D_TreeEq.

BRA/Th12IfLf.agda                Th12_F2_IfLf : Deriv P_Th12_IfLf (universal at var 0/1)
BRA/Th12TreeEqClose.agda         Th12_F2_TreeEq : Deriv P_Th12_TreeEq (universal)
BRA/Th12TreeEqNNFun.agda         template for the chain pattern (D_IfLf embedded in y2)
BRA/Th12TreeEqBasePP.agda        template for the bridge pattern

BRA/Thm14CodeFTeqAsym.agda       codeFTeq1Asym, codeFTeq2Asym, mkAp1T, mkAp2T
BRA/CorOfPair.agda               corOfPair, corOfFstPair, corOfSndPair
BRA/Cor.agda                     cor, stepCor, corOfReify (for z_corLemma at z = reify t)
BRA/ReifyClosed.agda             reifyClosed
BRA/Thm/ThmT.agda                thmTDispRuleTrans_param, thmTDispAxRecNd_param,
                                 thmTDispAxRecPNd_param, thClosed, thmTDispRuleInst_param
BRA/Thm/Parts/RuleInst.agda      ruleInst : (n : Nat) (t : Term) -> Deriv P -> Deriv (substF n t P)
BRA/Thm/Parts/RuleIndBT.agda     ruleIndBT (1D) — Rec uses this
BRA/Thm/Parts/RuleInst2.agda     ruleInst2 if needed
```

## Final note on the variable swap for RecP

The convention mismatch is the trickiest part of Task C.  Concretely: after
`R.Th12_F2_RecP_s : Deriv (atomic (eqn (ap1 thmT (ap2 D2_RecP_s (var 1)(var 0)))
(codeFTeq2Asym (RecP s) (var 1)(var 0))))`, applying `ruleInst (suc zero) p`
gives a Deriv with var 1 substituted by p; then `ruleInst zero x` substitutes
var 0 by x.  The substF reductions: `subst (suc zero) p (var 1) = p`,
`subst zero x (var 0) = x`, and codeFTeq2Asym substitutes structurally (since
its body only uses the supplied Term args via cor/codeF2).  Closure of
D2_RecP_s and thmT closes the rest.  Build the eqSubst chain carefully
mirroring `Th12RecPCloseS.basePair_substF`.
