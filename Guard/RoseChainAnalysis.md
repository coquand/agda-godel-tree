# Rose Theorem 4 chain — analysis and plan

## What I initially missed

In RoseDC2Analysis.md I claimed the polymorphic roseLemma1 (DC2, Lemma 1 for n≥1 hypotheses) was required by Rose's Theorem 4 and was ~1500-2000 lines of work.  On a careful re-read of Rose1.pdf p.381-383 this is WRONG.

## The actual structure of Rose's Theorem 4

Rose's chain (p.383) uses Lemma 1 twice:

1. `th(p_G(z,0)) = {G(z)=0} → th(V(p_G(z,0))) = {se(nu(N),N) = th(z)}`

   The derivation BEING INTERNALISED here is:  from  {G(z) = 0} (a computational fact) derive {se(nu(N), N) = th(z)}.  This is a CLOSED derivation (zero hypotheses beyond the axioms) -- it's just unfolding G's definition  G(z) = |se(nu(N),N), th(z)|  + the fact that  |a, b| = 0 ↔ a = b .

2. `Y(x, t)` satisfying  `th(Y(x,t)) ≠ {f(x)=0} → th(t) ≠ [f(z)=0]`

   The derivation being internalised is  numeral-substitution (substitute numeral z for variable x).  Again CLOSED: it's a one-step ruleInst derivation.

**Both uses are n=0 (no hypotheses).**  Rose's general Lemma 1 statement has n≥0, but for Theorem 4 only the n=0 specialisation is actually needed.

## In our Agda setting

Lemma 1 for n=0 is exactly DC1, which is exactly  `thm14EV3`  — we have it.  The full Lemma 1 machinery exported via  `RoseDC1.p_<rule>`  and  `p_dc1 = thm14EV3`  covers every case needed.

The polymorphic n≥1 case is NOT needed for Theorem 4, only for more general meta-theorems (like arbitrary Hilbert-Bernays DC2 at the formal system level).

## What's actually needed for Theorem 4

The seven-step chain of impT-implications, each closed by `mpT` at the meta-level:

```
step 1.  th(z) = se(nu(N), N)                    -- assumption
step 2. →  G(z) = 0                               -- computational
step 3. →  th(p_G(z, 0)) = {G(z) = 0}             -- DC1 on a concrete closed Deriv
step 4. →  th(V(p_G(z, 0))) = {se(nu(N),N) = th(z)}   -- DC1 on a concrete closed Deriv
step 5. →  e(th(V(...))) = {se(nu(N),N) ≠ th(z)} -- application of negation-encoder e
step 6. →  th(Y(z, z)) ≠ {se(nu(N),N) ≠ th(z)}    -- USES CONSISTENCY hypothesis
step 7. →  th(z) ≠ [se(nu(N),N) ≠ th(z)]         -- by (i) = Lemma 1 for Y
step 8. →  th(z) ≠ se(nu(N), N)                   -- by Lemma 3 = godelIClassical
```

Then reductio with Lemma 3 gives the theorem.

## Translation to our tree-setting

| Rose's symbol            | Our analogue                                                |
|--------------------------|-------------------------------------------------------------|
| th(t)                    | `ap1 (thmT trivCT) t`                                       |
| [A] (Gödel number of A)  | `reify (codeEqn A)`                                         |
| se(x, y, [A]) (subst)    | encoded substitution (SubstOp module)                       |
| nu(x) (numeral code)     | `reify (natCode x)` for variable index; reify code for terms |
| e(t) (negation encoder)  | map from "t = u" to "t ≠ u" at the code level               |
| |a, b| = 0               | `ap2 TreeEq a b = O` (trueT)                                |
| a ≠ b (meta-level)       | `ap2 TreeEq a b = falseT`                                   |
| a → b (object impl.)     | `impT A B = ap2 IfLf A (ap2 Pair B O)` (Guard.ImpT)         |
| z (Gödel sentence idx)   | specific encoding `enc_gs` of gsCR's proof structure         |
| Lemma 3 (Gödel I)        | `godelIClassical`                                           |
| Lemma 2                  | `RoseDC1.p_<ax>`                                            |
| Lemma 1 n=0              | `thm14EV3` = `RoseDC1.p_dc1`                                |

## Translation gaps we might hit

- **`se` and `nu`**: we have SubstOp for substitution;  reify (natCode n)  for numeral codes.  Should be fine.
- **`e` (negation encoder)**: in Rose, e takes a code of "A = B" and returns a code of "A ≠ B".  In our tree setting, equations are encoded as `codeEqn (eqn a b) = nd (code a) (code b)`.  "A ≠ B" isn't directly representable as an Equation in our Deriv (we only have = equations).  **GAP**: step 5 in the chain introduces negation-coded equations that don't live in our Deriv.

- **`|a, b|` (absolute-value difference)**: not a primitive in our tree setting.  We have  `ap2 TreeEq a b`  which returns O if equal, poo otherwise.  Maybe a Fun2 that returns O when inputs are equal, Pair O O when unequal.  **CLOSE**: we'd use `ap2 TreeEq` as an analogue of `|·,·|`.

- **Consistency hypothesis in step 6**: Rose's consistency statement is  `th(y) ≠ e(th(z))`  -- uses e.  Without e as a primitive, our ConTrivRose uses a different formulation:  `impT (TreeEq (thmT x) codeBotT) falseT = trueT`.  These are classically equivalent but may require a separate bridge.

## Plan

Attempt the chain directly.  For each step:

1.  Try to construct the specific `impT`-link as a Deriv in Triv.
2.  If we hit a  gap  (like  e  or  Y  not being directly available), document precisely where and pause.

Start with step 2 (G(z) = 0 from th(z) = se(nu(N),N)) since step 1 is just the assumption.

Status: in progress.
