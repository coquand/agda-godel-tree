# Audit of `BRA/Deriv.agda`'s 40 primitives

Classification: **(a) genuine primitive**, **(b) structurally derivable
(intuitionistic)**, **(c) classically derivable**.  Target: shrink to a
pruned primitive set that drives `thmT`'s tag schema.

## Combinator defining equations (21, all genuine)

These are the direct defining equations of BRA's primitive combinators
— Guard's Ax 0-3 and their project extensions.  Every one is needed
because it IS the meaning of its combinator.  All 21 **genuine (a)**.

| Name          | Comment                                                   |
|---------------|-----------------------------------------------------------|
| `axI`         | `I t = t`                                                 |
| `axFst`       | `Fst (Pair a b) = a`                                      |
| `axSnd`       | `Snd (Pair a b) = b`                                      |
| `axConst`     | `Const a b = a`                                           |
| `axComp`      | `(f ∘ g) t = f (g t)`                                     |
| `axComp2`     | `Comp2 h f g t = h (f t) (g t)`                           |
| `axLift`      | `Lift f a b = f a`                                        |
| `axPost`      | `Post f h a b = f (h a b)`                                |
| `axFan`       | `Fan h1 h2 h a b = h (h1 a b) (h2 a b)`                   |
| `axKT`        | `KT t x = t`                                              |
| `axRecLf`     | `Rec z s O = z`                                           |
| `axRecNd`     | `Rec z s (Pair a b) = s (Pair a b) (Pair (Rec z s a) (Rec z s b))` |
| `axRecPLf`    | `RecP s p O = O`                                          |
| `axRecPNd`    | `RecP s p (Pair a b) = s (Pair p (Pair a b)) (Pair (RecP s p a) (RecP s p b))` |
| `axIfLfL`     | `IfLf O (Pair a b) = a`                                   |
| `axIfLfN`     | `IfLf (Pair x y) (Pair a b) = b`                          |
| `axTreeEqLL`  | `TreeEq O O = O`                                          |
| `axTreeEqLN`  | `TreeEq O (Pair a b) = Pair O O`                          |
| `axTreeEqNL`  | `TreeEq (Pair a b) O = Pair O O`                          |
| `axTreeEqNN`  | `TreeEq (Pair a1 a2) (Pair b1 b2) = IfLf (TreeEq a1 b1) (Pair (TreeEq a2 b2) (Pair O O))` |
| `axGoodstein` | `IfLf (TreeEq a b) (Pair a O) = IfLf (TreeEq a b) (Pair b O)` — Goodstein's schema; says "a and b are interchangeable inside the `TreeEq`-guarded `IfLf`."  Not derivable from the other combinator equations (which only cover canonical-form reductions).  Genuine. |

## Structural equational rules (6, all derivable → demote)

The comment in `Deriv.agda` says these are derivable from Ax 4-7 + mp
+ ruleInst + axRefl.  Concrete derivations:

| Name        | Derivation                                                     | Class |
|-------------|----------------------------------------------------------------|-------|
| `axRefl`    | `ruleInst 0 t (axEqTrans (var 0) (var 0) (var 0))`-based chain; needs care, but available from Ax 4-7 + ruleInst per Guard Ex 17-18. | (b) |
| `ruleSym`   | `mp (mp (axEqTrans t u t) H) (axRefl t)` | (b) |
| `ruleTrans` | `mp (mp (axEqTrans u t v) (ruleSym H1)) H2` | (b) |
| `cong1`     | `mp (axEqCong1 f a b) H` | (b) |
| `congL`     | `mp (axEqCongL g a b c) H` | (b) |
| `congR`     | `mp (axEqCongR g c a b) H` | (b) |

**All 6 demotable.**  Cost of demotion: every `BRA/Sub.agda`,
`BRA/SubT.agda`, `BRA/Cor.agda`, `BRA/Mp.agda`, `BRA/CodeCommutes.agda`,
`BRA/Thm11Diagonal.agda` site that currently uses them has to either
keep using them as Agda-level helpers (same surface syntax) or be
rewritten.  Since the derivations are one-line combinators, exporting
them as helpers preserves ergonomics with zero downstream churn.

## Formula-level equality axioms (4, all genuine)

Guard's Ax 4-7.  Genuine base axioms for equality.  **All 4 (a).**

| Name         | Comment                                            |
|--------------|----------------------------------------------------|
| `axEqTrans`  | Ax 4: `a = b ⊃ (a = c ⊃ b = c)`                     |
| `axEqCong1`  | Ax 5: `a = b ⊃ f a = f b`                           |
| `axEqCongL`  | Ax 6: `a = b ⊃ g a c = g b c`                       |
| `axEqCongR`  | Ax 7: `a = b ⊃ g c a = g c b`                       |

## Propositional axioms (5 → keep 3, demote 2)

| Name         | Class | Note                                                               |
|--------------|-------|--------------------------------------------------------------------|
| `axK`        | (a)   | Hilbert K. Genuine.                                                |
| `axS`        | (a)   | Hilbert S. Genuine.                                                |
| `axNeg`      | (b)   | Curried form `~P ⊃ ~Q ⊃ (Q ⊃ P)`.  Intuitionistically derivable from `axExFalso`.  Demote. |
| `axExFalso`  | (c)   | `P ⊃ (~P ⊃ Q)`.  Derivable from `axContrapos + axK + axS + mp` (classical).  Demote. |
| `axContrapos`| (a)   | `(P ⊃ Q) ⊃ (~Q ⊃ ~P)`.  Classical contraposition.  NOT intuitionistic.  Genuine classical primitive. |

Three genuine: `axK`, `axS`, `axContrapos`.  Two demoted: `axNeg`,
`axExFalso`.

## Inference rules (4 → keep 3, demote 1)

| Name         | Class | Note                                                                 |
|--------------|-------|----------------------------------------------------------------------|
| `mp`         | (a)   | Modus ponens.  Genuine.                                              |
| `ruleInst`   | (a)   | Substitution rule.  Genuine (Guard Def 7 rule 2).                    |
| `ruleIndBT`  | (a)   | Binary-tree induction.  Genuine (Guard Def 7 rule 3 analog).         |
| `ruleF`      | (b)   | Schema F (uniqueness of tree recursion).  Derivable from `ruleIndBT` + structural rules.  Demote. |

Three genuine: `mp`, `ruleInst`, `ruleIndBT`.  One demoted: `ruleF`.

## Pruned count

- Combinator equations:       **21**
- Equality axioms:             **4**
- Propositional axioms:        **3**
- Inference rules:             **3**
- Total genuine primitives:   **31**

Down from 40.  Nine demoted:
`axRefl, ruleSym, ruleTrans, cong1, congL, congR, axNeg, axExFalso, ruleF`.
All nine are one-line Agda-level helpers using only genuine primitives.

## Implications for `thmT`

- 31 tags (not 40) for the proof-code alphabet.
- 31 dispatch branches in `ThmT.agda`.
- 31 cases in `encode`.
- 31 `Parts/<Name>.agda` files.
- 23% reduction in total `thmT` + `encode` size.

## Proposed next session ordering

1. Extract the 9 derivable primitives into a new `BRA/DerivDerived.agda`
   module, proving each as a one-line Agda function over the 31
   primitives that remain.  Re-export them with the same names so
   downstream proofs are unchanged.
2. In `BRA/Deriv.agda`, delete the 9 demoted constructors.  Rebuild
   the chain: `Cor.agda`, `Sub.agda`, `SubT.agda`, `Mp.agda`,
   `CodeCommutes.agda`, `Thm11Diagonal.agda`, `Thm11.agda`, adding
   `open import BRA.DerivDerived` where needed.
3. Verify fresh rebuild still under 1s total.
4. Begin `BRA/Thm/` scaffolding (Tag.agda, Common.agda, Parts/AxI.agda
   as prototype).

## Notes

- `axGoodstein` is worth double-checking before committing it as
  genuine: if the diagonal / `encode` work ever needs `TreeEq` to
  appear under a variable in a proof step, it is genuinely needed;
  otherwise it may be reducible to the other `TreeEq` axioms plus
  ruleIndBT.  Flagging for future audit, not touching now.

- `ruleF` deserves more attention.  It is stated with specific free
  variables (`zero`, `suc zero`); the derivation via `ruleIndBT`
  needs careful handling of fresh variables.  If the derivation turns
  out to be long, keeping `ruleF` as a primitive may be worth the
  tag cost.  Also flagging.
