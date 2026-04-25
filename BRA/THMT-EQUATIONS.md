# thmT equations needed by the abstract Thm 12-14 chain

Session date: 2026-04-25.  Branch: `main`.

This note inventories exactly which **parametric** defining equations
of `thmT` (i.e., Guard's Definition 12 of `th`, p.15 of guard15.pdf)
are needed by the abstract Goedel II chain.  The point is to localise
the gap left after `BRA/Sb.agda` + `BRA/SbAxiom.agda` were completed
and after the `parametric thmT-substitution dispatch` obstruction was
documented in `BRA/THM14-STEP4-OBSTRUCTION.md`.

The inventory is **architectural background for future sessions**.
It does NOT modify code; it sets up the next round of contract design.

## Background

Guard's `th` is introduced in Definition 12 by four PR equations:

  * `th(4y)   = ax(y)`                          -- axiom enumeration
  * `th(4y+1) = sb(KKy, IKy, th(Iy))`           -- substitution rule
  * `th(4y+2) = mp(th(Ky), th(Ly))`             -- modus ponens
  * `th(4y+3) = ind(th(Ky), th(Ly))`            -- induction

These hold parametrically in `y` (a free BRA term variable) in
Guard's reasoning -- he uses, e.g., line 2 with `y := J(J(num x, 1),
x)` parametric in `x` in step 4 of Thm 14.

In our Agda BRA, we have `thmT = Rec O stepProto` (in
`BRA/Thm/ThmT.agda`).  `thmT`'s defining equations are derivable for
**closed** input trees (via the IfLf/TreeEq dispatch), but not
parametrically for open Term variables.  Goedel I (Thm 11) only needs
closed-input behaviour and is unconditional.  Goedel II (Thm 14) step
4 and step 5 invoke Definition 12 parametrically -- this is where
our setup currently has a gap (see `BRA/THM14-STEP4-OBSTRUCTION.md`).

The plan is to **add those parametric equations as abstract
parameters** to `BRA/Thm14Abstract.agda`, mirroring how `encode`,
`thClosed`, `codeF1Th_noVar` are already abstract parameters.  The
question of how to **realise** them concretely (likely needing more
flexibility than `Rec`, e.g., the more-general function-definition
mechanisms Guard sketches around Exercise 11) is deferred.

## Which Definition 12 clauses each Thm 14 step uses

| Step | What it derives | Def 12 clause used |
|---|---|---|
| 1 | `th(x)=j ⊃ th(Dth(x))="th(x_)=j"`                   | none directly -- via Thm 13 (`encode`) |
| 2 | `th(Dsub(i,i))="sub(i,i)=j"` (closed)               | none directly -- via Thm 13 (`encode`) |
| 3 | `th(x)=j ⊃ th(g(x))="th(x_)=sub(i,i)"`              | none directly -- internal eq-trans on 1+2 |
| 4 | `th(x)=j ⊃ th(<sub-rule>(x))="th(x_)≠sub(i,i)"`     | **Line 2** (sb clause), parametric in `x` |
| 5 | `th(x)=j ⊃ th(<mp-rule>(x))="0=1"`                  | **Lines 2 and 3**: line 2 for the `h(x)` substitution, line 3 twice (inner mp at `gx,hx` and outer mp at step-4-witness, inner-mp-witness) |

So steps 1-3 are already discharged by the existing `encode`
parameter.  **The genuinely new contracts are only Definition 12
lines 2 and 3, parametric.**

## The minimal contract additions

Stated at the most general parametric level (= Guard's Definition 12
verbatim, parametric in `y`):

### Substitution rule (Def 12 line 2)

```
-- Definition 12 line 2 of thmT, parametric in (A, n_term, proof):
--   thmT(4·J(J(A, n_term), proof) + 1)  =  sb(A, n_term, thmT(proof))
--
-- where sb is BRA.Sb.sb (already built), parametrically in
-- (A : Term)        -- substituent code
-- (n_term : Term)   -- variable index code
-- (proof : Term)    -- antecedent proof tree

subRuleEnc : Term -> Term -> Term -> Term
   -- builds the BRA-term-level encoding of "4·J(J(A,n_term),proof)+1"
   -- (a closed-form construction from Pair / natCode constants).

axThmTSubRule :
  (A n_term proof : Term) ->
  Deriv (atomic (eqn (ap1 thmT (subRuleEnc A n_term proof))
                      (ap2 sb (ap2 Pair A n_term) (ap1 thmT proof))))
```

### Modus ponens rule (Def 12 line 3)

```
-- Definition 12 line 3 of thmT, parametric in (pAnt, pImp):
--   thmT(4·J(pAnt, pImp) + 2)  =  mp(thmT(pAnt), thmT(pImp))
-- where mp on codes:  mp("P", "P ⊃ Q")  =  "Q"  (Exercise 24 [1]).

mpRuleEnc : Term -> Term -> Term
   -- builds the BRA-term-level encoding of "4·J(pAnt,pImp)+2".

mp_codeF2 : Fun2
   -- BRA functor for mp on coded formulas.  By
   --   codeFormula(P imp Q) = nd tagImp (nd codeP codeQ)
   -- (BRA/Formula.agda line 79), mp-on-codes is just  Snd Snd  of
   -- the implication code.  Concretely:
   --
   --   mp_codeF2 = Post (Comp Snd Snd) (Post Snd Pair)
   --     -- ap2 mp_codeF2 a b = (Comp Snd Snd) (Snd (Pair a b))
   --     --                   = Snd (Snd b) = Q-code .
   --
   -- (Buildable from existing primitives, no axiom needed for
   -- mp_codeF2 itself -- only the axThmTMpRule below links it to thmT.)

axThmTMpRule :
  (pAnt pImp : Term) ->
  Deriv (atomic (eqn (ap1 thmT (mpRuleEnc pAnt pImp))
                      (ap2 mp_codeF2 (ap1 thmT pAnt) (ap1 thmT pImp))))
```

## Notable architectural points

1. **The parametric form matches Guard's Definition 12 verbatim.**
   No specialisation to step-4's particular `y := J(J(num x, 1), x)`
   instantiation; the contract is "thmT's defining equation, line 2,
   parametric in `y`" -- which is exactly how Guard introduces `th`.

2. **`mp_codeF2` is concretely buildable**, no axiom needed for it
   alone.  Only the link from `thmT` to it (`axThmTMpRule`) is
   axiom-shaped.

3. **The encodings `subRuleEnc` and `mpRuleEnc` are concretely
   buildable** from `Pair`, `cor` (numeral coding), `Const` /
   `natCode` constants.  They are ordinary BRA-term-level functions;
   the axiom-shaped content lives only in `axThmTSubRule` and
   `axThmTMpRule`.

4. **`sb` is already built** (`BRA/Sb.agda`) and `sbDef` reduces it
   on closed inputs.  `axThmTSubRule` is what *connects* `sb` to
   `thmT` parametrically; `BRA/SbAxiom.agda`'s `sbForOutRuleInst`
   then bridges to `outRuleInst` form for use in step 4 and 5.

5. **Steps 1-3 do not introduce new contracts.**  Existing `encode`
   covers them.  So Goedel II's abstract chain grows by exactly the
   two equations above (plus their construction parameters).

6. **Lines 1 and 4 of Definition 12 are not needed parametrically.**
   The `ax`-clause (line 1, axiom enumeration) and `ind`-clause
   (line 4, induction) are absorbed into `encode`'s closed-input
   coverage in `BRA/Thm/ThmT.agda` (which dispatches concretely on
   each tag).  If a future Thm-15+/-style result invokes them
   parametrically, they would need analogous contracts.

## Proposed next steps (deferred, not this session)

A subsequent session would:

  (a) Add `subRuleEnc`, `mpRuleEnc`, `mp_codeF2`, `axThmTSubRule`,
      `axThmTMpRule` as parameters of the `Thm14` module in
      `BRA/Thm14Abstract.agda`.

  (b) Define `constr5 : Fun1` in terms of the new constructions
      (combining step-4's sub-rule with step-5's nested mp-rules);
      build `step5` mechanically from `axThmTSubRule`,
      `axThmTMpRule`, `sbForOutRuleInst`, and existing
      `subIIeqcG`/`encode`.  This closes the abstract chain.

  (c) Defer the question of "how to programmatically realise a
      `thmT` satisfying `axThmTSubRule` + `axThmTMpRule`
      parametrically" to a separate design discussion.  This likely
      requires more general function-definition mechanisms than the
      current `Rec` (cf. Guard's exercises around Exercise 11), and
      is genuinely a research direction.

  (d) The concrete `BRA/Thm/ThmT.agda` + `thm11` (Goedel I) is
      preserved intact -- it does not depend on the new parametric
      contracts.

## Why this is the right framing

This separates two concerns cleanly:

  * **Goedel II's logical structure** = abstract over 5 contracts:
    `thmT`, `thClosed`, `codeF1Th_noVar`, `encode`, plus the new
    `axThmTSubRule` and `axThmTMpRule`.  This is mathematically
    Guard's Thm 14 argument, faithfully.

  * **The concrete realisation of `thmT`** with full Definition 12
    in parametric form = a separate question about BRA's PR
    function-definition machinery.

The first concern is fully formalisable in our Agda BRA without any
new postulates or new primitive axioms.  The second is open and
deferred.

The user's instinct here ("we first have to understand what are the
equations needed for `thmT`") is exactly right: this inventory is the
spec the future concrete `thmT` must satisfy.
