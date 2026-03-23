# Next session prompt

Read GUARD-STATUS.md for context. The goal is to eliminate axRepMPG2
from GuardFull.agda by writing the ~40-line equational D2 derivation.

```text
Read GUARD-STATUS.md, then read GuardFull.agda (focus on Sections 3, 5, 8).

Goal:
Eliminate axRepMPG2 by deriving D2 internally from computation axioms.

Context:
- GuardFull.agda has exIntroTmG2 (term witnesses), congruence layer
  (axCongCaseG2, axCongFoldG2, axCongIfG2), and Hilbert helpers
  (transG2, symG2, congFoldG2, congCaseG2, congNodeBothG2, exElimImpG2).
- D2 = Prov(A->B) -> Prov(A) -> Prov(B) where
  Prov(X) = fexTA3 (feqTA3 checkCG2 (liftCode (encFormTA3 X))).
- The mp witness term is:
  ctNode (ctAtom tagMP3) (ctNode (ctVar (suc zero)) (ctVar zero))
  (var 1 = c1 from first universal, var 0 = c2 from second universal)

Tasks:
1. Write d2G2-inner: the equational proof that the checker applied to
   the mp witness gives enc(B), given hypotheses for c1 and c2.

   The derivation chain (see GUARD-STATUS.md for details):
   a. axFoldNode on the mp witness
   b. axCaseNodeL on the outer ctCase
   c. Tag dispatch for tagMP3 (axClosedEq for comparisons)
   d. hMP on fold(payload) = cnode(checker(c1), checker(c2))
   e. congNodeBothG2 + hypotheses -> cnode(enc(A->B), enc(A))
   f. axClosedEq for matchMP -> enc(B)
   g. Chain with transG2

2. Wrap d2G2-inner with genG2 + exElimImpG2 to build the full D2.

3. Replace d2G2 to use the derivation instead of axRepMPG2.

4. If successful, do the same for axRepD3G2 (derive D3).

5. If both succeed, remove axRepMPG2 and axRepD3G2 from ProofG2.

Constraints:
- no new axioms
- no semantic shortcuts
- zero postulates
- zero holes

If blocked, report:
- the exact step in the chain that fails
- the exact missing lemma in Agda type form
```

After D2 and D3 are derived, the only remaining representability
constructors are axGodelLeftG2/axGodelRightG2 (the diagonal). These
are harder to eliminate (they require representable internal
substitution = Guard's Exercise 24 item [8]). That would be a
separate follow-up session.
