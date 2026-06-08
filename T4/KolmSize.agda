{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmSize -- the size accounting:  the Horner code is LINEAR in the number
-- of base-3 digits.  Combined with T4.KolmRun's  p < 3^(nodes+1)  this is the
-- logarithmic upper bound.
--
--   nodes_horner_bound :
--     AllLt3 ds -> NatLe (nodes (mcode1 (horner ds))) (addN baseN (repAdd PDmax (lenDL ds)))
--
-- i.e.  nodes (mcode1 (horner ds))  <=  baseN + PDmax * (number of digits) .

module T4.KolmSize where

open import T4.Base
open import BRA3.Code.Tag         using ( addN )
open import BRA3.Code.NatLemmas   using ( addN_suc_right )
open import BRA3.Code.CantorGrowth using ( addN_comm ; addN_assoc )
open import T4.TreeDigitsSize     using ( addN_suc2 ; addN_suc3 )
open import BRA3.RuleInst2         using ( NatLe ; le-zero ; le-suc ; le-refl
                                         ; le-suc-right ; le-trans
                                         ; maxN ; maxN-le-left ; maxN-le-right )
open import T4.ProgEnc            using ( nodes )
open import T4.EvalU             using ( mcode1 ; mcode2 )
open import T4.Tags              using ( tag_C )
open import T4.Exp3              using ( triple_F1 )
open import T4.KolmHorner        using ( DL ; dnil ; dcons ; horner ; addD )

------------------------------------------------------------------------
-- addN monotonicity (right argument).

le_addN_2nd : (c : Nat) {a b : Nat} -> NatLe a b -> NatLe (addN c a) (addN c b)
le_addN_2nd zero    h = h
le_addN_2nd (suc c) h = le-suc (le_addN_2nd c h)

le_addN_1st : {a b : Nat} (c : Nat) -> NatLe a b -> NatLe (addN a c) (addN b c)
le_addN_1st {a} {b} c h =
  -- addN c a = addN a c (comm) ; mono in 2nd ; rewrite both sides.
  eqSubst (\ z -> NatLe z (addN b c)) (addN_comm c a)
    (eqSubst (\ z -> NatLe (addN c a) z) (addN_comm c b)
      (le_addN_2nd c h))

------------------------------------------------------------------------
-- The per-compose constants (all left symbolic; Agda computes them).

T0 : Nat
T0 = nodes (natCode tag_C)

U0 : Nat
U0 = nodes (mcode1 u)

-- the lift-leg node count of the inner functor.
Lf : Fun1 -> Nat
Lf f = nodes (mcode2 (Lift1 f))

-- one compose layer, as a function of the sub-program node count m.
gnodes : Fun1 -> Nat -> Nat
gnodes f m = suc (addN T0 (suc (addN (Lf f) (suc (addN m U0)))))

-- the per-layer constant.
Wf : Fun1 -> Nat
Wf f = suc (suc (suc (addN T0 (addN (Lf f) U0))))

------------------------------------------------------------------------
-- nodes (mcode1 (compose1U f P)) = gnodes f (nodes (mcode1 P))   [definitional].
-- We re-express gnodes as  m + Wf f  (pull the sub-count out).

-- pull lemma:  suc (t + suc (l + suc (m + u))) = m + (3 + t + (l + u)) .
pull4 : (t l m uu : Nat) ->
  Eq (suc (addN t (suc (addN l (suc (addN m uu))))))
     (addN m (suc (suc (suc (addN t (addN l uu))))))
pull4 t l m uu =
  let -- LHS = suc (suc (suc (addN t (addN l (addN m uu)))))
      lInner : Eq (addN l (suc (addN m uu))) (suc (addN l (addN m uu)))
      lInner = addN_suc_right l (addN m uu)
      tStep : Eq (addN t (suc (addN l (suc (addN m uu)))))
                 (suc (suc (addN t (addN l (addN m uu)))))
      tStep = eqTrans (eqCong (\ z -> addN t z) (eqCong suc lInner))
                      (addN_suc2 t (addN l (addN m uu)))
      lhs : Eq (suc (addN t (suc (addN l (suc (addN m uu))))))
               (suc (suc (suc (addN t (addN l (addN m uu))))))
      lhs = eqCong suc tStep
      -- reorder:  addN t (addN l (addN m uu)) = addN m (addN t (addN l uu)) .
      -- step a:  addN l (addN m uu) = addN m (addN l uu)
      a1 : Eq (addN l (addN m uu)) (addN (addN l m) uu)
      a1 = eqSym (addN_assoc l m uu)
      a2 : Eq (addN (addN l m) uu) (addN (addN m l) uu)
      a2 = eqCong (\ z -> addN z uu) (addN_comm l m)
      a3 : Eq (addN (addN m l) uu) (addN m (addN l uu))
      a3 = addN_assoc m l uu
      lma : Eq (addN l (addN m uu)) (addN m (addN l uu))
      lma = eqTrans a1 (eqTrans a2 a3)
      -- step b: addN t (addN l (addN m uu)) = addN m (addN t (addN l uu))
      b1 : Eq (addN t (addN l (addN m uu))) (addN t (addN m (addN l uu)))
      b1 = eqCong (\ z -> addN t z) lma
      b2 : Eq (addN t (addN m (addN l uu))) (addN (addN t m) (addN l uu))
      b2 = eqSym (addN_assoc t m (addN l uu))
      b3 : Eq (addN (addN t m) (addN l uu)) (addN (addN m t) (addN l uu))
      b3 = eqCong (\ z -> addN z (addN l uu)) (addN_comm t m)
      b4 : Eq (addN (addN m t) (addN l uu)) (addN m (addN t (addN l uu)))
      b4 = addN_assoc m t (addN l uu)
      reorder : Eq (addN t (addN l (addN m uu))) (addN m (addN t (addN l uu)))
      reorder = eqTrans b1 (eqTrans b2 (eqTrans b3 b4))
      -- RHS = suc (suc (suc (addN m (addN t (addN l uu)))))
      rhs : Eq (addN m (suc (suc (suc (addN t (addN l uu))))))
               (suc (suc (suc (addN m (addN t (addN l uu))))))
      rhs = addN_suc3 m (addN t (addN l uu))
  in eqTrans lhs (eqTrans (eqCong (\ z -> suc (suc (suc z))) reorder) (eqSym rhs))

gnodes_eq : (f : Fun1) (m : Nat) -> Eq (gnodes f m) (addN m (Wf f))
gnodes_eq f m = pull4 T0 (Lf f) m U0

------------------------------------------------------------------------
-- The per-digit recurrence (uses the refl decomposition of nodes/mcode1).

-- nodes (mcode1 (horner (dcons d ds)))
--   = gnodes (addD d) (gnodes triple_F1 (nodes (mcode1 (horner ds))))   [refl]
nodes_cons_raw :
  (d : Nat) (ds : DL) ->
  Eq (nodes (mcode1 (horner (dcons d ds))))
     (gnodes (addD d) (gnodes triple_F1 (nodes (mcode1 (horner ds)))))
nodes_cons_raw d ds = refl

-- the per-digit cost.
perDigit : Nat -> Nat
perDigit d = addN (Wf triple_F1) (Wf (addD d))

nodes_cons :
  (d : Nat) (ds : DL) ->
  Eq (nodes (mcode1 (horner (dcons d ds))))
     (addN (nodes (mcode1 (horner ds))) (perDigit d))
nodes_cons d ds =
  let m : Nat
      m = nodes (mcode1 (horner ds))
      -- inner layer:  gnodes triple_F1 m = addN m (Wf triple_F1)
      inner : Eq (gnodes triple_F1 m) (addN m (Wf triple_F1))
      inner = gnodes_eq triple_F1 m
      -- outer layer:  gnodes (addD d) k = addN k (Wf (addD d))  at k = gnodes triple_F1 m
      outer : Eq (gnodes (addD d) (gnodes triple_F1 m))
                 (addN (gnodes triple_F1 m) (Wf (addD d)))
      outer = gnodes_eq (addD d) (gnodes triple_F1 m)
      -- substitute inner into outer's first addN argument.
      sub1 : Eq (addN (gnodes triple_F1 m) (Wf (addD d)))
                (addN (addN m (Wf triple_F1)) (Wf (addD d)))
      sub1 = eqCong (\ z -> addN z (Wf (addD d))) inner
      -- associate:  (m + Wf tri) + Wf(addD d) = m + (Wf tri + Wf(addD d)) = m + perDigit d
      assoc : Eq (addN (addN m (Wf triple_F1)) (Wf (addD d)))
                 (addN m (perDigit d))
      assoc = addN_assoc m (Wf triple_F1) (Wf (addD d))
  in eqTrans (nodes_cons_raw d ds) (eqTrans outer (eqTrans sub1 assoc))

------------------------------------------------------------------------
-- Digit-list length and the uniform per-digit bound (digits < 3).

lenDL : DL -> Nat
lenDL dnil        = zero
lenDL (dcons _ ds) = suc (lenDL ds)

-- all digits < 3 (the digits produced by mod3).
data AllLt3 : DL -> Set where
  allNil  : AllLt3 dnil
  allCons : {d : Nat} {ds : DL} -> NatLe d (suc (suc zero)) -> AllLt3 ds -> AllLt3 (dcons d ds)

-- the uniform per-digit bound.
PDmax : Nat
PDmax = maxN (perDigit zero) (maxN (perDigit (suc zero)) (perDigit (suc (suc zero))))

perDigit_le : (d : Nat) -> NatLe d (suc (suc zero)) -> NatLe (perDigit d) PDmax
perDigit_le zero                   _ =
  maxN-le-left (perDigit zero) (maxN (perDigit (suc zero)) (perDigit (suc (suc zero))))
perDigit_le (suc zero)             _ =
  le-trans (maxN-le-left (perDigit (suc zero)) (perDigit (suc (suc zero))))
           (maxN-le-right (perDigit zero) (maxN (perDigit (suc zero)) (perDigit (suc (suc zero)))))
perDigit_le (suc (suc zero))       _ =
  le-trans (maxN-le-right (perDigit (suc zero)) (perDigit (suc (suc zero))))
           (maxN-le-right (perDigit zero) (maxN (perDigit (suc zero)) (perDigit (suc (suc zero)))))
perDigit_le (suc (suc (suc d)))    (le-suc (le-suc ()))

------------------------------------------------------------------------
-- repeated addition (PDmax * n) and the base node count.

repAdd : Nat -> Nat -> Nat
repAdd k zero    = zero
repAdd k (suc n) = addN k (repAdd k n)

baseN : Nat
baseN = nodes (mcode1 (horner dnil))

------------------------------------------------------------------------
-- The linear bound.

nodes_horner_bound :
  (ds : DL) -> AllLt3 ds ->
  NatLe (nodes (mcode1 (horner ds))) (addN baseN (repAdd PDmax (lenDL ds)))
nodes_horner_bound dnil        allNil =
  -- nodes (mcode1 (horner dnil)) = baseN <= addN baseN 0 = baseN
  eqSubst (\ z -> NatLe baseN z) (eqSym (addN_comm zero baseN)) (le-refl baseN)
nodes_horner_bound (dcons d ds) (allCons dle dsOk) =
  let m : Nat
      m = nodes (mcode1 (horner ds))
      ih : NatLe m (addN baseN (repAdd PDmax (lenDL ds)))
      ih = nodes_horner_bound ds dsOk
      -- nodes (cons) = addN m (perDigit d) = addN (perDigit d) m  (we bound via comm)
      step_eq : Eq (nodes (mcode1 (horner (dcons d ds)))) (addN m (perDigit d))
      step_eq = nodes_cons d ds
      -- bound:  addN m (perDigit d) <= addN (addN baseN (repAdd PDmax (lenDL ds))) PDmax
      b1 : NatLe (addN m (perDigit d))
                 (addN (addN baseN (repAdd PDmax (lenDL ds))) (perDigit d))
      b1 = le_addN_1st (perDigit d) ih
      b2 : NatLe (addN (addN baseN (repAdd PDmax (lenDL ds))) (perDigit d))
                 (addN (addN baseN (repAdd PDmax (lenDL ds))) PDmax)
      b2 = le_addN_2nd (addN baseN (repAdd PDmax (lenDL ds))) (perDigit_le d dle)
      -- target RHS = addN baseN (repAdd PDmax (suc (lenDL ds)))
      --            = addN baseN (addN PDmax (repAdd PDmax (lenDL ds)))
      -- reassociate the bound to match.
      reassoc : Eq (addN (addN baseN (repAdd PDmax (lenDL ds))) PDmax)
                   (addN baseN (addN PDmax (repAdd PDmax (lenDL ds))))
      reassoc =
        eqTrans (addN_assoc baseN (repAdd PDmax (lenDL ds)) PDmax)
                (eqCong (\ z -> addN baseN z) (addN_comm (repAdd PDmax (lenDL ds)) PDmax))
      chain : NatLe (nodes (mcode1 (horner (dcons d ds))))
                    (addN baseN (addN PDmax (repAdd PDmax (lenDL ds))))
      chain = eqSubst (\ z -> NatLe (nodes (mcode1 (horner (dcons d ds)))) z)
                (eqTrans reassoc refl)
                (eqSubst (\ z -> NatLe z (addN (addN baseN (repAdd PDmax (lenDL ds))) PDmax))
                   (eqSym step_eq)
                   (le-trans b1 b2))
  in chain
