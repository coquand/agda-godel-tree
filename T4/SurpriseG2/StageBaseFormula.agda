{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageBaseFormula --
--
-- The BASE CASE  S(0)  of the EXTERNAL induction , in the FORMULA-LEVEL
-- per T4/clos lines 11-19 and
-- [[feedback_no_meta_to_imp_primitive_needed]] :
--
--   stageBaseF :
--     (consts : SurpriseConstsConj) ->
--     Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
--     StagePredF consts zero
--
-- Output : `(picks : Picks) (bound : PicksBound consts picks) ->
--           Deriv (neg (BigConjFormula consts zero picks))` .
--
-- =====================================================================
-- PROOF STRUCTURE.
-- =====================================================================
--
-- Pigeonhole on `picks` restricted to [0..N] gives colliding days  i, j
-- with  picks i = picks j  and  i ≠ j .   Project the conjuncts at days
-- i  and  j  from the hypothetical  BigConj  via repeated  fstAndImp /
-- sndAndImp ;  align their programs via congruence on  picks i = picks j ;
-- combine via lifted  ax_eqTrans + eqSymImp  to derive
-- `eqF (s natCode i) (s natCode j)` under the hypothesis ;  apply
-- lifted  s_injImp  +  numNeq  +  axExFalso  to derive falseF under the
-- hypothesis ;  impFalseToNeg  closes the Deriv .

module T4.SurpriseG2.StageBaseFormula where

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; le-zero ; le-suc )
open import BRA3.Logic              using ( impTrans ; eqSymImp ; prependEqLeft
                                          ; appendEqRight )
open import BRA3.Contrapositive
  using ( liftP ; bComb ; bCombTwo ; axContrapos ; axExFalso ; identP )
open import BRA3.Church             using ( predecessor ; T_p_S_v0 )
open import T4.Code               using ( falseF )
open import T4.Kdef               using ( runProg )
open import T4.PHP                using ( impFalseToNeg )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.BigConjFormula
  using ( BigConjFormula ; bigConjCount ; conjF ; trueF ; describeAt
        ; countDays ; countAux )
open import T4.SurpriseG2.AndLemmas
  using ( fstAndImp ; sndAndImp )
open import T4.SurpriseG2.StagePredFormula
  using ( StagePredF ; Picks ; PicksBound )
open import T4.SurpriseG2.NumNeq     using ( Not ; numNeq )
open import T4.SurpriseG2.MetaPigeonhole as MP
  using ( Lt ; Collide ; pigeonhole )

------------------------------------------------------------------------
-- Helper :  addO  function and bridge lemma .

addO : Nat -> Nat -> Nat
addO start zero    = start
addO start (suc ofs) = suc (addO start ofs)

addO_zero_left : (i : Nat) -> Eq (addO zero i) i
addO_zero_left zero    = refl
addO_zero_left (suc ofs) = eqCong suc (addO_zero_left ofs)

addO_suc_left : (start o : Nat) -> Eq (addO (suc start) o) (suc (addO start o))
addO_suc_left start zero    = refl
addO_suc_left start (suc ofs) = eqCong suc (addO_suc_left start ofs)

------------------------------------------------------------------------
-- NatLe <-> Lt conversions  ( same as in OLD StageBase ) .

natLe_to_lt : (n m : Nat) -> NatLe m n -> Lt m (suc n)
natLe_to_lt n .zero (le-zero .n) = MP.ltZ n
natLe_to_lt (suc n') (suc m') (le-suc le') =
  MP.ltS m' (suc n') (natLe_to_lt n' m' le')

lt_to_natLe : (a b : Nat) -> Lt a (suc b) -> NatLe a b
lt_to_natLe zero    b     (MP.ltZ .b)              = le-zero b
lt_to_natLe (suc a) zero  (MP.ltS .a .zero h)      = MP.ltAbsurd h
lt_to_natLe (suc a) (suc b') (MP.ltS .a .(suc b') h) =
  le-suc (lt_to_natLe a b' h)

------------------------------------------------------------------------
-- Project the  offset -th conjunct from  bigConjCount enum count start picks .

projectConjF :
  (enum : Fun1) (count : Nat) (start : Nat) (picks : Picks) (offset : Nat) ->
  Lt offset count ->
  Deriv (imp (bigConjCount enum count start picks)
              (describeAt enum (picks (addO start offset)) (addO start offset)))
projectConjF enum (suc c) start picks zero    lt =
  fstAndImp (describeAt enum (picks start) start)
            (bigConjCount enum c (suc start) picks)
projectConjF enum (suc c) start picks (suc ofs) lt =
  let lt' : Lt ofs c
      lt' = MP.ltPred lt
      skip : Deriv (imp (bigConjCount enum (suc c) start picks)
                         (bigConjCount enum c (suc start) picks))
      skip = sndAndImp (describeAt enum (picks start) start)
                       (bigConjCount enum c (suc start) picks)
      ih : Deriv (imp (bigConjCount enum c (suc start) picks)
                       (describeAt enum (picks (addO (suc start) ofs)) (addO (suc start) ofs)))
      ih = projectConjF enum c (suc start) picks ofs lt'
      bridge : Eq (addO (suc start) ofs) (addO start (suc ofs))
      bridge = addO_suc_left start ofs
      composed : Deriv (imp (bigConjCount enum (suc c) start picks)
                             (describeAt enum (picks (addO (suc start) ofs))
                                          (addO (suc start) ofs)))
      composed = impTrans skip ih
  in eqSubst (\ z -> Deriv (imp (bigConjCount enum (suc c) start picks)
                                 (describeAt enum (picks z) z)))
             bridge
             composed

------------------------------------------------------------------------
-- s_injImp :  imp (eqF (s a) (s b)) (eqF a b)  via predecessor congruence .

s_injImp : (a b : Term) -> Deriv (imp (eqF (ap1 s a) (ap1 s b)) (eqF a b))
s_injImp a b =
  let cong_step : Deriv (imp (eqF (ap1 s a) (ap1 s b))
                              (eqF (ap1 predecessor (ap1 s a))
                                    (ap1 predecessor (ap1 s b))))
      cong_step = ax_eqCong1 predecessor (ap1 s a) (ap1 s b)

      pSa_eq_a : Deriv (eqF (ap1 predecessor (ap1 s a)) a)
      pSa_eq_a = ruleInst 0 a T_p_S_v0

      pSb_eq_b : Deriv (eqF (ap1 predecessor (ap1 s b)) b)
      pSb_eq_b = ruleInst 0 b T_p_S_v0

      prepend : Deriv (imp (eqF (ap1 predecessor (ap1 s a)) (ap1 predecessor (ap1 s b)))
                            (eqF a (ap1 predecessor (ap1 s b))))
      prepend = prependEqLeft a (ap1 predecessor (ap1 s a)) (ap1 predecessor (ap1 s b))
                              (ruleSym pSa_eq_a)

      append : Deriv (imp (eqF a (ap1 predecessor (ap1 s b))) (eqF a b))
      append = appendEqRight a (ap1 predecessor (ap1 s b)) b pSb_eq_b
  in impTrans cong_step (impTrans prepend append)

------------------------------------------------------------------------
-- twoFalseImp :  two describes ( same program , same fuel , different days )
-- give falseF .   The "contradiction from same-program-different-days" lemma
-- in formula-level imp form .

twoFalseImp :
  (p : Term) (i j : Nat) -> Not (Eq i j) ->
  Deriv (imp (eqF (ap2 runProg p (var zero)) (ap1 s (natCode i)))
              (imp (eqF (ap2 runProg p (var zero)) (ap1 s (natCode j))) falseF))
twoFalseImp p i j i_neq_j =
  let rpv0 : Term
      rpv0 = ap2 runProg p (var zero)

      nci : Term
      nci = natCode i

      ncj : Term
      ncj = natCode j

      -- Step 1 : imp (rpv0 = s nci) (imp (rpv0 = s ncj) (s nci = s ncj))
      -- ax_eqTrans x y z : imp (x=y) (imp (x=z) (y=z)).   Apply at
      -- x := rpv0, y := s nci, z := s ncj : DIRECT match .
      combine1 : Deriv (imp (eqF rpv0 (ap1 s nci))
                             (imp (eqF rpv0 (ap1 s ncj))
                                   (eqF (ap1 s nci) (ap1 s ncj))))
      combine1 = ax_eqTrans rpv0 (ap1 s nci) (ap1 s ncj)

      -- Step 2 : imp (s nci = s ncj) (nci = ncj) .
      sinj_step : Deriv (imp (eqF (ap1 s nci) (ap1 s ncj)) (eqF nci ncj))
      sinj_step = s_injImp nci ncj

      -- Compose Step 1's inner imp with Step 2 .
      lifted_sinj :
        Deriv (imp (eqF rpv0 (ap1 s nci))
                    (imp (eqF rpv0 (ap1 s ncj))
                          (imp (eqF (ap1 s nci) (ap1 s ncj)) (eqF nci ncj))))
      lifted_sinj = liftP (eqF rpv0 (ap1 s nci))
                          (liftP (eqF rpv0 (ap1 s ncj)) sinj_step)

      step3 : Deriv (imp (eqF rpv0 (ap1 s nci))
                          (imp (eqF rpv0 (ap1 s ncj)) (eqF nci ncj)))
      step3 = bCombTwo {eqF rpv0 (ap1 s nci)} {eqF rpv0 (ap1 s ncj)}
                        {eqF (ap1 s nci) (ap1 s ncj)} {eqF nci ncj}
                        lifted_sinj combine1

      -- Step 4 : numNeq + axExFalso → imp (nci = ncj) falseF .
      numNeq_d : Deriv (neg (eqF nci ncj))
      numNeq_d = numNeq i j i_neq_j

      exf : Deriv (imp (eqF nci ncj) (imp (neg (eqF nci ncj)) falseF))
      exf = axExFalso (eqF nci ncj) falseF

      lifted_numNeq : Deriv (imp (eqF nci ncj) (neg (eqF nci ncj)))
      lifted_numNeq = liftP (eqF nci ncj) numNeq_d

      step4 : Deriv (imp (eqF nci ncj) falseF)
      step4 = bComb exf lifted_numNeq

      -- Compose step3 + step4 .
      lifted_step4 :
        Deriv (imp (eqF rpv0 (ap1 s nci))
                    (imp (eqF rpv0 (ap1 s ncj))
                          (imp (eqF nci ncj) falseF)))
      lifted_step4 = liftP (eqF rpv0 (ap1 s nci))
                           (liftP (eqF rpv0 (ap1 s ncj)) step4)

      final : Deriv (imp (eqF rpv0 (ap1 s nci))
                          (imp (eqF rpv0 (ap1 s ncj)) falseF))
      final = bCombTwo {eqF rpv0 (ap1 s nci)} {eqF rpv0 (ap1 s ncj)}
                        {eqF nci ncj} {falseF}
                        lifted_step4 step3
  in final

------------------------------------------------------------------------
-- The BASE CASE  S(0)  in FORMULA-LEVEL form .

stageBaseF :
  (consts : SurpriseConstsConj) ->
  Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
  StagePredF consts zero
stageBaseF consts ltMN picks bound =
  let N : Nat
      N = SurpriseConstsConj.N consts
      M : Nat
      M = SurpriseConstsConj.M consts
      enum : Fun1
      enum = SurpriseConstsConj.enum consts

      -- Convert NatLe-bound to Lt-bound for pigeonhole .
      bound_lt : (i : Nat) -> Lt i (suc N) -> Lt (picks i) (suc M)
      bound_lt i lt_i_sN =
        natLe_to_lt M (picks i) (bound i (lt_to_natLe i N lt_i_sN))

      coll : Collide picks N
      coll = pigeonhole picks N M bound_lt ltMN

      i : Nat
      i = Collide.i_idx coll
      j : Nat
      j = Collide.j_idx coll
      i_lt_sN : Lt i (suc N)
      i_lt_sN = Collide.i_lt coll
      j_lt_sN : Lt j (suc N)
      j_lt_sN = Collide.j_lt coll
      i_neq_j : Not (Eq i j)
      i_neq_j = Collide.i_neq coll
      picks_eq : Eq (picks i) (picks j)
      picks_eq = Collide.ix_eq coll

      -- BigConj at r=0 = bigConjCount enum (suc N) 0 picks .
      BigConj0 : Formula
      BigConj0 = BigConjFormula consts zero picks

      -- Project conjunct at day i .
      proj_i_raw : Deriv (imp BigConj0
                               (describeAt enum (picks (addO zero i)) (addO zero i)))
      proj_i_raw = projectConjF enum (suc N) zero picks i i_lt_sN

      proj_i : Deriv (imp BigConj0 (describeAt enum (picks i) i))
      proj_i = eqSubst
        (\ z -> Deriv (imp BigConj0 (describeAt enum (picks z) z)))
        (addO_zero_left i) proj_i_raw

      -- Project conjunct at day j .
      proj_j_raw : Deriv (imp BigConj0
                               (describeAt enum (picks (addO zero j)) (addO zero j)))
      proj_j_raw = projectConjF enum (suc N) zero picks j j_lt_sN

      proj_j : Deriv (imp BigConj0 (describeAt enum (picks j) j))
      proj_j = eqSubst
        (\ z -> Deriv (imp BigConj0 (describeAt enum (picks z) z)))
        (addO_zero_left j) proj_j_raw

      -- The program at slot picks i ( = picks j by collision ) .
      progT : Term
      progT = ap1 enum (natCode (picks i))

      -- Align proj_j to use progT ( i.e., natCode (picks i) ) instead of natCode (picks j) .
      proj_j_aligned :
        Deriv (imp BigConj0
                    (eqF (ap2 runProg progT (var zero)) (ap1 s (natCode j))))
      proj_j_aligned = eqSubst
        (\ z -> Deriv (imp BigConj0
                            (eqF (ap2 runProg (ap1 enum (natCode z)) (var zero))
                                  (ap1 s (natCode j)))))
        (eqSym picks_eq) proj_j

      -- The contradiction lemma at progT .
      twoFalse : Deriv (imp (eqF (ap2 runProg progT (var zero)) (ap1 s (natCode i)))
                             (imp (eqF (ap2 runProg progT (var zero)) (ap1 s (natCode j)))
                                   falseF))
      twoFalse = twoFalseImp progT i j i_neq_j

      lifted_twoFalse :
        Deriv (imp BigConj0
                    (imp (eqF (ap2 runProg progT (var zero)) (ap1 s (natCode i)))
                          (imp (eqF (ap2 runProg progT (var zero)) (ap1 s (natCode j)))
                                falseF)))
      lifted_twoFalse = liftP BigConj0 twoFalse

      step5 :
        Deriv (imp BigConj0
                    (imp (eqF (ap2 runProg progT (var zero)) (ap1 s (natCode j)))
                          falseF))
      step5 = bComb lifted_twoFalse proj_i

      step6 : Deriv (imp BigConj0 falseF)
      step6 = bComb step5 proj_j_aligned
  in impFalseToNeg BigConj0 step6
