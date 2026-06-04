{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StageBaseFN -- the number-code BASE CASE  S(0)  of surprise-GII's external
-- induction ( clos lines 11-19, 71-73 ;  SURPRISE-GII-NUMBERCODE-HANDOFF S3.6 ).
--
--   stageBaseFN : (N M : Nat) -> Lt M N -> StagePredFN N M zero
--
-- Number-code mirror of  T4.SurpriseG2.StageBaseFormula  with the describe atom
-- re-pointed to  runProgN  and the program slot the NUMBER  natCode (picks i)
-- ( enum = identity ).
--
-- PROOF ( clos line 20 ) :  pigeonhole on  picks  over the  N+1  days  [0..N]
-- into the  M+1 < N+1  program slots gives colliding days  i /= j  with
-- picks i = picks j .   Project the day-i and day-j conjuncts from the
-- hypothetical big conjunction ;  both say  runProgN (natCode (picks i)) (var 0)
-- equals  s (natCode i)  resp.  s (natCode j) ;   transitivity + s-injectivity +
-- numNeq  give  falseF  under the hypothesis ;   impFalseToNeg  closes  neg .

open import T4.Base
open import BRA3.RuleInst2          using ( NatLe ; le-zero ; le-suc )
open import BRA3.Logic              using ( impTrans ; eqSymImp ; prependEqLeft
                                          ; appendEqRight )
open import BRA3.Contrapositive
  using ( liftP ; bComb ; bCombTwo ; axExFalso )
open import BRA3.Church             using ( predecessor ; T_p_S_v0 )
open import T4.ParseN               using ( runProgN )
open import T4.Code                 using ( falseF )
open import T4.PHP                  using ( impFalseToNeg )
open import T4.SurpriseG2.BigConjFormula using ( conjF ; trueF ; countDays )
open import T4.SurpriseG2.AndLemmas using ( fstAndImp ; sndAndImp )
open import T4.SurpriseG2.NumNeq    using ( Not ; numNeq )
open import T4.SurpriseG2.MetaPigeonhole as MP
  using ( Lt ; Collide ; pigeonhole )
open import T4.StagePredFN
  using ( describeAtN ; bigConjCountN ; openFuel ; BigConjFormulaN
        ; StagePredFN ; Picks ; PicksBound )

module T4.StageBaseFN where

------------------------------------------------------------------------
-- addO  helper ( verbatim from StageBaseFormula ) .

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
-- NatLe <-> Lt conversions ( verbatim from StageBaseFormula ) .

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
-- Project the  offset -th conjunct from  bigConjCountN count start picks openFuel .

projectConjFN :
  (count : Nat) (start : Nat) (picks : Picks) (offset : Nat) ->
  Lt offset count ->
  Deriv (imp (bigConjCountN count start picks openFuel)
              (describeAtN (picks (addO start offset)) (addO start offset) (var zero)))
projectConjFN (suc c) start picks zero    lt =
  fstAndImp (describeAtN (picks start) start (var zero))
            (bigConjCountN c (suc start) picks openFuel)
projectConjFN (suc c) start picks (suc ofs) lt =
  let lt' : Lt ofs c
      lt' = MP.ltPred lt
      skip : Deriv (imp (bigConjCountN (suc c) start picks openFuel)
                         (bigConjCountN c (suc start) picks openFuel))
      skip = sndAndImp (describeAtN (picks start) start (var zero))
                       (bigConjCountN c (suc start) picks openFuel)
      ih : Deriv (imp (bigConjCountN c (suc start) picks openFuel)
                       (describeAtN (picks (addO (suc start) ofs)) (addO (suc start) ofs) (var zero)))
      ih = projectConjFN c (suc start) picks ofs lt'
      bridge : Eq (addO (suc start) ofs) (addO start (suc ofs))
      bridge = addO_suc_left start ofs
      composed : Deriv (imp (bigConjCountN (suc c) start picks openFuel)
                             (describeAtN (picks (addO (suc start) ofs)) (addO (suc start) ofs) (var zero)))
      composed = impTrans skip ih
  in eqSubst (\ z -> Deriv (imp (bigConjCountN (suc c) start picks openFuel)
                                 (describeAtN (picks z) z (var zero))))
             bridge
             composed

------------------------------------------------------------------------
-- s_injImp  ( verbatim from StageBaseFormula ) .

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
-- twoFalseImpN :  same program (NUMBER), same fuel, two DIFFERENT days give falseF .

twoFalseImpN :
  (p : Term) (i j : Nat) -> Not (Eq i j) ->
  Deriv (imp (eqF (ap2 runProgN p (var zero)) (ap1 s (natCode i)))
              (imp (eqF (ap2 runProgN p (var zero)) (ap1 s (natCode j))) falseF))
twoFalseImpN p i j i_neq_j =
  let rpv0 : Term
      rpv0 = ap2 runProgN p (var zero)
      nci : Term
      nci = natCode i
      ncj : Term
      ncj = natCode j
      combine1 : Deriv (imp (eqF rpv0 (ap1 s nci))
                             (imp (eqF rpv0 (ap1 s ncj))
                                   (eqF (ap1 s nci) (ap1 s ncj))))
      combine1 = ax_eqTrans rpv0 (ap1 s nci) (ap1 s ncj)
      sinj_step : Deriv (imp (eqF (ap1 s nci) (ap1 s ncj)) (eqF nci ncj))
      sinj_step = s_injImp nci ncj
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
      numNeq_d : Deriv (neg (eqF nci ncj))
      numNeq_d = numNeq i j i_neq_j
      exf : Deriv (imp (eqF nci ncj) (imp (neg (eqF nci ncj)) falseF))
      exf = axExFalso (eqF nci ncj) falseF
      lifted_numNeq : Deriv (imp (eqF nci ncj) (neg (eqF nci ncj)))
      lifted_numNeq = liftP (eqF nci ncj) numNeq_d
      step4 : Deriv (imp (eqF nci ncj) falseF)
      step4 = bComb exf lifted_numNeq
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
-- The BASE CASE  S(0) .

stageBaseFN :
  (N M : Nat) -> Lt M N -> StagePredFN N M zero
stageBaseFN N M ltMN picks bound =
  let bound_lt : (i : Nat) -> Lt i (suc N) -> Lt (picks i) (suc M)
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

      BigConj0 : Formula
      BigConj0 = BigConjFormulaN N zero picks

      proj_i_raw : Deriv (imp BigConj0
                               (describeAtN (picks (addO zero i)) (addO zero i) (var zero)))
      proj_i_raw = projectConjFN (suc N) zero picks i i_lt_sN

      proj_i : Deriv (imp BigConj0 (describeAtN (picks i) i (var zero)))
      proj_i = eqSubst
        (\ z -> Deriv (imp BigConj0 (describeAtN (picks z) z (var zero))))
        (addO_zero_left i) proj_i_raw

      proj_j_raw : Deriv (imp BigConj0
                               (describeAtN (picks (addO zero j)) (addO zero j) (var zero)))
      proj_j_raw = projectConjFN (suc N) zero picks j j_lt_sN

      proj_j : Deriv (imp BigConj0 (describeAtN (picks j) j (var zero)))
      proj_j = eqSubst
        (\ z -> Deriv (imp BigConj0 (describeAtN (picks z) z (var zero))))
        (addO_zero_left j) proj_j_raw

      -- The program at slot picks i ( = picks j by collision ), the NUMBER itself .
      progT : Term
      progT = natCode (picks i)

      -- Align proj_j to use natCode (picks i) instead of natCode (picks j) .
      proj_j_aligned :
        Deriv (imp BigConj0
                    (eqF (ap2 runProgN progT (var zero)) (ap1 s (natCode j))))
      proj_j_aligned = eqSubst
        (\ z -> Deriv (imp BigConj0
                            (eqF (ap2 runProgN (natCode z) (var zero))
                                  (ap1 s (natCode j)))))
        (eqSym picks_eq) proj_j

      twoFalse : Deriv (imp (eqF (ap2 runProgN progT (var zero)) (ap1 s (natCode i)))
                             (imp (eqF (ap2 runProgN progT (var zero)) (ap1 s (natCode j)))
                                   falseF))
      twoFalse = twoFalseImpN progT i j i_neq_j

      lifted_twoFalse :
        Deriv (imp BigConj0
                    (imp (eqF (ap2 runProgN progT (var zero)) (ap1 s (natCode i)))
                          (imp (eqF (ap2 runProgN progT (var zero)) (ap1 s (natCode j)))
                                falseF)))
      lifted_twoFalse = liftP BigConj0 twoFalse

      step5 :
        Deriv (imp BigConj0
                    (imp (eqF (ap2 runProgN progT (var zero)) (ap1 s (natCode j)))
                          falseF))
      step5 = bComb lifted_twoFalse proj_i

      step6 : Deriv (imp BigConj0 falseF)
      step6 = bComb step5 proj_j_aligned
  in impFalseToNeg BigConj0 step6
