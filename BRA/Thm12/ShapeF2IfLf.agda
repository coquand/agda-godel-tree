{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm12.ShapeF2IfLf -- universal Fst-shape lemma for D_IfLf.
--
-- Mirrors BRA.Thm12.Parts.IfLf.D_correct2_IfLf_univ structure: 4 leaf
-- shape proofs (LL, LN, NL, NN), inner ruleIndBT on v at fixed x = O
-- and at fixed x = Pair _ _, outer ruleIndBT on x.  Each leaf uses
-- the pair_eta trick on the concrete parEncAxIfLf* result.

module BRA.Thm12.ShapeF2IfLf where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv

open import BRA.Thm.ThmT using (thmT)
open import BRA.Thm12.Parts.IfLf
  using ( D_IfLf
        ; D_IfLf_reduce_OO
        ; D_IfLf_reduce_LN
        ; D_IfLf_reduce_NL
        ; D_IfLf_reduce_NN )
open import BRA.Thm12.Param.AxIfLfL  using (parEncAxIfLfL)
open import BRA.Thm12.Param.AxIfLfN  using (parEncAxIfLfN)
open import BRA.Thm12.Param.AxIfLfLL using (parEncAxIfLfLL)
open import BRA.Thm12.Param.AxIfLfNL using (parEncAxIfLfNL)
open import BRA.Cor using (cor)

------------------------------------------------------------------------
-- Generic Pair-eta.

private
  pair_eta : (a b : Term) ->
    Deriv (atomic (eqn (ap2 Pair a b)
                       (ap2 Pair (ap1 Fst (ap2 Pair a b))
                                 (ap1 Snd (ap2 Pair a b)))))
  pair_eta a b =
    let
      fstEq : Deriv (atomic (eqn (ap1 Fst (ap2 Pair a b)) a))
      fstEq = axFst a b
      sndEq : Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
      sndEq = axSnd a b
      step1 : Deriv (atomic (eqn (ap2 Pair a b)
                                 (ap2 Pair (ap1 Fst (ap2 Pair a b)) b)))
      step1 = congL Pair b (ruleSym fstEq)
      step2 : Deriv (atomic (eqn (ap2 Pair (ap1 Fst (ap2 Pair a b)) b)
                                 (ap2 Pair (ap1 Fst (ap2 Pair a b))
                                           (ap1 Snd (ap2 Pair a b)))))
      step2 = congR Pair (ap1 Fst (ap2 Pair a b)) (ruleSym sndEq)
    in ruleTrans step1 step2

------------------------------------------------------------------------
-- The shape formula at universal var 0 (= x) and var 1 (= v).

P_shape_IfLf : Formula
P_shape_IfLf =
  atomic (eqn (ap1 Fst (ap2 D_IfLf (var zero) (var (suc zero))))
              (ap2 Pair
                (ap1 Fst (ap1 Fst (ap2 D_IfLf (var zero) (var (suc zero)))))
                (ap1 Snd (ap1 Fst (ap2 D_IfLf (var zero) (var (suc zero)))))))

------------------------------------------------------------------------
-- Generic leaf-case lifter.
--
-- Given:  ap2 D_IfLf X V = parEnc...     (the reduce lemma at the leaf)
-- where parEnc... has the form  ap2 Pair tag <body>  with tag itself
-- definitionally Pair O <inner> (positive natCode reify),
-- derive  ap1 Fst (ap2 D_IfLf X V)  =  Pair (Fst ...) (Snd ...)  via pair_eta.

private
  leaf_shape :
    (X V : Term) (parEnc : Term) ->
    Deriv (atomic (eqn (ap2 D_IfLf X V) parEnc)) ->
    -- Witness that parEnc is Pair-shaped: parEnc = Pair pTag pBody.
    (pTag pBody : Term) ->
    Deriv (atomic (eqn parEnc (ap2 Pair pTag pBody))) ->
    -- And pTag is Pair-shaped: pTag = Pair tA tB.
    (tA tB : Term) ->
    Deriv (atomic (eqn pTag (ap2 Pair tA tB))) ->
    Deriv (atomic
      (eqn (ap1 Fst (ap2 D_IfLf X V))
           (ap2 Pair
             (ap1 Fst (ap1 Fst (ap2 D_IfLf X V)))
             (ap1 Snd (ap1 Fst (ap2 D_IfLf X V))))))
  leaf_shape X V parEnc reduce pTag pBody parEncIsPair tA tB pTagIsPair =
    let
      -- s1: Fst (D_IfLf X V) = Fst parEnc.
      s1 : Deriv (atomic (eqn (ap1 Fst (ap2 D_IfLf X V))
                              (ap1 Fst parEnc)))
      s1 = cong1 Fst reduce

      -- s2: Fst parEnc = pTag (via parEncIsPair + axFst).
      s2a : Deriv (atomic (eqn (ap1 Fst parEnc)
                               (ap1 Fst (ap2 Pair pTag pBody))))
      s2a = cong1 Fst parEncIsPair
      s2b : Deriv (atomic (eqn (ap1 Fst (ap2 Pair pTag pBody)) pTag))
      s2b = axFst pTag pBody
      s2 : Deriv (atomic (eqn (ap1 Fst parEnc) pTag))
      s2 = ruleTrans s2a s2b

      s12 : Deriv (atomic (eqn (ap1 Fst (ap2 D_IfLf X V)) pTag))
      s12 = ruleTrans s1 s2

      -- s3: pTag = Pair (Fst pTag) (Snd pTag) via pair_eta on (tA, tB).
      etaTag : Deriv (atomic (eqn (ap2 Pair tA tB)
                                  (ap2 Pair (ap1 Fst (ap2 Pair tA tB))
                                            (ap1 Snd (ap2 Pair tA tB)))))
      etaTag = pair_eta tA tB

      -- Bridge from pTag back through pTagIsPair: pTag = Pair tA tB,
      -- so Fst pTag = Fst (Pair tA tB), Snd pTag = Snd (Pair tA tB).
      bridge_fst : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tA tB))
                                       (ap1 Fst pTag)))
      bridge_fst = cong1 Fst (ruleSym pTagIsPair)
      bridge_snd : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tA tB))
                                       (ap1 Snd pTag)))
      bridge_snd = cong1 Snd (ruleSym pTagIsPair)

      -- pTag = Pair tA tB = Pair (Fst pTag) (Snd pTag).
      etaTagBridged : Deriv (atomic (eqn pTag
                                          (ap2 Pair (ap1 Fst pTag) (ap1 Snd pTag))))
      etaTagBridged =
        ruleTrans pTagIsPair
          (ruleTrans etaTag
            (ruleTrans (congL Pair (ap1 Snd (ap2 Pair tA tB)) bridge_fst)
                       (congR Pair (ap1 Fst pTag) bridge_snd)))

      -- s123: Fst (D_IfLf X V) = Pair (Fst pTag) (Snd pTag).
      s123 : Deriv (atomic (eqn (ap1 Fst (ap2 D_IfLf X V))
                                (ap2 Pair (ap1 Fst pTag) (ap1 Snd pTag))))
      s123 = ruleTrans s12 etaTagBridged

      -- Now rewrite pTag back to Fst (D_IfLf X V) inside the RHS Pair.
      s12_sym : Deriv (atomic (eqn pTag (ap1 Fst (ap2 D_IfLf X V))))
      s12_sym = ruleSym s12

      rhs_fst : Deriv (atomic (eqn (ap1 Fst pTag)
                                    (ap1 Fst (ap1 Fst (ap2 D_IfLf X V)))))
      rhs_fst = cong1 Fst s12_sym
      rhs_snd : Deriv (atomic (eqn (ap1 Snd pTag)
                                    (ap1 Snd (ap1 Fst (ap2 D_IfLf X V)))))
      rhs_snd = cong1 Snd s12_sym

      rhs_pair : Deriv (atomic (eqn
        (ap2 Pair (ap1 Fst pTag) (ap1 Snd pTag))
        (ap2 Pair (ap1 Fst (ap1 Fst (ap2 D_IfLf X V)))
                  (ap1 Snd (ap1 Fst (ap2 D_IfLf X V))))))
      rhs_pair =
        ruleTrans (congL Pair (ap1 Snd pTag) rhs_fst)
                  (congR Pair (ap1 Fst (ap1 Fst (ap2 D_IfLf X V))) rhs_snd)
    in ruleTrans s123 rhs_pair

------------------------------------------------------------------------
-- Four leaf shape proofs.

shape_LL :
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_IfLf O O))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_IfLf O O)))
           (ap1 Snd (ap1 Fst (ap2 D_IfLf O O))))))
shape_LL =
  leaf_shape O O (parEncAxIfLfLL O) D_IfLf_reduce_OO
             _ _ (axRefl (parEncAxIfLfLL O))
             _ _ (axRefl _)

shape_LN : (a b : Term) ->
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_IfLf O (ap2 Pair a b)))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_IfLf O (ap2 Pair a b))))
           (ap1 Snd (ap1 Fst (ap2 D_IfLf O (ap2 Pair a b)))))))
shape_LN a b =
  leaf_shape O (ap2 Pair a b)
             (parEncAxIfLfL (ap1 cor a) (ap1 cor b))
             (D_IfLf_reduce_LN a b)
             _ _ (axRefl (parEncAxIfLfL (ap1 cor a) (ap1 cor b)))
             _ _ (axRefl _)

shape_NL : (p q : Term) ->
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_IfLf (ap2 Pair p q) O))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_IfLf (ap2 Pair p q) O)))
           (ap1 Snd (ap1 Fst (ap2 D_IfLf (ap2 Pair p q) O))))))
shape_NL p q =
  leaf_shape (ap2 Pair p q) O
             (parEncAxIfLfNL (ap1 cor p) (ap1 cor q))
             (D_IfLf_reduce_NL p q)
             _ _ (axRefl _)
             _ _ (axRefl _)

shape_NN : (p q a b : Term) ->
  Deriv (atomic
    (eqn (ap1 Fst (ap2 D_IfLf (ap2 Pair p q) (ap2 Pair a b)))
         (ap2 Pair
           (ap1 Fst (ap1 Fst (ap2 D_IfLf (ap2 Pair p q) (ap2 Pair a b))))
           (ap1 Snd (ap1 Fst (ap2 D_IfLf (ap2 Pair p q) (ap2 Pair a b)))))))
shape_NN p q a b =
  leaf_shape (ap2 Pair p q) (ap2 Pair a b)
             (parEncAxIfLfN (ap1 cor p) (ap1 cor q) (ap1 cor a) (ap1 cor b))
             (D_IfLf_reduce_NN p q a b)
             _ _ (axRefl _)
             _ _ (axRefl _)

------------------------------------------------------------------------
-- Nested ruleIndBT lift.  Same structure as D_correct2_IfLf_univ in
-- BRA/Thm12/Parts/IfLf.agda:957, except the shape formula has NO thmT,
-- so no thClosed gymnastics are needed.
--
-- Variable layout:
--   var 0 = x (outer inducting var)
--   var 1 = v (inner inducting var; held free during outer phase)
--   var 2, 3 = outer fresh
--   var 4, 5 = inner fresh

private
  v1OuterNat : Nat
  v1OuterNat = suc (suc zero)
  v2OuterNat : Nat
  v2OuterNat = suc (suc (suc zero))
  v1InnerNat : Nat
  v1InnerNat = suc (suc (suc (suc zero)))
  v2InnerNat : Nat
  v2InnerNat = suc (suc (suc (suc (suc zero))))
  vOuterNat : Nat
  vOuterNat = suc zero

  ----------------------------------------------------------------------
  -- Inner formula at fixed x = O.

  Q_baseO : Formula
  Q_baseO =
    atomic (eqn (ap1 Fst (ap2 D_IfLf O (var zero)))
                (ap2 Pair
                  (ap1 Fst (ap1 Fst (ap2 D_IfLf O (var zero))))
                  (ap1 Snd (ap1 Fst (ap2 D_IfLf O (var zero))))))

  inner_base_O_proof : Deriv (substF zero O Q_baseO)
  inner_base_O_proof = shape_LL

  inner_step_O_concl :
    Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
  inner_step_O_concl = shape_LN (var v1InnerNat) (var v2InnerNat)

  inner_step_O_imp_inner :
    Deriv (substF zero (var v2InnerNat) Q_baseO imp
           substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
  inner_step_O_imp_inner =
    mp (axK (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
            (substF zero (var v2InnerNat) Q_baseO))
       inner_step_O_concl

  inner_step_O_imp :
    Deriv (substF zero (var v1InnerNat) Q_baseO imp
           (substF zero (var v2InnerNat) Q_baseO imp
            substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO))
  inner_step_O_imp =
    mp (axK (substF zero (var v2InnerNat) Q_baseO imp
             substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_baseO)
            (substF zero (var v1InnerNat) Q_baseO))
       inner_step_O_imp_inner

  univ_x_O : Deriv Q_baseO
  univ_x_O = ruleIndBT Q_baseO v1InnerNat v2InnerNat
                       inner_base_O_proof inner_step_O_imp

  ----------------------------------------------------------------------
  -- Convert univ_x_O to substF zero O P_shape_IfLf via ruleInst.
  -- ruleInst zero (var 1) substitutes var 0 -> var 1, yielding a formula
  -- where var 1 is free.  This formula is definitionally equal to
  -- substF zero O P_shape_IfLf.

  outer_base_proof : Deriv (substF zero O P_shape_IfLf)
  outer_base_proof = ruleInst zero (var vOuterNat) univ_x_O

  ----------------------------------------------------------------------
  -- Inner formula at fixed x = Pair (var 2)(var 3).

  pairOuter : Term
  pairOuter = ap2 Pair (var v1OuterNat) (var v2OuterNat)

  Q_stepP : Formula
  Q_stepP =
    atomic (eqn (ap1 Fst (ap2 D_IfLf pairOuter (var zero)))
                (ap2 Pair
                  (ap1 Fst (ap1 Fst (ap2 D_IfLf pairOuter (var zero))))
                  (ap1 Snd (ap1 Fst (ap2 D_IfLf pairOuter (var zero))))))

  inner_base_P_proof : Deriv (substF zero O Q_stepP)
  inner_base_P_proof = shape_NL (var v1OuterNat) (var v2OuterNat)

  inner_step_P_concl :
    Deriv (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
  inner_step_P_concl =
    shape_NN (var v1OuterNat) (var v2OuterNat)
             (var v1InnerNat) (var v2InnerNat)

  inner_step_P_imp_inner :
    Deriv (substF zero (var v2InnerNat) Q_stepP imp
           substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
  inner_step_P_imp_inner =
    mp (axK (substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
            (substF zero (var v2InnerNat) Q_stepP))
       inner_step_P_concl

  inner_step_P_imp :
    Deriv (substF zero (var v1InnerNat) Q_stepP imp
           (substF zero (var v2InnerNat) Q_stepP imp
            substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP))
  inner_step_P_imp =
    mp (axK (substF zero (var v2InnerNat) Q_stepP imp
             substF zero (ap2 Pair (var v1InnerNat) (var v2InnerNat)) Q_stepP)
            (substF zero (var v1InnerNat) Q_stepP))
       inner_step_P_imp_inner

  univ_x_P : Deriv Q_stepP
  univ_x_P = ruleIndBT Q_stepP v1InnerNat v2InnerNat
                       inner_base_P_proof inner_step_P_imp

  outer_step_concl : Deriv (substF zero pairOuter P_shape_IfLf)
  outer_step_concl = ruleInst zero (var vOuterNat) univ_x_P

  outer_step_imp_inner :
    Deriv (substF zero (var v2OuterNat) P_shape_IfLf imp
           substF zero pairOuter P_shape_IfLf)
  outer_step_imp_inner =
    mp (axK (substF zero pairOuter P_shape_IfLf)
            (substF zero (var v2OuterNat) P_shape_IfLf))
       outer_step_concl

  outer_step_imp :
    Deriv (substF zero (var v1OuterNat) P_shape_IfLf imp
           (substF zero (var v2OuterNat) P_shape_IfLf imp
            substF zero pairOuter P_shape_IfLf))
  outer_step_imp =
    mp (axK (substF zero (var v2OuterNat) P_shape_IfLf imp
             substF zero pairOuter P_shape_IfLf)
            (substF zero (var v1OuterNat) P_shape_IfLf))
       outer_step_imp_inner

shape_D_F2_IfLf_var01 : Deriv P_shape_IfLf
shape_D_F2_IfLf_var01 =
  ruleIndBT P_shape_IfLf v1OuterNat v2OuterNat
            outer_base_proof outer_step_imp
