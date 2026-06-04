{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RunProgMono -- FORMULA-LEVEL run monotonicity ( the surprise-GII two-fuel
-- linchpin ).
--
-- =====================================================================
-- WHY ( supersedes the earlier "readout non-invertible" claim ).
-- =====================================================================
--
-- An earlier note claimed formula-level run-monotonicity is NOT internally
-- derivable ( "readout not invertible : from  runProg p L = s val  one cannot
-- recover the halt witness" ).   That was WRONG.   The read-off
--   readout = fork (compose1U s Snd) o isHalt   ( T4.EvalUEval )
-- returns  O  on non-halted configs ( isHalt c = O  =>  readout c = o c = O ).
-- So  readout c = s val  INTERNALLY forces  isHalt c = s O , hence ( symbolic
-- reflection  T4.NatEqReflect.natEqF_complete )  Fst c = tagHALT , i.e.  c  is a
--  stepU -fixpoint.   Iterating  stepU  any further preserves the value, giving
--
--   runProgMonoPlus :  runProg p L = s val   =>   runProg p (L + g) = s val
--
-- for ALL Terms  p, val, L, g  ( no  NoVar , no config-level halt witness ).
-- This is exactly  clos 's "by monotonicity of run", now FORMULA-level, so the
-- two fuels  x0 ( K_rest ) and  x1 ( phi )  can be lifted to a common bound
-- WITHOUT pinning either.

module T4.RunProgMono where

open import T4.Base

open import BRA3.Church            using ( sigma ; pi )
open import BRA3.CourseOfValues    using ( iter )
open import BRA3.RecBRA3AtPairUniv using ( iter_base_univ ; iter_step_univ )
open import BRA3.Logic             using ( eqSymImp ; prependEqLeft )
open import BRA3.SubT.NatEq         using ( natEqF )
open import BRA3.SubT.V2NatNeq      using ( natEqF_at_neq ; decideNatNeq )
open import BRA3.Contrapositive     using ( identP ; compI )
open import BRA3.ChurchT80          using ( succEqO_to_anything )
open import BRA3.ChurchCM           using ( caseElim )
open import BRA3.ChurchDChurchAsSub using ( caseElimUnderOne )
open import BRA3.RuleInst2          using ( ruleInst2 )

open import T4.EvalU      using ( tagHALT ; tagEV ; tagRT )
open import T4.EvalUEval  using ( readout ; isHalt ; initF ; evalU ; evalU_unfold )
open import T4.EvalUStep
  using ( stepU ; fork ; evBranch ; modeRT ; isEV ; isRT ; rtBranch ; fireF )
open import T4.Kdef       using ( runProg ; runProg_eq )
open import T4.ProgParse  using ( parse )
open import T4.RunMonoLeq using ( iter_add_gen )
open import T4.NatEqReflect using ( natEqF_complete ; app2 )
open import T4.Thm12.ImpHelpers
  using ( impLift ; impCongR ; impCongL ; impCong1 ; impEqTrans ; impRuleSym )
open import BRA3.Contrapositive    using ( bComb ; axExFalso )

------------------------------------------------------------------------
-- SECTION 0.  Two-antecedent  eqF -transitivity ( Carneiro, mirroring
--   ImpHelpers.impEqTrans one layer up via  app2 ).

impEqTrans2 :
  {W1 W2 : Formula} (a b c : Term) ->
  Deriv (imp W1 (imp W2 (eqF a b))) ->
  Deriv (imp W1 (imp W2 (eqF b c))) ->
  Deriv (imp W1 (imp W2 (eqF a c)))
impEqTrans2 {W1} {W2} a b c f1 f2 =
  let f1flip : Deriv (imp W1 (imp W2 (eqF b a)))
      f1flip = app2 (impLift {W1} (impLift {W2} (eqSymImp a b))) f1
      lifted : Deriv (imp W1 (imp W2 (imp (eqF b c) (eqF a c))))
      lifted = app2 (impLift {W1} (impLift {W2} (ax_eqTrans b a c))) f1flip
  in app2 lifted f2

------------------------------------------------------------------------
-- SECTION 1.  Iterating a  stepU -fixpoint preserves it ( for ANY object fuel
--   g , for ANY Term config c ).   The fixpoint fact  stepU c = c  is threaded
--   as the antecedent of the induction motive ( config at  var 1 , fuel at
--   var 0 ), so the  ruleIndNat  is var-safe for a symbolic c ; the actual c
--   and g are installed by  ruleInst2  at the end.

iterFixGen_univ :
  Deriv (imp (eqF (ap1 stepU (var (suc zero))) (var (suc zero)))
             (eqF (ap2 (iter stepU) (var (suc zero)) (var zero)) (var (suc zero))))
iterFixGen_univ =
  let Pant : Formula
      Pant = eqF (ap1 stepU (var (suc zero))) (var (suc zero))
      cfg : Term
      cfg = var (suc zero)
      Pmot : Formula
      Pmot = imp Pant (eqF (ap2 (iter stepU) cfg (var zero)) cfg)

      baseCase : Deriv (imp Pant (eqF (ap2 (iter stepU) cfg O) cfg))
      baseCase = impLift {Pant} (iter_base_univ stepU cfg)

      stepCase : Deriv (imp Pmot
                            (imp Pant (eqF (ap2 (iter stepU) cfg (ap1 s (var zero))) cfg)))
      stepCase =
        let A : Term                       -- iter stepU cfg (var 0)
            A = ap2 (iter stepU) cfg (var zero)
            B : Term                       -- iter stepU cfg (s (var 0))
            B = ap2 (iter stepU) cfg (ap1 s (var zero))
            Qn : Formula
            Qn = eqF A cfg

            e_su : Deriv (eqF B (ap1 stepU A))
            e_su = iter_step_univ stepU cfg (var zero)

            f0 : Deriv (imp Pant (imp Qn (eqF B (ap1 stepU A))))
            f0 = impLift {Pant} (impLift {Qn} e_su)
            qn_as : Deriv (imp Pant (imp Qn (eqF A cfg)))
            qn_as = impLift {Pant} (identP Qn)
            f1 : Deriv (imp Pant (imp Qn (eqF (ap1 stepU A) (ap1 stepU cfg))))
            f1 = app2 (impLift {Pant} (impLift {Qn} (ax_eqCong1 stepU A cfg))) qn_as
            f2 : Deriv (imp Pant (imp Qn (eqF (ap1 stepU cfg) cfg)))
            f2 = axK Pant Qn

            g1 : Deriv (imp Pant (imp Qn (eqF B (ap1 stepU cfg))))
            g1 = impEqTrans2 {Pant} {Qn} B (ap1 stepU A) (ap1 stepU cfg) f0 f1
            w : Deriv (imp Pant (imp Qn (eqF B cfg)))
            w = impEqTrans2 {Pant} {Qn} B (ap1 stepU cfg) cfg g1 f2
        in mp (axS Pant Qn (eqF B cfg)) w
  in ruleIndNat zero {P = Pmot} baseCase stepCase

iterFixGen :
  (c : Term) ->
  Deriv (eqF (ap1 stepU c) c) ->
  (g : Term) ->
  Deriv (eqF (ap2 (iter stepU) c g) c)
iterFixGen c hfix g =
  mp (ruleInst2 zero g (suc zero) c refl iterFixGen_univ) hfix

------------------------------------------------------------------------
-- SECTION 2.  Mode generalisation of  stepU_at_halt :  from  Fst c = tagHALT
--   ( NOT necessarily  c = cfgHALT val )  the universal machine is stuck.

isEV_at :
  (c : Term) -> Deriv (eqF (ap1 Fst c) (natCode tagHALT)) ->
  Deriv (eqF (ap1 isEV c) O)
isEV_at c hmode =
  let e1 = ax_C natEqF Fst (constN tagEV) c
      e2 = congL natEqF (ap1 (constN tagEV) c) hmode
      e3 = congR natEqF (natCode tagHALT) (constN_eq tagEV c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3
       (natEqF_at_neq tagHALT tagEV (decideNatNeq tagHALT tagEV (\ ())))))

isRT_at :
  (c : Term) -> Deriv (eqF (ap1 Fst c) (natCode tagHALT)) ->
  Deriv (eqF (ap1 isRT c) O)
isRT_at c hmode =
  let e1 = ax_C natEqF Fst (constN tagRT) c
      e2 = congL natEqF (ap1 (constN tagRT) c) hmode
      e3 = congR natEqF (natCode tagHALT) (constN_eq tagRT c)
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3
       (natEqF_at_neq tagHALT tagRT (decideNatNeq tagHALT tagRT (\ ())))))

stepU_at_haltMode :
  (c : Term) -> Deriv (eqF (ap1 Fst c) (natCode tagHALT)) ->
  Deriv (eqF (ap1 stepU c) c)
stepU_at_haltMode c hmode =
  let m1 = fireF evBranch modeRT isEV c (isEV_at c hmode)
      m2 = fireF rtBranch u isRT c (isRT_at c hmode)
  in ruleTrans m1 (ruleTrans m2 (ax_u c))

------------------------------------------------------------------------
-- SECTION 3.  Readout inversion :  readout c = s val  =>  Fst c = tagHALT .
--   readout = fork (compose1U s Snd) o isHalt  ;  if  Fst c /= tagHALT  then
--   ( natEqF_complete )  isHalt c = O , so  readout c = Snd (...) = o c = O ,
--   contradicting  readout c = s val .   ( Classical dispatch on the goal. )

readoutModeInv :
  (c val : Term) ->
  Deriv (eqF (ap1 readout c) (ap1 s val)) ->
  Deriv (eqF (ap1 Fst c) (natCode tagHALT))
readoutModeInv c val H =
  let goal : Formula
      goal = eqF (ap1 Fst c) (natCode tagHALT)
      PR : Term                 -- C pi (compose1U s Snd) o  applied to c
      PR = ap1 (C pi (compose1U s Snd) o) c

      -- isHalt c = natEqF (Fst c) (natCode tagHALT) .
      isHaltUnfold : Deriv (eqF (ap1 isHalt c)
                                (ap2 natEqF (ap1 Fst c) (natCode tagHALT)))
      isHaltUnfold =
        ruleTrans (ax_C natEqF Fst (constN tagHALT) c)
                  (congR natEqF (ap1 Fst c) (constN_eq tagHALT c))

      -- readout c = condFork PR (isHalt c) .
      rcUnfold : Deriv (eqF (ap1 readout c) (ap2 condFork PR (ap1 isHalt c)))
      rcUnfold = ax_C condFork (C pi (compose1U s Snd) o) isHalt c

      -- Snd PR = o c .
      sndPR : Deriv (eqF (ap1 Snd PR) (ap1 o c))
      sndPR = ruleTrans (cong1 Snd (ax_C pi (compose1U s Snd) o c))
                        (axSnd (ap1 (compose1U s Snd) c) (ap1 o c))

      -- Under  neg goal :  isHalt c = O .
      isHaltO : Deriv (imp (neg goal) (eqF (ap1 isHalt c) O))
      isHaltO =
        compI (natEqF_complete (ap1 Fst c) (natCode tagHALT))
              (prependEqLeft (ap1 isHalt c)
                             (ap2 natEqF (ap1 Fst c) (natCode tagHALT)) O
                             isHaltUnfold)

      -- Under  neg goal :  readout c = O .
      readoutO : Deriv (imp (neg goal) (eqF (ap1 readout c) O))
      readoutO =
        let eA : Deriv (imp (neg goal)
                            (eqF (ap2 condFork PR (ap1 isHalt c)) (ap2 condFork PR O)))
            eA = impCongR {neg goal} condFork (ap1 isHalt c) O PR isHaltO
        in impEqTrans {neg goal} (ap1 readout c) (ap2 condFork PR (ap1 isHalt c)) O
             (impLift {neg goal} rcUnfold)
             (impEqTrans {neg goal} (ap2 condFork PR (ap1 isHalt c)) (ap2 condFork PR O) O
                eA
                (impEqTrans {neg goal} (ap2 condFork PR O) (ap1 Snd PR) O
                   (impLift {neg goal} (condFork_false PR))
                   (impEqTrans {neg goal} (ap1 Snd PR) (ap1 o c) O
                      (impLift {neg goal} sndPR)
                      (impLift {neg goal} (ax_o c)))))

      -- Under  neg goal :  s val = O  -- contradiction.
      svalO : Deriv (imp (neg goal) (eqF (ap1 s val) O))
      svalO = impEqTrans {neg goal} (ap1 s val) (ap1 readout c) O
                (impLift {neg goal} (ruleSym H)) readoutO

      caseNeg : Deriv (imp (neg goal) goal)
      caseNeg = compI svalO (succEqO_to_anything val goal)
  in caseElim {goal} {neg goal} {goal} (identP (neg goal)) (identP goal) caseNeg

------------------------------------------------------------------------
-- SECTION 4.  The headline : additive formula-level run monotonicity.

runProgMonoPlus :
  (p val L g : Term) ->
  Deriv (eqF (ap2 runProg p L) (ap1 s val)) ->
  Deriv (eqF (ap2 runProg p (ap2 sigma L g)) (ap1 s val))
runProgMonoPlus p val L g hyp =
  let pe : Term
      pe = ap1 parse p
      C0 : Term                 -- iter stepU (initF (parse p)) L
      C0 = ap2 (iter stepU) (ap1 initF pe) L

      -- readout C0 = s val .
      hRO : Deriv (eqF (ap1 readout C0) (ap1 s val))
      hRO = ruleTrans (ruleSym (ruleTrans (runProg_eq p L) (evalU_unfold pe L))) hyp

      -- C0 is a stepU-fixpoint.
      fstHalt : Deriv (eqF (ap1 Fst C0) (natCode tagHALT))
      fstHalt = readoutModeInv C0 val hRO
      cFix : Deriv (eqF (ap1 stepU C0) C0)
      cFix = stepU_at_haltMode C0 fstHalt

      -- iter stepU (initF (parse p)) (L + g) = iter stepU C0 g = C0 .
      addEq : Deriv (eqF (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g))
                         (ap2 (iter stepU) C0 g))
      addEq = iter_add_gen stepU (ap1 initF pe) L g
      cLgEq : Deriv (eqF (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g)) C0)
      cLgEq = ruleTrans addEq (iterFixGen C0 cFix g)

      -- readout (config at L+g) = readout C0 = s val .
      finalRO : Deriv (eqF (ap1 readout (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g)))
                           (ap1 s val))
      finalRO = ruleTrans (cong1 readout cLgEq) hRO
  in ruleTrans (ruleTrans (runProg_eq p (ap2 sigma L g))
                          (evalU_unfold pe (ap2 sigma L g)))
               finalRO

------------------------------------------------------------------------
-- SECTION 5.  CARNEIRO IMP-LIFT of the whole chain : the monotone step
--   threaded under an arbitrary antecedent  P  ( so a POSITIVE  runProg = s val
--   conjunct that is itself only available UNDER a hypothesis -- e.g. a conjunct
--   of  K_rest  under the imp of the frontEnd -- can be lifted x0 -> common ).

-- imp-lifted  fireF  ( the false-branch fire, with the flag witness under P ).
imp_fireF :
  (P : Formula) (trueB falseB flag : Fun1) (input : Term) ->
  Deriv (imp P (eqF (ap1 flag input) O)) ->
  Deriv (imp P (eqF (ap1 (fork trueB falseB flag) input) (ap1 falseB input)))
imp_fireF P trueB falseB flag input flagFP =
  let pairT : Term
      pairT = ap1 (C pi trueB falseB) input
      e1 : Deriv (eqF (ap1 (fork trueB falseB flag) input)
                      (ap2 condFork pairT (ap1 flag input)))
      e1 = ax_C condFork (C pi trueB falseB) flag input
      e2 : Deriv (imp P (eqF (ap2 condFork pairT (ap1 flag input))
                             (ap2 condFork pairT O)))
      e2 = impCongR {P} condFork (ap1 flag input) O pairT flagFP
      e34 : Deriv (eqF (ap2 condFork pairT O) (ap1 falseB input))
      e34 = ruleTrans (condFork_false pairT)
              (ruleTrans (cong1 Snd (ax_C pi trueB falseB input))
                         (axSnd (ap1 trueB input) (ap1 falseB input)))
  in impEqTrans {P} (ap1 (fork trueB falseB flag) input)
       (ap2 condFork pairT (ap1 flag input)) (ap1 falseB input)
       (impLift {P} e1)
       (impEqTrans {P} (ap2 condFork pairT (ap1 flag input)) (ap2 condFork pairT O)
                   (ap1 falseB input) e2 (impLift {P} e34))

-- isEV / isRT  fire to  O  under  P  given  Fst c = tagHALT  under  P .
imp_modeFlag_O :
  (P : Formula) (c : Term) (tg : Nat) ->
  Deriv (eqF (ap2 natEqF (natCode tagHALT) (natCode tg)) O) ->
  Deriv (imp P (eqF (ap1 Fst c) (natCode tagHALT))) ->
  Deriv (imp P (eqF (ap1 (C natEqF Fst (constN tg)) c) O))
imp_modeFlag_O P c tg neqHt hmodeP =
  let e1 : Deriv (eqF (ap1 (C natEqF Fst (constN tg)) c)
                      (ap2 natEqF (ap1 Fst c) (ap1 (constN tg) c)))
      e1 = ax_C natEqF Fst (constN tg) c
      e2 : Deriv (imp P (eqF (ap2 natEqF (ap1 Fst c) (ap1 (constN tg) c))
                             (ap2 natEqF (natCode tagHALT) (ap1 (constN tg) c))))
      e2 = impCongL {P} natEqF (ap1 Fst c) (natCode tagHALT) (ap1 (constN tg) c) hmodeP
      e34 : Deriv (eqF (ap2 natEqF (natCode tagHALT) (ap1 (constN tg) c)) O)
      e34 = ruleTrans (congR natEqF (natCode tagHALT) (constN_eq tg c)) neqHt
  in impEqTrans {P} (ap1 (C natEqF Fst (constN tg)) c)
       (ap2 natEqF (ap1 Fst c) (ap1 (constN tg) c)) O
       (impLift {P} e1)
       (impEqTrans {P} (ap2 natEqF (ap1 Fst c) (ap1 (constN tg) c))
          (ap2 natEqF (natCode tagHALT) (ap1 (constN tg) c)) O
          e2 (impLift {P} e34))

imp_stepU_at_haltMode :
  (P : Formula) (c : Term) ->
  Deriv (imp P (eqF (ap1 Fst c) (natCode tagHALT))) ->
  Deriv (imp P (eqF (ap1 stepU c) c))
imp_stepU_at_haltMode P c hmodeP =
  let evO : Deriv (imp P (eqF (ap1 isEV c) O))
      evO = imp_modeFlag_O P c tagEV
              (natEqF_at_neq tagHALT tagEV (decideNatNeq tagHALT tagEV (\ ()))) hmodeP
      rtO : Deriv (imp P (eqF (ap1 isRT c) O))
      rtO = imp_modeFlag_O P c tagRT
              (natEqF_at_neq tagHALT tagRT (decideNatNeq tagHALT tagRT (\ ()))) hmodeP
      m1 : Deriv (imp P (eqF (ap1 stepU c) (ap1 modeRT c)))
      m1 = imp_fireF P evBranch modeRT isEV c evO
      m2 : Deriv (imp P (eqF (ap1 modeRT c) (ap1 u c)))
      m2 = imp_fireF P rtBranch u isRT c rtO
  in impEqTrans {P} (ap1 stepU c) (ap1 modeRT c) c m1
       (impEqTrans {P} (ap1 modeRT c) (ap1 u c) c m2 (impLift {P} (ax_u c)))

imp_readoutModeInv :
  (P : Formula) (c val : Term) ->
  Deriv (imp P (eqF (ap1 readout c) (ap1 s val))) ->
  Deriv (imp P (eqF (ap1 Fst c) (natCode tagHALT)))
imp_readoutModeInv P c val hP =
  let goal : Formula
      goal = eqF (ap1 Fst c) (natCode tagHALT)
      PR : Term
      PR = ap1 (C pi (compose1U s Snd) o) c

      isHaltUnfold : Deriv (eqF (ap1 isHalt c)
                                (ap2 natEqF (ap1 Fst c) (natCode tagHALT)))
      isHaltUnfold =
        ruleTrans (ax_C natEqF Fst (constN tagHALT) c)
                  (congR natEqF (ap1 Fst c) (constN_eq tagHALT c))
      rcUnfold : Deriv (eqF (ap1 readout c) (ap2 condFork PR (ap1 isHalt c)))
      rcUnfold = ax_C condFork (C pi (compose1U s Snd) o) isHalt c
      sndPR : Deriv (eqF (ap1 Snd PR) (ap1 o c))
      sndPR = ruleTrans (cong1 Snd (ax_C pi (compose1U s Snd) o c))
                        (axSnd (ap1 (compose1U s Snd) c) (ap1 o c))

      -- Under  neg goal :  isHalt c = O ,  hence  readout c = O .
      isHaltO : Deriv (imp (neg goal) (eqF (ap1 isHalt c) O))
      isHaltO =
        compI (natEqF_complete (ap1 Fst c) (natCode tagHALT))
              (prependEqLeft (ap1 isHalt c)
                             (ap2 natEqF (ap1 Fst c) (natCode tagHALT)) O isHaltUnfold)
      readoutO : Deriv (imp (neg goal) (eqF (ap1 readout c) O))
      readoutO =
        let eA : Deriv (imp (neg goal)
                            (eqF (ap2 condFork PR (ap1 isHalt c)) (ap2 condFork PR O)))
            eA = impCongR {neg goal} condFork (ap1 isHalt c) O PR isHaltO
        in impEqTrans {neg goal} (ap1 readout c) (ap2 condFork PR (ap1 isHalt c)) O
             (impLift {neg goal} rcUnfold)
             (impEqTrans {neg goal} (ap2 condFork PR (ap1 isHalt c)) (ap2 condFork PR O) O
                eA
                (impEqTrans {neg goal} (ap2 condFork PR O) (ap1 Snd PR) O
                   (impLift {neg goal} (condFork_false PR))
                   (impEqTrans {neg goal} (ap1 Snd PR) (ap1 o c) O
                      (impLift {neg goal} sndPR)
                      (impLift {neg goal} (ax_o c)))))

      -- Under  (P , neg goal) :  s val = O   ( from  hP  and  readoutO ).
      hP_neg : Deriv (imp P (imp (neg goal) (eqF (ap1 s val) (ap1 readout c))))
      hP_neg = bComb (impLift {P} (axK (eqF (ap1 s val) (ap1 readout c)) (neg goal)))
                     (impRuleSym hP)
      readoutO_l : Deriv (imp P (imp (neg goal) (eqF (ap1 readout c) O)))
      readoutO_l = impLift {P} readoutO
      svalO : Deriv (imp P (imp (neg goal) (eqF (ap1 s val) O)))
      svalO = impEqTrans2 {P} {neg goal} (ap1 s val) (ap1 readout c) O hP_neg readoutO_l
      caseNeg : Deriv (imp P (imp (neg goal) goal))
      caseNeg = app2 (impLift {P} (impLift {neg goal} (succEqO_to_anything val goal))) svalO
  in caseElimUnderOne {P} {goal} {neg goal} {goal}
       (impLift {P} (identP (neg goal)))
       (impLift {P} (identP goal))
       caseNeg

------------------------------------------------------------------------
-- SECTION 6.  The IMP-LIFTED additive monotonicity ( the form the two-fuel
--   frontEnd consumes ) :  P -> runProg p L = s val   gives
--   P -> runProg p (L + g) = s val .

imp_runProgMonoPlus :
  (P : Formula) (p val L g : Term) ->
  Deriv (imp P (eqF (ap2 runProg p L) (ap1 s val))) ->
  Deriv (imp P (eqF (ap2 runProg p (ap2 sigma L g)) (ap1 s val)))
imp_runProgMonoPlus P p val L g hyp =
  let pe : Term
      pe = ap1 parse p
      C0 : Term
      C0 = ap2 (iter stepU) (ap1 initF pe) L

      hRO : Deriv (imp P (eqF (ap1 readout C0) (ap1 s val)))
      hRO = impEqTrans {P} (ap1 readout C0) (ap2 runProg p L) (ap1 s val)
              (impLift {P} (ruleSym (ruleTrans (runProg_eq p L) (evalU_unfold pe L))))
              hyp
      fstHalt : Deriv (imp P (eqF (ap1 Fst C0) (natCode tagHALT)))
      fstHalt = imp_readoutModeInv P C0 val hRO
      cFix : Deriv (imp P (eqF (ap1 stepU C0) C0))
      cFix = imp_stepU_at_haltMode P C0 fstHalt

      -- iter stepU (initF (parse p)) (L+g) = C0   under P  ( iterFixGen is a
      --   CLOSED implication  (stepU C0 = C0) -> (iter stepU C0 g = C0) ).
      cLgEq : Deriv (imp P (eqF (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g)) C0))
      cLgEq =
        impEqTrans {P} (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g))
          (ap2 (iter stepU) C0 g) C0
          (impLift {P} (iter_add_gen stepU (ap1 initF pe) L g))
          (compI cFix (ruleInst2 zero g (suc zero) C0 refl iterFixGen_univ))
      finalRO : Deriv (imp P
                  (eqF (ap1 readout (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g)))
                       (ap1 s val)))
      finalRO = impEqTrans {P}
                  (ap1 readout (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g)))
                  (ap1 readout C0) (ap1 s val)
                  (impCong1 {P} readout
                     (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g)) C0 cLgEq)
                  hRO
  in impEqTrans {P} (ap2 runProg p (ap2 sigma L g))
       (ap1 readout (ap2 (iter stepU) (ap1 initF pe) (ap2 sigma L g))) (ap1 s val)
       (impLift {P} (ruleTrans (runProg_eq p (ap2 sigma L g))
                               (evalU_unfold pe (ap2 sigma L g))))
       finalRO
