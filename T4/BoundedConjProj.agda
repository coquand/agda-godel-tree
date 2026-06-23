{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BoundedConjProj -- prerequisites for the PROJECTION lemma of the object
-- bounded conjunction (the internal course-of-values LOOKUP).  This file ships
-- the two clean pieces:
--
--   leqSuccFlip : leq a (s b) -> ~(a = s b) -> leq a b   (DNE on T82)
--   bigCLe_base : the base case (K = O) of the projection induction
--
-- The full projection  imp (leq p K) (imp (bigC f O K = O) (f p = O))  by
-- ruleIndNat on K is assembled from these + the sigma-split (bigC_step +
-- sigmaZeroL/R); its STEP case is a multi-antecedent Hilbert-combinator
-- assembly (documented in MEMORY) still to be built.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.BoundedConjProj where

open import T4.Base

open import T4.BoundedConj using ( bigC ; bigC_base ; bigC_step )

open import BRA3.Church        using ( sigma ; sub ; T33 )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.ChurchSubSucc using ( T_sub_O )
open import BRA3.ChurchT82     using ( T82 )
open import BRA3.RuleInst2     using ( ruleInst2 )
open import BRA3.Logic         using ( prependEqLeft ; eqSymImp )
open import BRA3.Classical     using ( axContrapos )
open import BRA3.Contrapositive using ( compI ; liftP ; bComb ; bCombTwo ; identP ; DNE )
open import BRA3.ChurchCM      using ( caseElim )
open import T4.SigmaZeroN      using ( sigmaZeroL ; sigmaZeroR )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impRuleSym ; impLift ; impEqTrans )

------------------------------------------------------------------------
-- leqSuccFlip :  leq a (s b)  ->  ~(a = s b)  ->  leq a b .

leqSuccFlip : (a b : Term) ->
  Deriv (imp (leq a (ap1 s b)) (imp (neg (eqF a (ap1 s b))) (leq a b)))
leqSuccFlip a b =
  let P1 : Formula
      P1 = leq a (ap1 s b)
      P2 : Formula
      P2 = neg (eqF a (ap1 s b))
      T82ab : Deriv (imp P1 (imp (neg (leq a b)) (eqF a (ap1 s b))))
      T82ab = ruleInst2 0 a 1 b refl T82
      inner_contra : Deriv (imp P1 (imp P2 (neg (neg (leq a b)))))
      inner_contra = compI T82ab (axContrapos (neg (leq a b)) (eqF a (ap1 s b)))
  in bCombTwo (liftP P1 (liftP P2 (DNE (leq a b)))) inner_contra

------------------------------------------------------------------------
-- Base case of the projection:  for K = O ,
--   imp (leq p O) (imp (bigC f O O = O) (f p = O)) .

bigCLe_base : (f : Fun1) (p : Term) ->
  Deriv (imp (leq p O) (imp (eqF (ap2 (bigC f) O O) O) (eqF (ap1 f p) O)))
bigCLe_base f p =
  let leqpO : Deriv (imp (leq p O) (eqF p O))
      leqpO = prependEqLeft p (ap2 sub p O) O (ruleSym (T_sub_O p))
      P1' : Formula
      P1' = eqF p O
      P2' : Formula
      P2' = eqF (ap2 (bigC f) O O) O
      fcong : Deriv (imp P1' (eqF (ap1 f O) (ap1 f p)))
      fcong = impRuleSym (impCong1 f p O (identP P1'))
      bcO : Deriv (imp P2' (eqF (ap1 f O) O))
      bcO = prependEqLeft (ap1 f O) (ap2 (bigC f) O O) O (ruleSym (bigC_base f O))
      e1 : Deriv (imp P1' (imp P2' (eqF (ap1 f O) (ap1 f p))))
      e1 = compI fcong (axK (eqF (ap1 f O) (ap1 f p)) P2')
      e2 : Deriv (imp P1' (imp P2' (eqF (ap1 f O) O)))
      e2 = liftP P1' bcO
      transL : Deriv (imp P1' (imp P2'
                 (imp (eqF (ap1 f O) (ap1 f p))
                      (imp (eqF (ap1 f O) O) (eqF (ap1 f p) O)))))
      transL = liftP P1' (liftP P2' (ax_eqTrans (ap1 f O) (ap1 f p) O))
      W : Deriv (imp P1' (imp P2' (eqF (ap1 f p) O)))
      W = bCombTwo (bCombTwo transL e1) e2
  in compI leqpO W

------------------------------------------------------------------------
-- CtA tiny reusable depth-3 Hilbert-context plumbing kit.  All combinators
-- work "in context [CtA,CtB,CtC]" i.e. with three nested antecedents.

private
  lift3 : (CtA CtB CtC : Formula) {X : Formula} ->
          Deriv X -> Deriv (imp CtA (imp CtB (imp CtC X)))
  lift3 CtA CtB CtC d = liftP CtA (liftP CtB (liftP CtC d))

  get3A : (CtA CtB CtC : Formula) -> Deriv (imp CtA (imp CtB (imp CtC CtA)))
  get3A CtA CtB CtC = bComb (liftP CtA (axK (imp CtC CtA) CtB)) (axK CtA CtC)

  get3B : (CtA CtB CtC : Formula) -> Deriv (imp CtA (imp CtB (imp CtC CtB)))
  get3B CtA CtB CtC = liftP CtA (axK CtB CtC)

  get3C : (CtA CtB CtC : Formula) -> Deriv (imp CtA (imp CtB (imp CtC CtC)))
  get3C CtA CtB CtC = liftP CtA (liftP CtB (identP CtC))

  -- modus ponens in context [CtA,CtB,CtC]
  ap3 : {CtA CtB CtC Q Rf : Formula} ->
        Deriv (imp CtA (imp CtB (imp CtC (imp Q Rf)))) ->
        Deriv (imp CtA (imp CtB (imp CtC Q))) ->
        Deriv (imp CtA (imp CtB (imp CtC Rf)))
  ap3 {CtA} {CtB} {CtC} {Q} {Rf} d1 d2 =
    bCombTwo (bCombTwo (liftP CtA (liftP CtB (axS CtC Q Rf))) d1) d2

  -- equational transitivity in context [CtA,CtB,CtC]
  trans3 : {CtA CtB CtC : Formula} (a b c : Term) ->
           Deriv (imp CtA (imp CtB (imp CtC (eqF a b)))) ->
           Deriv (imp CtA (imp CtB (imp CtC (eqF b c)))) ->
           Deriv (imp CtA (imp CtB (imp CtC (eqF a c))))
  trans3 {CtA} {CtB} {CtC} a b c f g =
    let fflip : Deriv (imp CtA (imp CtB (imp CtC (eqF b a))))
        fflip = ap3 (lift3 CtA CtB CtC (eqSymImp a b)) f
        lifted : Deriv (imp CtA (imp CtB (imp CtC (imp (eqF b c) (eqF a c)))))
        lifted = ap3 (lift3 CtA CtB CtC (ax_eqTrans b a c)) fflip
    in ap3 lifted g

------------------------------------------------------------------------
-- The PROJECTION lemma (internal course-of-values LOOKUP).
--
--   bigCLe f :
--     imp (sigma (sub p K) (bigC f O K) = O) (f p = O)   -- p = var 1, K = var 0
--
-- where  sigma (sub p K) (bigC f O K) = O  is the single object equation
-- encoding the conjunction  "leq p K  AND  bigC f O K = O".  By ruleIndNat
-- on K (= var 0); the bound  p (= var 1) stays free (universally
-- instantiable downstream).

bigCLe : (f : Fun1) ->
  Deriv (imp (eqF (ap2 sigma (ap2 sub (var 1) (var 0))
                             (ap2 (bigC f) O (var 0))) O)
             (eqF (ap1 f (var 1)) O))
bigCLe f = ruleIndNat 0 {P = Pform} baseCase stepCase
  where
    p : Term
    p = var 1

    Pform : Formula
    Pform = imp (eqF (ap2 sigma (ap2 sub p (var 0))
                                (ap2 (bigC f) O (var 0))) O)
                (eqF (ap1 f p) O)

    ----------------------------------------------------------------
    -- Base case  K := O .
    baseCase : Deriv (substF 0 O Pform)
    baseCase =
      let HO : Formula
          HO = eqF (ap2 sigma (ap2 sub p O) (ap2 (bigC f) O O)) O
          subO : Deriv (imp HO (eqF (ap2 sub p O) O))
          subO = sigmaZeroL (ap2 sub p O) (ap2 (bigC f) O O)
          bcO : Deriv (imp HO (eqF (ap2 (bigC f) O O) O))
          bcO = sigmaZeroR (ap2 sub p O) (ap2 (bigC f) O O)
          pEq : Deriv (imp HO (eqF p O))
          pEq = impEqTrans p (ap2 sub p O) O
                  (impLift {HO} (ruleSym (T_sub_O p))) subO
          fpfO : Deriv (imp HO (eqF (ap1 f p) (ap1 f O)))
          fpfO = impCong1 f p O pEq
          fO : Deriv (imp HO (eqF (ap1 f O) O))
          fO = impEqTrans (ap1 f O) (ap2 (bigC f) O O) O
                 (impLift {HO} (ruleSym (bigC_base f O))) bcO
      in impEqTrans (ap1 f p) (ap1 f O) O fpfO fO

    ----------------------------------------------------------------
    -- Step case  K := s K .
    stepCase : Deriv (imp Pform (substF 0 (ap1 s (var 0)) Pform))
    stepCase =
      let sk : Term
          sk = ap1 s (var 0)
          A  : Term
          A  = ap2 sub p sk
          B  : Term
          B  = ap2 (bigC f) O sk
          AK : Term
          AK = ap2 sub p (var 0)
          BK : Term
          BK = ap2 (bigC f) O (var 0)
          H  : Formula
          H  = eqF (ap2 sigma A B) O
          PK : Formula
          PK = Pform
          G  : Formula
          G  = eqF (ap1 f p) O
          X  : Formula
          X  = eqF p sk

          -- facts available in any context [C1, PK, H] (C1 = X or neg X).
          fSigSK : (C1 : Formula) ->
            Deriv (imp C1 (imp PK (imp H
                    (eqF (ap2 sigma (ap1 f sk) BK) O))))
          fSigSK C1 =
            let fBCsk : Deriv (imp C1 (imp PK (imp H (eqF B O))))
                fBCsk = ap3 (lift3 C1 PK H (sigmaZeroR A B)) (get3C C1 PK H)
                rwStep : Deriv (imp (eqF B O)
                          (eqF (ap2 sigma (ap1 f sk) BK) O))
                rwStep = prependEqLeft (ap2 sigma (ap1 f sk) BK) B O
                           (ruleSym (bigC_step f O (var 0)))
            in ap3 (lift3 C1 PK H rwStep) fBCsk

          fSK : (C1 : Formula) ->
            Deriv (imp C1 (imp PK (imp H (eqF (ap1 f sk) O))))
          fSK C1 = ap3 (lift3 C1 PK H (sigmaZeroL (ap1 f sk) BK)) (fSigSK C1)

          fBCK : (C1 : Formula) ->
            Deriv (imp C1 (imp PK (imp H (eqF BK O))))
          fBCK C1 = ap3 (lift3 C1 PK H (sigmaZeroR (ap1 f sk) BK)) (fSigSK C1)

          ----------------------------------------------------------
          -- X-branch :  p = s K  =>  f p = f (s K) = O .
          X_R : Deriv (imp X (imp PK (imp H G)))
          X_R =
            let fEq : Deriv (imp X (imp PK (imp H
                        (eqF (ap1 f p) (ap1 f sk)))))
                fEq = ap3 (lift3 X PK H (ax_eqCong1 f p sk)) (get3A X PK H)
            in trans3 {X} {PK} {H} (ap1 f p) (ap1 f sk) O fEq (fSK X)

          ----------------------------------------------------------
          -- Y-branch :  p /= s K  =>  leq p K , bigC f O K = O  =>  IH .
          Y_R : Deriv (imp (neg X) (imp PK (imp H G)))
          Y_R =
            let nX : Formula
                nX = neg X
                fLeqsk : Deriv (imp nX (imp PK (imp H (eqF A O))))
                fLeqsk = ap3 (lift3 nX PK H (sigmaZeroL A B)) (get3C nX PK H)
                fLeqK : Deriv (imp nX (imp PK (imp H (eqF AK O))))
                fLeqK =
                  let lf : Deriv (imp nX (imp PK (imp H
                            (imp (eqF A O) (imp nX (eqF AK O))))))
                      lf = lift3 nX PK H (leqSuccFlip p (var 0))
                  in ap3 (ap3 lf fLeqsk) (get3A nX PK H)
                fConjK : Deriv (imp nX (imp PK (imp H
                          (eqF (ap2 sigma AK BK) O))))
                fConjK =
                  let r1 : Deriv (imp nX (imp PK (imp H
                            (eqF (ap2 sigma AK BK) (ap2 sigma O BK)))))
                      r1 = ap3 (lift3 nX PK H (ax_eqCongL sigma AK O BK)) fLeqK
                      r2 : Deriv (imp nX (imp PK (imp H
                            (eqF (ap2 sigma O BK) (ap2 sigma O O)))))
                      r2 = ap3 (lift3 nX PK H (ax_eqCongR sigma BK O O)) (fBCK nX)
                      r3 : Deriv (imp nX (imp PK (imp H
                            (eqF (ap2 sigma O O) O))))
                      r3 = lift3 nX PK H (T33 O)
                  in trans3 (ap2 sigma AK BK) (ap2 sigma O O) O
                       (trans3 (ap2 sigma AK BK) (ap2 sigma O BK) (ap2 sigma O O)
                          r1 r2)
                       r3
            in ap3 (get3B nX PK H) fConjK
      in caseElim {X = X} {Y = neg X} {Rf = imp PK (imp H G)}
           (identP (neg X)) X_R Y_R
