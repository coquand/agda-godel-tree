{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.NatEqReflect -- SYMBOLIC reflection of the machine's mode test  natEqF .
--
-- =====================================================================
-- WHY.
-- =====================================================================
--
-- The universal machine's HALT test is  isHalt = C natEqF Fst (constN tagHALT)
-- ( T4.EvalUEval ), built on  natEqF  ( BRA3.SubT.NatEq ).   To invert  readout
-- ( "readout c = s val  forces  Fst c = tagHALT" ) the formula-level run
-- monotonicity needs SYMBOLIC reflection of  natEqF  ( the numeral-only
-- natEq_at_neq  does not suffice -- the machine's mode  Fst c  is symbolic ):
--
--   natEqF_sound    :  natEqF a b = s O   =>   a = b          ( all Terms a, b )
--   natEqF_complete :  a /= b             =>   natEqF a b = O  ( all Terms a, b )
--
-- Both are internally derivable from three SHIPPED facts:
--   * natEq_unfold_nc  ( closed-free :  natEqF a b = condFork (Pair Z2 O) Z1 ,
--       Z1 = isZero (sub a b) , Z2 = isZero (sub b a) ) ;
--   * T52  ( boolean totality of isZero :  ~(isZero x = O) -> isZero x = s O )
--     + isZeroSO_to_zero  ( isZero x = s O -> x = O ) ;
--   * antisym_curry  ( leq a b -> leq b a -> a = b ;  leq a b = (sub a b = O) ).
--
-- All internal reasoning is done in CARNEIRO style ( everything threaded under
-- the standing hypothesis via  impLift / bComb / caseElimUnderOne / impFlip ),
-- not by hand-rolled Hilbert combinator nests.

module T4.NatEqReflect where

open import T4.Base

open import BRA3.Church           using ( sub ; isZero )
open import BRA3.ChurchLeq        using ( leq )
open import BRA3.SubT.NatEq        using ( natEqF )
open import BRA3.SubT.NatEqRefl    using ( natEq_unfold_nc )
open import BRA3.RecBRA3AtPairUniv using ( condFork_true_univ )
open import BRA3.ChurchT52         using ( T52 )
open import BRA3.ChurchIsZeroEq    using ( isZeroSO_to_zero )
open import BRA3.ChurchT80         using ( exFalsoFromSO ; impFlip )
open import BRA3.ChurchCM          using ( caseElim )
open import BRA3.ChurchDChurchAsSub using ( caseElimUnderOne )
open import BRA3.Contrapositive    using ( identP ; compI ; bComb ; axExFalso ; axContrapos )
open import T4.Counting            using ( antisym_curry )
open import T4.Thm12.ImpHelpers    using ( impLift ; impCongR ; impEqTrans ; impRuleSym )

------------------------------------------------------------------------
-- SECTION 0.  Carneiro micro-helper :  modus ponens under TWO standing
--   hypotheses ( Y  then  P ).   app2 f g  is  bComb  at the inner P-layer.

app2 : {Y P A B : Formula} ->
       Deriv (imp Y (imp P (imp A B))) ->
       Deriv (imp Y (imp P A)) ->
       Deriv (imp Y (imp P B))
app2 {Y} {P} {A} {B} f g = bComb (bComb (impLift {Y} (axS P A B)) f) g

------------------------------------------------------------------------
-- SECTION 1.  The two condFork value facts ( closed-free unfold of natEqF ).
--   factO :  Z1 = O    =>  natEqF a b = O      ( false dispatch -> Snd = O )
--   factS :  Z1 = s O  =>  natEqF a b = Z2     ( true dispatch  -> Fst = Z2 )

factO :
  (a b : Term) ->
  Deriv (imp (eqF (ap1 isZero (ap2 sub a b)) O)
             (eqF (ap2 natEqF a b) O))
factO a b =
  let Z1 : Term
      Z1 = ap1 isZero (ap2 sub a b)
      Z2 : Term
      Z2 = ap1 isZero (ap2 sub b a)
      P : Term
      P = ap2 Pair Z2 O
      X : Formula
      X = eqF Z1 O
      U : Deriv (eqF (ap2 natEqF a b) (ap2 condFork P Z1))
      U = natEq_unfold_nc a b

      eA : Deriv (imp X (eqF (ap2 condFork P Z1) (ap2 condFork P O)))
      eA = impCongR {X} condFork Z1 O P (identP X)
      eB : Deriv (imp X (eqF (ap2 condFork P O) (ap1 Snd P)))
      eB = impLift {X} (condFork_false P)
      eC : Deriv (imp X (eqF (ap1 Snd P) O))
      eC = impLift {X} (axSnd Z2 O)

      cf : Deriv (imp X (eqF (ap2 condFork P Z1) O))
      cf = impEqTrans {X} (ap2 condFork P Z1) (ap1 Snd P) O
             (impEqTrans {X} (ap2 condFork P Z1) (ap2 condFork P O) (ap1 Snd P) eA eB)
             eC
  in impEqTrans {X} (ap2 natEqF a b) (ap2 condFork P Z1) O (impLift {X} U) cf

factS :
  (a b : Term) ->
  Deriv (imp (eqF (ap1 isZero (ap2 sub a b)) (ap1 s O))
             (eqF (ap2 natEqF a b) (ap1 isZero (ap2 sub b a))))
factS a b =
  let Z1 : Term
      Z1 = ap1 isZero (ap2 sub a b)
      Z2 : Term
      Z2 = ap1 isZero (ap2 sub b a)
      P : Term
      P = ap2 Pair Z2 O
      X : Formula
      X = eqF Z1 (ap1 s O)
      U : Deriv (eqF (ap2 natEqF a b) (ap2 condFork P Z1))
      U = natEq_unfold_nc a b

      eZ1 : Deriv (imp X (eqF (ap2 condFork P Z1) (ap2 condFork P (ap1 s O))))
      eZ1 = impCongR {X} condFork Z1 (ap1 s O) P (identP X)
      eTrue : Deriv (imp X (eqF (ap2 condFork P (ap1 s O)) (ap1 Fst P)))
      eTrue = impLift {X} (condFork_true_univ P O)
      eFst : Deriv (imp X (eqF (ap1 Fst P) Z2))
      eFst = impLift {X} (axFst Z2 O)

      chain : Deriv (imp X (eqF (ap2 condFork P Z1) Z2))
      chain = impEqTrans {X} (ap2 condFork P Z1) (ap1 Fst P) Z2
                (impEqTrans {X} (ap2 condFork P Z1) (ap2 condFork P (ap1 s O)) (ap1 Fst P)
                            eZ1 eTrue)
                eFst
  in impEqTrans {X} (ap2 natEqF a b) (ap2 condFork P Z1) Z2 (impLift {X} U) chain

------------------------------------------------------------------------
-- SECTION 2.  isZero of a non-zero argument is  O   ( the converse of
--   isZeroSO_to_zero , via T52 + a one-case classical dispatch ).

isZero_neq_imp :
  (x : Term) ->
  Deriv (imp (neg (eqF x O)) (eqF (ap1 isZero x) O))
isZero_neq_imp x =
  let P1 : Formula
      P1 = neg (eqF x O)
      Xz : Formula
      Xz = eqF (ap1 isZero x) O
      Yz : Formula
      Yz = neg Xz

      yt52 : Deriv (imp Yz (eqF (ap1 isZero x) (ap1 s O)))
      yt52 = ruleInst 0 x T52
      yx0 : Deriv (imp Yz (eqF x O))
      yx0 = compI yt52 (ruleInst 0 x isZeroSO_to_zero)
      g : Deriv (imp Yz (imp P1 Xz))
      g = compI yx0 (axExFalso (eqF x O) Xz)
  in caseElimUnderOne {P1} {Xz} {Yz} {Xz}
        (impLift {P1} (identP Yz))
        (impLift {P1} (identP Xz))
        (impFlip g)

------------------------------------------------------------------------
-- SECTION 3.  FORWARD reflection :  natEqF a b = s O  =>  a = b .
--   One classical dispatch on  Z1 = O :  the  O -branch makes  natEqF a b = O ,
--   contradicting  s O = O ; the non- O -branch gives  Z1 = s O ( T52 ), which
--   fires the TRUE branch exposing  Z2 = s O  ; both  isZero = s O  give
--   sub a b = O  and  sub b a = O ( leq both ways ) ;  antisym_curry  concludes.

natEqF_sound :
  (a b : Term) ->
  Deriv (eqF (ap2 natEqF a b) (ap1 s O)) ->
  Deriv (eqF a b)
natEqF_sound a b H =
  let nat : Term
      nat = ap2 natEqF a b
      Z1 : Term
      Z1 = ap1 isZero (ap2 sub a b)
      Z2 : Term
      Z2 = ap1 isZero (ap2 sub b a)
      X : Formula
      X = eqF Z1 O

      czero : Deriv (imp X (eqF Z1 (ap1 s O)))
      czero = compI
                (impEqTrans {X} (ap1 s O) nat O
                   (impLift {X} (ruleSym H)) (factO a b))
                (exFalsoFromSO (eqF Z1 (ap1 s O)))
      cnz : Deriv (imp (neg X) (eqF Z1 (ap1 s O)))
      cnz = ruleInst 0 (ap2 sub a b) T52

      Z1eq : Deriv (eqF Z1 (ap1 s O))
      Z1eq = caseElim {X} {neg X} {eqF Z1 (ap1 s O)} (identP (neg X)) czero cnz

      natZ2 : Deriv (eqF nat Z2)
      natZ2 = mp (factS a b) Z1eq
      Z2eq : Deriv (eqF Z2 (ap1 s O))
      Z2eq = ruleTrans (ruleSym natZ2) H

      leqab : Deriv (leq a b)
      leqab = mp (ruleInst 0 (ap2 sub a b) isZeroSO_to_zero) Z1eq
      leqba : Deriv (leq b a)
      leqba = mp (ruleInst 0 (ap2 sub b a) isZeroSO_to_zero) Z2eq
  in mp (mp (antisym_curry a b) leqab) leqba

------------------------------------------------------------------------
-- SECTION 4.  CONTRAPOSITIVE reflection :  a /= b  =>  natEqF a b = O .
--   Outer dispatch on  Z1 = O ( caseElimUnderOne , standing hyp  a /= b ):
--     * Z1 = O   -> natEqF a b = O                       ( factO , independent )
--     * Z1 = s O -> natEqF a b = Z2 ;  leq a b ( isZeroSO_to_zero ) , so
--       antisym_curry  +  a /= b  give  ~ leq b a , i.e.  sub b a /= O , whence
--       Z2 = isZero (sub b a) = O ( isZero_neq_imp ) , so  natEqF a b = O .

natEqF_complete :
  (a b : Term) ->
  Deriv (imp (neg (eqF a b)) (eqF (ap2 natEqF a b) O))
natEqF_complete a b =
  let nat : Term
      nat = ap2 natEqF a b
      Z1 : Term
      Z1 = ap1 isZero (ap2 sub a b)
      Z2 : Term
      Z2 = ap1 isZero (ap2 sub b a)
      P1 : Formula
      P1 = neg (eqF a b)
      X : Formula
      X = eqF Z1 O
      Y : Formula
      Y = neg X

      -- Under  Y ( = Z1 /= O ) :  Z1 = s O ,  leq a b ,  nat = Z2 .
      yZ1s : Deriv (imp Y (eqF Z1 (ap1 s O)))
      yZ1s = ruleInst 0 (ap2 sub a b) T52
      yLeqab : Deriv (imp Y (leq a b))
      yLeqab = compI yZ1s (ruleInst 0 (ap2 sub a b) isZeroSO_to_zero)
      ynatZ2 : Deriv (imp Y (eqF nat Z2))
      ynatZ2 = compI yZ1s (factS a b)

      -- Under  Y :  leq b a -> a = b  ;  hence  P1 -> ~ leq b a -> Z2 = O .
      yAnti : Deriv (imp Y (imp (leq b a) (eqF a b)))
      yAnti = bComb (impLift {Y} (antisym_curry a b)) yLeqab
      yContra : Deriv (imp Y (imp P1 (neg (leq b a))))
      yContra = bComb (impLift {Y} (axContrapos (leq b a) (eqF a b))) yAnti
      yP1Z2 : Deriv (imp Y (imp P1 (eqF Z2 O)))
      yP1Z2 = app2 (impLift {Y} (impLift {P1} (isZero_neq_imp (ap2 sub b a)))) yContra

      -- Under  Y :  P1 -> nat = O   ( from  Z2 = nat  and  Z2 = O ,  via
      --   ax_eqTrans Z2 nat O :  Z2 = nat -> Z2 = O -> nat = O ).
      yZ2nat : Deriv (imp Y (eqF Z2 nat))
      yZ2nat = impRuleSym ynatZ2
      ynat2' : Deriv (imp Y (imp P1 (eqF Z2 nat)))
      ynat2' = bComb (impLift {Y} (axK (eqF Z2 nat) P1)) yZ2nat
      tEq : Deriv (imp Y (imp P1 (imp (eqF Z2 nat) (imp (eqF Z2 O) (eqF nat O)))))
      tEq = impLift {Y} (impLift {P1} (ax_eqTrans Z2 nat O))
      t2 : Deriv (imp Y (imp P1 (imp (eqF Z2 O) (eqF nat O))))
      t2 = app2 tEq ynat2'
      t3 : Deriv (imp Y (imp P1 (eqF nat O)))
      t3 = app2 t2 yP1Z2
  in caseElimUnderOne {P1} {X} {Y} {eqF nat O}
        (impLift {P1} (identP Y))
        (impLift {P1} (factO a b))
        (impFlip t3)
