{-# OPTIONS --safe --without-K --exact-split #-}

-- Schematic lemma: double substitution on thFunTFor replaces the embedded
-- substTFor (in case23) with closedSubstTFor.
-- No computation on crTC. Only substReify on natCode v1 (2 nodes).

module Guard.ThFunTForSubst where

open import Guard.Base
open import Guard.Term
open import Guard.ThFunTForDefs
open import Guard.ThFunTForCases0
open import Guard.ThFunTForCases1
open import Guard.ThFunTForCases2
open import Guard.ThFunTForCases3
open import Guard.ThFunTFor
open import Guard.SubstTFor using (substTFor)
open import Guard.SubstTForCorrect using (closedSubstTFor)
open import Guard.SubstTForClose

private
  v11 : Nat
  v11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  v12 : Nat
  v12 = suc v11

  -- case23 after double subst: substTFor -> closedSubstTFor
  case23Closed : (replT tgtT : Tree) -> Fun2
  case23Closed replT tgtT =
    mkEqF (Post (closedSubstTFor (reify replT) (reify tgtT)) recsBL)
          (Post (closedSubstTFor (reify replT) (reify tgtT)) recsBR)

  case23Eq : (replT tgtT : Tree) ->
    Eq (substF2 v11 (reify replT) (substF2 v12 (reify tgtT) case23))
       (case23Closed replT tgtT)
  case23Eq replT tgtT =
    eqCong2 (\f g -> mkEqF (Post f recsBL) (Post g recsBR))
            (substTForClose replT tgtT)
            (substTForClose replT tgtT)

  -- Propagate through branch chain: if rest changes, branch propagates
  branchRestEq : (n : Nat) (c : Fun2) {r1 r2 : Fun2} ->
    Eq r1 r2 -> Eq (branch (tagCheck n) c r1) (branch (tagCheck n) c r2)
  branchRestEq n c p = eqCong (\r -> Fan (tagCheck n) (Fan c r Pair) IfLf) p

  -- ndT23 after double subst
  ndT23Eq : (replT tgtT : Tree) ->
    Eq (substF2 v11 (reify replT) (substF2 v12 (reify tgtT) ndT23))
       (branch (tagCheck (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) (case23Closed replT tgtT) ndT24)
  ndT23Eq replT tgtT =
    eqCong (\c -> Fan (tagCheck (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))
                      (Fan c ndT24 Pair) IfLf)
           (case23Eq replT tgtT)

  -- Chain from ndT23 up to ndDispatch: 23 levels of branchRestEq
  -- ndT22 = branch 22 case22 ndT23
  -- ndT21 = branch 21 case21 ndT22
  -- ...
  -- ndT0 = ndDispatch = branch 0 case0 ndT1

  -- I'll define the nat abbreviations locally
  ln0  : Nat ; ln0  = zero
  ln1  : Nat ; ln1  = suc ln0
  ln2  : Nat ; ln2  = suc ln1
  ln3  : Nat ; ln3  = suc ln2
  ln4  : Nat ; ln4  = suc ln3
  ln5  : Nat ; ln5  = suc ln4
  ln6  : Nat ; ln6  = suc ln5
  ln7  : Nat ; ln7  = suc ln6
  ln8  : Nat ; ln8  = suc ln7
  ln9  : Nat ; ln9  = suc ln8
  ln10 : Nat ; ln10 = suc ln9
  ln11 : Nat ; ln11 = suc ln10
  ln12 : Nat ; ln12 = suc ln11
  ln13 : Nat ; ln13 = suc ln12
  ln14 : Nat ; ln14 = suc ln13
  ln15 : Nat ; ln15 = suc ln14
  ln16 : Nat ; ln16 = suc ln15
  ln17 : Nat ; ln17 = suc ln16
  ln18 : Nat ; ln18 = suc ln17
  ln19 : Nat ; ln19 = suc ln18
  ln20 : Nat ; ln20 = suc ln19
  ln21 : Nat ; ln21 = suc ln20
  ln22 : Nat ; ln22 = suc ln21
  ln23 : Nat ; ln23 = suc ln22
  ln24 : Nat ; ln24 = suc ln23
  ln25 : Nat ; ln25 = suc ln24

  -- Propagate ndT23Eq up to ndDispatch
  ndDispatchEq : (replT tgtT : Tree) ->
    Eq (substF2 v11 (reify replT) (substF2 v12 (reify tgtT) ndDispatch))
       (branch (tagCheck ln0) case0
       (branch (tagCheck ln1) case1
       (branch (tagCheck ln2) case2
       (branch (tagCheck ln3) case3
       (branch (tagCheck ln4) case4
       (branch (tagCheck ln5) case5
       (branch (tagCheck ln6) case6
       (branch (tagCheck ln7) case7
       (branch (tagCheck ln8) case8
       (branch (tagCheck ln9) case9
       (branch (tagCheck ln10) case10
       (branch (tagCheck ln11) case11
       (branch (tagCheck ln12) case12
       (branch (tagCheck ln13) case13
       (branch (tagCheck ln14) case14
       (branch (tagCheck ln15) case15
       (branch (tagCheck ln16) case16
       (branch (tagCheck ln17) case17
       (branch (tagCheck ln18) case18
       (branch (tagCheck ln19) case19
       (branch (tagCheck ln20) case20
       (branch (tagCheck ln21) case21
       (branch (tagCheck ln22) case22
       (branch (tagCheck ln23) (case23Closed replT tgtT)
       ndT24))))))))))))))))))))))))
  ndDispatchEq replT tgtT =
    branchRestEq ln0 case0
    (branchRestEq ln1 case1
    (branchRestEq ln2 case2
    (branchRestEq ln3 case3
    (branchRestEq ln4 case4
    (branchRestEq ln5 case5
    (branchRestEq ln6 case6
    (branchRestEq ln7 case7
    (branchRestEq ln8 case8
    (branchRestEq ln9 case9
    (branchRestEq ln10 case10
    (branchRestEq ln11 case11
    (branchRestEq ln12 case12
    (branchRestEq ln13 case13
    (branchRestEq ln14 case14
    (branchRestEq ln15 case15
    (branchRestEq ln16 case16
    (branchRestEq ln17 case17
    (branchRestEq ln18 case18
    (branchRestEq ln19 case19
    (branchRestEq ln20 case20
    (branchRestEq ln21 case21
    (branchRestEq ln22 case22
    (ndT23Eq replT tgtT)))))))))))))))))))))))

------------------------------------------------------------------------
-- Main result: double subst on thFunTFor

thFunTForSubst : (replT tgtT : Tree) ->
  Eq (substF1 v11 (reify replT) (substF1 v12 (reify tgtT) thFunTFor))
     (Rec O
       (Fan dataIsLf
            (Fan lfDispatch
                 (branch (tagCheck ln0) case0
                 (branch (tagCheck ln1) case1
                 (branch (tagCheck ln2) case2
                 (branch (tagCheck ln3) case3
                 (branch (tagCheck ln4) case4
                 (branch (tagCheck ln5) case5
                 (branch (tagCheck ln6) case6
                 (branch (tagCheck ln7) case7
                 (branch (tagCheck ln8) case8
                 (branch (tagCheck ln9) case9
                 (branch (tagCheck ln10) case10
                 (branch (tagCheck ln11) case11
                 (branch (tagCheck ln12) case12
                 (branch (tagCheck ln13) case13
                 (branch (tagCheck ln14) case14
                 (branch (tagCheck ln15) case15
                 (branch (tagCheck ln16) case16
                 (branch (tagCheck ln17) case17
                 (branch (tagCheck ln18) case18
                 (branch (tagCheck ln19) case19
                 (branch (tagCheck ln20) case20
                 (branch (tagCheck ln21) case21
                 (branch (tagCheck ln22) case22
                 (branch (tagCheck ln23) (case23Closed replT tgtT)
                 ndT24))))))))))))))))))))))))
                 Pair)
            IfLf))
thFunTForSubst replT tgtT =
  eqCong (\d -> Rec O (Fan dataIsLf (Fan lfDispatch d Pair) IfLf))
         (ndDispatchEq replT tgtT)

-- Named export: the closed thFunTFor
thFunTForClosed : Tree -> Tree -> Fun1
thFunTForClosed replT tgtT =
  Rec O
    (Fan dataIsLf
         (Fan lfDispatch
              (branch (tagCheck ln0) case0
              (branch (tagCheck ln1) case1
              (branch (tagCheck ln2) case2
              (branch (tagCheck ln3) case3
              (branch (tagCheck ln4) case4
              (branch (tagCheck ln5) case5
              (branch (tagCheck ln6) case6
              (branch (tagCheck ln7) case7
              (branch (tagCheck ln8) case8
              (branch (tagCheck ln9) case9
              (branch (tagCheck ln10) case10
              (branch (tagCheck ln11) case11
              (branch (tagCheck ln12) case12
              (branch (tagCheck ln13) case13
              (branch (tagCheck ln14) case14
              (branch (tagCheck ln15) case15
              (branch (tagCheck ln16) case16
              (branch (tagCheck ln17) case17
              (branch (tagCheck ln18) case18
              (branch (tagCheck ln19) case19
              (branch (tagCheck ln20) case20
              (branch (tagCheck ln21) case21
              (branch (tagCheck ln22) case22
              (branch (tagCheck ln23) (case23Closed replT tgtT)
              ndT24))))))))))))))))))))))))
              Pair)
         IfLf)

thFunTForSubstEq : (replT tgtT : Tree) ->
  Eq (substF1 v11 (reify replT) (substF1 v12 (reify tgtT) thFunTFor))
     (thFunTForClosed replT tgtT)
thFunTForSubstEq replT tgtT = thFunTForSubst replT tgtT
