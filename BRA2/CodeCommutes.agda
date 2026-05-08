{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.CodeCommutes
--
-- Spec lemma 3 of the Thm 11 gap programme (see BRA/THM11-GAP.md):
-- coding commutes with substitution, on Term/Fun1/Fun2/Formula.
--
-- Structure (mutual, because code/codeF1/codeF2 and subst/substF1/substF2
-- are all mutual):
--
--   codeCommutesT  : code of subst  = codedSubst of code    (Term)
--   codeCommutesF1 : codeF1 of substF1 = codedSubst of codeF1 (Fun1)
--   codeCommutesF2 : codeF2 of substF2 = codedSubst of codeF2 (Fun2)
--
-- Formula-level is an outer, non-mutual induction.
--
-- NOTE: this file is NOT parameterised by  th .  When applied to an
-- abstract  th , codeCommutesF1 x r th is reduction-stuck but still
-- well-typed; we simply do not call it that way inside this file.
-- Thm11Diagonal.agda handles the  th -specific transport via
-- thClosed + codeF1Th_noVar.

module BRA2.CodeCommutes where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula

------------------------------------------------------------------------
-- boolCase routing helpers

boolCaseTrue : {A : Set} (t f : A) {b : Bool} ->
               Eq b true -> Eq (boolCase b t f) t
boolCaseTrue t f refl = refl

boolCaseFalse : {A : Set} (t f : A) {b : Bool} ->
                Eq b false -> Eq (boolCase b t f) f
boolCaseFalse t f refl = refl

------------------------------------------------------------------------
-- Nat / natCode interaction

natEqSym : (n m : Nat) -> Eq (natEq n m) (natEq m n)
natEqSym zero    zero    = refl
natEqSym zero    (suc _) = refl
natEqSym (suc _) zero    = refl
natEqSym (suc n) (suc m) = natEqSym n m

natCodeEq : (n m : Nat) -> Eq (treeEq (natCode n) (natCode m)) (natEq n m)
natCodeEq zero    zero    = refl
natCodeEq zero    (suc _) = refl
natCodeEq (suc _) zero    = refl
natCodeEq (suc n) (suc m) = natCodeEq n m

-- Variant used at the var-case of codeCommutesT: after the outer tagVar
-- on both sides of treeEq reduces to true, we are left with
-- treeEq (natCode x) (natCode n), and  subst  tested on  natEq n x .
natCodeEqSwap : (x n : Nat) -> Eq (treeEq (natCode x) (natCode n)) (natEq n x)
natCodeEqSwap x n = eqTrans (natCodeEq x n) (natEqSym x n)

------------------------------------------------------------------------
-- code distributes over boolCase (at the  var n  case of codeCommutesT).

codeBoolCase : (b : Bool) (t f : Term) ->
               Eq (code (boolCase b t f)) (boolCase b (code t) (code f))
codeBoolCase true  t f = refl
codeBoolCase false t f = refl

------------------------------------------------------------------------
-- natCode has no code(var x) subtree: codedSubst passes through it.

natCode_noVar : (x : Nat) (repl : Tree) (n : Nat) ->
                Eq (codedSubst repl (code (var x)) (natCode n)) (natCode n)
natCode_noVar x repl zero    = refl
natCode_noVar x repl (suc n) =
  eqCong (nd lf) (natCode_noVar x repl n)

------------------------------------------------------------------------
-- Per-constructor "nd-passthrough" for codeF1 / codeF2 at the head of
-- an  nd .  With  f  concrete,  codeF1 f  has outer shape
--  nd (natCode k) _  where k >= 26; tagVar's outer first-child is
--  nd (nd lf lf) lf  which mismatches the  lf  first-child of
--  natCode k .  So the outer boolCase in codedSubst reduces to its
-- else branch, and the passthrough is refl.

------------------------------------------------------------------------
-- Everything below this point is wrapped in  abstract  so that the
-- proof-term bodies (which descend into closed combinator trees like
-- sub / subT / cor / stepCor, and into concrete  natCode k  values for
-- k >= 26) are not unfolded at consumer call sites.  Without  abstract ,
-- Agda's type-checker materialises a multi-gigabyte proof expression
-- when the call is at  F_pre  (which contains  ap2 sub ... ).

abstract

 codedSubst_nd_codeF1 :
   (x : Nat) (repl : Tree) (f : Fun1) (rest : Tree) ->
   Eq (codedSubst repl (code (var x)) (nd (codeF1 f) rest))
      (nd (codedSubst repl (code (var x)) (codeF1 f))
          (codedSubst repl (code (var x)) rest))
 codedSubst_nd_codeF1 x repl I              rest = refl
 codedSubst_nd_codeF1 x repl Fst            rest = refl
 codedSubst_nd_codeF1 x repl Snd            rest = refl
 codedSubst_nd_codeF1 x repl (Comp _ _)     rest = refl
 codedSubst_nd_codeF1 x repl (Comp2 _ _ _)  rest = refl
 codedSubst_nd_codeF1 x repl Z              rest = refl

 codedSubst_nd_codeF2 :
   (x : Nat) (repl : Tree) (g : Fun2) (rest : Tree) ->
   Eq (codedSubst repl (code (var x)) (nd (codeF2 g) rest))
      (nd (codedSubst repl (code (var x)) (codeF2 g))
          (codedSubst repl (code (var x)) rest))
 codedSubst_nd_codeF2 x repl Pair         rest = refl
 codedSubst_nd_codeF2 x repl Const        rest = refl
 codedSubst_nd_codeF2 x repl (Lift _)     rest = refl
 codedSubst_nd_codeF2 x repl (Post _ _)   rest = refl
 codedSubst_nd_codeF2 x repl (Fan _ _ _)  rest = refl
 codedSubst_nd_codeF2 x repl IfLf         rest = refl
 codedSubst_nd_codeF2 x repl TreeEq       rest = refl
 codedSubst_nd_codeF2 x repl (treeRec _ _) rest = refl

 ---------------------------------------------------------------------
 -- Mutual: coding commutes with substitution on Term / Fun1 / Fun2.

 codeCommutesT  : (x : Nat) (r : Term) (t : Term) ->
                  Eq (code (subst x r t))
                     (codedSubst (code r) (code (var x)) (code t))

 codeCommutesF1 : (x : Nat) (r : Term) (f : Fun1) ->
                  Eq (codeF1 (substF1 x r f))
                     (codedSubst (code r) (code (var x)) (codeF1 f))

 codeCommutesF2 : (x : Nat) (r : Term) (g : Fun2) ->
                  Eq (codeF2 (substF2 x r g))
                     (codedSubst (code r) (code (var x)) (codeF2 g))

------------------------------------------------------------------------
-- codeCommutesT

-- Case  O : both sides reduce to  nd lf lf .
 codeCommutesT x r O = refl
 
 -- Case  var n : both sides reduce to
 --   boolCase <b> (code r) (code (var n))
 -- for the same boolean b =  natEq n x  (on LHS, via boolCase of subst
 -- and codeBoolCase)  =  treeEq (natCode x) (natCode n)  (on RHS, via
 -- codedSubst unfolded, tagVar-vs-tagVar match, and natCodeEqSwap).
 codeCommutesT x r (var n) =
   let LStep : Eq (code (subst x r (var n)))
                  (boolCase (natEq n x) (code r) (code (var n)))
       LStep = codeBoolCase (natEq n x) r (var n)
 
       tvId : Eq (codedSubst (code r) (code (var x)) tagVar) tagVar
       tvId = refl
 
       ncId : Eq (codedSubst (code r) (code (var x)) (natCode n)) (natCode n)
       ncId = natCode_noVar x (code r) n
 
       elseEq : Eq (nd (codedSubst (code r) (code (var x)) tagVar)
                       (codedSubst (code r) (code (var x)) (natCode n)))
                   (code (var n))
       elseEq = eqCong2 nd tvId ncId
 
       R1 : Eq (codedSubst (code r) (code (var x)) (code (var n)))
               (boolCase (treeEq (natCode x) (natCode n))
                         (code r)
                         (nd (codedSubst (code r) (code (var x)) tagVar)
                             (codedSubst (code r) (code (var x)) (natCode n))))
       R1 = refl
 
       R2 : Eq (boolCase (treeEq (natCode x) (natCode n))
                         (code r)
                         (nd (codedSubst (code r) (code (var x)) tagVar)
                             (codedSubst (code r) (code (var x)) (natCode n))))
               (boolCase (treeEq (natCode x) (natCode n))
                         (code r)
                         (code (var n)))
       R2 = eqCong (\ e -> boolCase (treeEq (natCode x) (natCode n)) (code r) e) elseEq
 
       R3 : Eq (boolCase (treeEq (natCode x) (natCode n)) (code r) (code (var n)))
               (boolCase (natEq n x) (code r) (code (var n)))
       R3 = eqCong (\ b -> boolCase b (code r) (code (var n))) (natCodeEqSwap x n)
 
       RStep : Eq (codedSubst (code r) (code (var x)) (code (var n)))
                  (boolCase (natEq n x) (code r) (code (var n)))
       RStep = eqTrans R1 (eqTrans R2 R3)
   in eqTrans LStep (eqSym RStep)
 
 -- Case  ap1 f t : push codedSubst through  nd tagAp1 _  (refl; tagAp1
 -- mismatches tagVar) and through  nd (codeF1 f) _  (via
 -- codedSubst_nd_codeF1 ).  Combine with the F1 and T inductive
 -- hypotheses on f and t.
 codeCommutesT x r (ap1 f t) =
   let ihF : Eq (codeF1 (substF1 x r f))
                (codedSubst (code r) (code (var x)) (codeF1 f))
       ihF = codeCommutesF1 x r f
 
       ihT : Eq (code (subst x r t))
                (codedSubst (code r) (code (var x)) (code t))
       ihT = codeCommutesT x r t
 
       innerEq : Eq (nd (codeF1 (substF1 x r f)) (code (subst x r t)))
                    (nd (codedSubst (code r) (code (var x)) (codeF1 f))
                        (codedSubst (code r) (code (var x)) (code t)))
       innerEq = eqCong2 nd ihF ihT
 
       -- RHS push through outer tagAp1 and then through (codeF1 f , _).
       rhsPush :
         Eq (codedSubst (code r) (code (var x))
              (nd tagAp1 (nd (codeF1 f) (code t))))
            (nd tagAp1
                (nd (codedSubst (code r) (code (var x)) (codeF1 f))
                    (codedSubst (code r) (code (var x)) (code t))))
       rhsPush =
         eqCong (nd tagAp1)
                (codedSubst_nd_codeF1 x (code r) f (code t))
   in eqTrans (eqCong (nd tagAp1) innerEq) (eqSym rhsPush)
 
 -- Case  ap2 g a b : symmetric to  ap1 , but an extra level of  nd
 -- because  code (ap2 g a b) = nd tagAp2 (nd (codeF2 g) (nd (code a)
 -- (code b))) .  Use codedSubst_nd_codeF2 at the F2 head, and one
 -- further "nd passthrough" for the  (code a , code b)  pair (which
 -- requires no extra lemma: its outer treeEq mismatch is determined by
 -- the outer tag of  code a , which is one of tagO / tagVar / tagAp1 /
 -- tagAp2 , all mismatching tagVar's outer).  To stay uniform, we do
 -- NOT write a separate "code _ head" lemma; instead we unfold the
 -- passthrough via  eqCong2 nd ihA ihB  combined with  eqSym  of a
 -- direct  codedSubst (nd (code a) (code b)) passthrough.  The latter
 -- holds by  refl  when  code a  has concrete outer shape; since  a
 -- is here a Term whose  code  outer tag is in the set above, it does
 -- hold by  refl  per  a -constructor.  We avoid the per-constructor
 -- case split by a small combined lemma:
 --   codedSubst_nd_code : for any term  a  and Tree rest,
 --     codedSubst (code (var x)) (nd (code a) rest)
 --       passes through as  nd (codedSubst ... (code a)) (codedSubst ... rest) .
 -- Defined below.
 codeCommutesT x r (ap2 g a b) =
   let ihG : Eq (codeF2 (substF2 x r g))
                (codedSubst (code r) (code (var x)) (codeF2 g))
       ihG = codeCommutesF2 x r g
 
       ihA : Eq (code (subst x r a))
                (codedSubst (code r) (code (var x)) (code a))
       ihA = codeCommutesT x r a
 
       ihB : Eq (code (subst x r b))
                (codedSubst (code r) (code (var x)) (code b))
       ihB = codeCommutesT x r b
 
       innerAB : Eq (nd (code (subst x r a)) (code (subst x r b)))
                    (nd (codedSubst (code r) (code (var x)) (code a))
                        (codedSubst (code r) (code (var x)) (code b)))
       innerAB = eqCong2 nd ihA ihB
 
       abPush :
         Eq (codedSubst (code r) (code (var x)) (nd (code a) (code b)))
            (nd (codedSubst (code r) (code (var x)) (code a))
                (codedSubst (code r) (code (var x)) (code b)))
       abPush = codedSubst_nd_code x (code r) a (code b)
 
       innerG : Eq (nd (codeF2 (substF2 x r g))
                       (nd (code (subst x r a)) (code (subst x r b))))
                   (nd (codedSubst (code r) (code (var x)) (codeF2 g))
                       (codedSubst (code r) (code (var x))
                         (nd (code a) (code b))))
       innerG = eqCong2 nd ihG (eqTrans innerAB (eqSym abPush))
 
       rhsPush :
         Eq (codedSubst (code r) (code (var x))
              (nd tagAp2 (nd (codeF2 g) (nd (code a) (code b)))))
            (nd tagAp2
                (nd (codedSubst (code r) (code (var x)) (codeF2 g))
                    (codedSubst (code r) (code (var x))
                      (nd (code a) (code b)))))
       rhsPush =
         eqCong (nd tagAp2)
                (codedSubst_nd_codeF2 x (code r) g (nd (code a) (code b)))
   in eqTrans (eqCong (nd tagAp2) innerG) (eqSym rhsPush)
   where
     -- codedSubst_nd_code: codedSubst passes through  nd (code a) rest .
     -- Case-splits on  a  to expose the outer tag of  code a .
     codedSubst_nd_code :
       (x : Nat) (repl : Tree) (a : Term) (rest : Tree) ->
       Eq (codedSubst repl (code (var x)) (nd (code a) rest))
          (nd (codedSubst repl (code (var x)) (code a))
              (codedSubst repl (code (var x)) rest))
     codedSubst_nd_code x repl O         rest = refl
     codedSubst_nd_code x repl (var n)   rest = refl
     codedSubst_nd_code x repl (ap1 _ _) rest = refl
     codedSubst_nd_code x repl (ap2 _ _ _) rest = refl
 
 ------------------------------------------------------------------------
 -- codeCommutesF1
 
 codeCommutesF1 x r I   = refl
 codeCommutesF1 x r Fst = refl
 codeCommutesF1 x r Snd = refl
 
 codeCommutesF1 x r (Comp f g) =
   eqCong2 nd refl
     (eqTrans (eqCong2 nd (codeCommutesF1 x r f) (codeCommutesF1 x r g))
              (eqSym (codedSubst_nd_codeF1 x (code r) f (codeF1 g))))
 
 codeCommutesF1 x r (Comp2 h f g) =
   let ihH : Eq (codeF2 (substF2 x r h))
                (codedSubst (code r) (code (var x)) (codeF2 h))
       ihH = codeCommutesF2 x r h
       ihF : Eq (codeF1 (substF1 x r f))
                (codedSubst (code r) (code (var x)) (codeF1 f))
       ihF = codeCommutesF1 x r f
       ihG : Eq (codeF1 (substF1 x r g))
                (codedSubst (code r) (code (var x)) (codeF1 g))
       ihG = codeCommutesF1 x r g
 
       innerFG :
         Eq (nd (codeF1 (substF1 x r f)) (codeF1 (substF1 x r g)))
            (codedSubst (code r) (code (var x)) (nd (codeF1 f) (codeF1 g)))
       innerFG =
         eqTrans (eqCong2 nd ihF ihG)
                 (eqSym (codedSubst_nd_codeF1 x (code r) f (codeF1 g)))
 
       innerH :
         Eq (nd (codeF2 (substF2 x r h))
                (nd (codeF1 (substF1 x r f)) (codeF1 (substF1 x r g))))
            (codedSubst (code r) (code (var x))
              (nd (codeF2 h) (nd (codeF1 f) (codeF1 g))))
       innerH =
         eqTrans (eqCong2 nd ihH innerFG)
                 (eqSym (codedSubst_nd_codeF2 x (code r) h
                          (nd (codeF1 f) (codeF1 g))))
   in eqCong2 nd refl innerH
 
 codeCommutesF1 x r Z = refl
 
 ------------------------------------------------------------------------
 -- codeCommutesF2
 
 codeCommutesF2 x r Pair   = refl
 codeCommutesF2 x r Const  = refl
 codeCommutesF2 x r IfLf   = refl
 codeCommutesF2 x r TreeEq = refl
 
 codeCommutesF2 x r (Lift f) =
   eqCong2 nd refl (codeCommutesF1 x r f)
 
 codeCommutesF2 x r (Post f h) =
   let ihF = codeCommutesF1 x r f
       ihH = codeCommutesF2 x r h
       inner :
         Eq (nd (codeF1 (substF1 x r f)) (codeF2 (substF2 x r h)))
            (codedSubst (code r) (code (var x)) (nd (codeF1 f) (codeF2 h)))
       inner =
         eqTrans (eqCong2 nd ihF ihH)
                 (eqSym (codedSubst_nd_codeF1 x (code r) f (codeF2 h)))
   in eqCong2 nd refl inner
 
 codeCommutesF2 x r (Fan h1 h2 h) =
   let ih1 = codeCommutesF2 x r h1
       ih2 = codeCommutesF2 x r h2
       ihH = codeCommutesF2 x r h
 
       inner23 :
         Eq (nd (codeF2 (substF2 x r h2)) (codeF2 (substF2 x r h)))
            (codedSubst (code r) (code (var x)) (nd (codeF2 h2) (codeF2 h)))
       inner23 =
         eqTrans (eqCong2 nd ih2 ihH)
                 (eqSym (codedSubst_nd_codeF2 x (code r) h2 (codeF2 h)))
 
       inner1 :
         Eq (nd (codeF2 (substF2 x r h1))
                (nd (codeF2 (substF2 x r h2)) (codeF2 (substF2 x r h))))
            (codedSubst (code r) (code (var x))
              (nd (codeF2 h1) (nd (codeF2 h2) (codeF2 h))))
       inner1 =
         eqTrans (eqCong2 nd ih1 inner23)
                 (eqSym (codedSubst_nd_codeF2 x (code r) h1
                          (nd (codeF2 h2) (codeF2 h))))
   in eqCong2 nd refl inner1
 
 -- treeRec f s: encoded as  nd tag (nd (codeF1 f) (codeF2 s)) , parallel
 -- to  Post f h .  Inner level-1  nd (codeF1 f) (codeF2 s)  pushes via
 -- codedSubst_nd_codeF1 ; F1 + F2 IHs supply the inner equalities.
 codeCommutesF2 x r (treeRec f s) =
   let ihF = codeCommutesF1 x r f
       ihS = codeCommutesF2 x r s
       inner :
         Eq (nd (codeF1 (substF1 x r f)) (codeF2 (substF2 x r s)))
            (codedSubst (code r) (code (var x)) (nd (codeF1 f) (codeF2 s)))
       inner =
         eqTrans (eqCong2 nd ihF ihS)
                 (eqSym (codedSubst_nd_codeF1 x (code r) f (codeF2 s)))
   in eqCong2 nd refl inner
 
 ------------------------------------------------------------------------
 -- Outer: codeCommutes on Formula.
 
 codeCommutesEq : (x : Nat) (r : Term) (e : Equation) ->
                  Eq (codeEqn (substEq x r e))
                     (codedSubst (code r) (code (var x)) (codeEqn e))
 codeCommutesEq x r (eqn l rr) =
   let ihL = codeCommutesT x r l
       ihR = codeCommutesT x r rr
   in eqTrans (eqCong2 nd ihL ihR)
              (eqSym (codedSubst_nd_code_outer x (code r) l (code rr)))
   where
     -- Like the helpers above: pass codedSubst through  nd (code l) _
     -- by case on l's outer tag.
     codedSubst_nd_code_outer :
       (x : Nat) (repl : Tree) (t : Term) (rest : Tree) ->
       Eq (codedSubst repl (code (var x)) (nd (code t) rest))
          (nd (codedSubst repl (code (var x)) (code t))
              (codedSubst repl (code (var x)) rest))
     codedSubst_nd_code_outer x repl O           rest = refl
     codedSubst_nd_code_outer x repl (var n)     rest = refl
     codedSubst_nd_code_outer x repl (ap1 _ _)   rest = refl
     codedSubst_nd_code_outer x repl (ap2 _ _ _) rest = refl
 
 codeCommutesFormula : (x : Nat) (r : Term) (F : Formula) ->
                       Eq (codeFormula (substF x r F))
                          (codedSubst (code r) (code (var x)) (codeFormula F))
 codeCommutesFormula x r (atomic e) = codeCommutesEq x r e
 codeCommutesFormula x r (not P) =
   eqCong2 nd refl (codeCommutesFormula x r P)
 codeCommutesFormula x r (P imp Q) =
   let ihP = codeCommutesFormula x r P
       ihQ = codeCommutesFormula x r Q
 
       inner :
         Eq (nd (codeFormula (substF x r P)) (codeFormula (substF x r Q)))
            (codedSubst (code r) (code (var x))
              (nd (codeFormula P) (codeFormula Q)))
       inner =
         eqTrans (eqCong2 nd ihP ihQ)
                 (eqSym (codedSubst_nd_codeF_pair x (code r) P (codeFormula Q)))
   in eqCong2 nd refl inner
   where
     -- codedSubst passes through  nd (codeFormula P) rest .  Case on P's
     -- outer tag: atomic -> codeEqn -> nd (code _) _, with the code-outer
     -- tag in {tagO,tagVar,tagAp1,tagAp2}; not -> tagNeg; imp -> tagImp.
     -- All four outer tags mismatch tagVar, so the passthrough is refl
     -- after case-splitting on P.
     codedSubst_nd_codeF_pair :
       (x : Nat) (repl : Tree) (P : Formula) (rest : Tree) ->
       Eq (codedSubst repl (code (var x)) (nd (codeFormula P) rest))
          (nd (codedSubst repl (code (var x)) (codeFormula P))
              (codedSubst repl (code (var x)) rest))
     codedSubst_nd_codeF_pair x repl (atomic (eqn O           _)) rest = refl
     codedSubst_nd_codeF_pair x repl (atomic (eqn (var _)     _)) rest = refl
     codedSubst_nd_codeF_pair x repl (atomic (eqn (ap1 _ _)   _)) rest = refl
     codedSubst_nd_codeF_pair x repl (atomic (eqn (ap2 _ _ _) _)) rest = refl
     codedSubst_nd_codeF_pair x repl (not (atomic (eqn _ _)))     rest = refl
     codedSubst_nd_codeF_pair x repl (not (not _))                rest = refl
     codedSubst_nd_codeF_pair x repl (not (_ imp _))              rest = refl
     codedSubst_nd_codeF_pair x repl (_ imp _)                    rest = refl
