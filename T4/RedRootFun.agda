{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.RedRootFun -- STAGE I2 of attempt3 §11, the ITERABLE form of the
-- toy TRS's root contraction.
--
-- T4.StepObj gave the root contraction as a META-combinator
-- (devRootExpr : Term -> Term).  For the Church-Rosser internalisation
-- we want reduction to be driven by a single OBJECT function iterated on
-- a fuel counter (the  iter  pattern of T4.EvalU / BRA3.CourseOfValues:
-- `ap2 (iter f) x O = x`, `ap2 (iter f) x (s n) = f (ap2 (iter f) x n)`).
-- That pattern is TERMINATION-FREE and avoids the heavy course-of-values
-- (cov_spec) lookup machinery: a complete development / reduction step is
-- a NON-RECURSIVE combinator, multistep is fuel iteration, and an  E
-- (object existential) over the fuel supplies the reduction witness.
--
-- This file builds the contraction as a genuine  Fun1 :
--     redRoot : Fun1
-- using the conditional-Fun1 kit  fork / fireT / fireF  of T4.EvalUStep
-- (the same kit  stepU  is built from).  It DISPATCHES on the head tag
-- of an ad#-node's first subterm via  eqAtT 1 / condFork  and contracts:
--     redRoot (ad# ze# y)      = y                  (object rO)
--     redRoot (ad# (su# x) y)  = su# (ad# x y)      (object rS)
-- NB this is the HEAD contractor (the redex the CK reduction machine
-- fires); it does NOT descend into subterms -- descent is the
-- continuation-stack layer (templated on T4.EvalU), the next stage.
--
-- Proved from  fork/fireT/fireF + compose1U_eq + eqAtT + the TrsCodeObj
-- projection equations.  No induction, no postulates, no holes.

module T4.RedRootFun where

open import T4.Base
open import T4.TrsCodeObj
open import T4.EvalUStep using ( fork ; fireT ; fireF )
open import BRA3.Fan      using ( compose1U_eq )
open import BRA3.Dispatch using ( eqAtT ; eqAtT_match ; eqAtT_above )
open import BRA3.CourseOfValues using ( iter ; iter_base ; iter_step )

------------------------------------------------------------------------
-- Field-extractor Fun1's (universal composition  compose1U f g  with
-- closure  compose1U_eq : (compose1U f g) x = f (g x) ).
--
--   g1 t = Snd (Fst (Snd t))   -- ar of the first subterm,
--   g2 t = Snd (Snd t)         -- the second subterm  (= secondArg),
--   hdFirst t = Fst (Fst (Snd t)) -- head tag of the first subterm.

g1 : Fun1
g1 = compose1U Snd (compose1U Fst Snd)

g2 : Fun1
g2 = compose1U Snd Snd

hdFirst : Fun1
hdFirst = compose1U Fst (compose1U Fst Snd)

-- The conditional flag:  eqAtT 1  applied to the first subterm's head
-- tag  ( = s O iff that tag >= 1, i.e. the first subterm is su#).
flag : Fun1
flag = compose1U (eqAtT 1) hdFirst

-- The two branches.
--   trueB t  = su# (ad# (g1 t) (g2 t))   -- the rS contractum,
--   falseB t = g2 t  (= secondArg t)     -- the rO contractum.

trueB : Fun1
trueB = C Pair (constN 1) (C Pair (constN 2) (C Pair g1 g2))

falseB : Fun1
falseB = g2

redRoot : Fun1
redRoot = fork trueB falseB flag

------------------------------------------------------------------------
-- Flag evaluation at the two redex shapes.

-- At  ad# (su# x) y :  flag = s O  (su head, tag 1).
flag_rS : (x y : Term) -> Deriv (eqF (ap1 flag (ad# (su# x) y)) (ap1 s O))
flag_rS x y =
  let t : Term
      t = ad# (su# x) y

      -- hdFirst t = Fst (Fst (Snd t)) = head tag of firstArg = tagSu.
      eHd : Deriv (eqF (ap1 hdFirst t) tagSu)
      eHd =
        ruleTrans (compose1U_eq Fst (compose1U Fst Snd) t)
          (ruleTrans (cong1 Fst (compose1U_eq Fst Snd t))
            (ruleTrans (cong1 Fst (ad1 (su# x) y)) (hd_su x)))
  in ruleTrans (compose1U_eq (eqAtT 1) hdFirst t)
       (ruleTrans (cong1 (eqAtT 1) eHd) (eqAtT_match 1))

-- At  ad# ze# y :  flag = O  (ze head, tag 0).
flag_rO : (y : Term) -> Deriv (eqF (ap1 flag (ad# ze# y)) O)
flag_rO y =
  let t : Term
      t = ad# ze# y

      eHd : Deriv (eqF (ap1 hdFirst t) tagZe)
      eHd =
        ruleTrans (compose1U_eq Fst (compose1U Fst Snd) t)
          (ruleTrans (cong1 Fst (compose1U_eq Fst Snd t))
            (ruleTrans (cong1 Fst (ad1 ze# y)) hd_ze))
  in ruleTrans (compose1U_eq (eqAtT 1) hdFirst t)
       (ruleTrans (cong1 (eqAtT 1) eHd) (eqAtT_above 0 0))

------------------------------------------------------------------------
-- rO :  redRoot (ad# ze# y)  =  y .

redRoot_rO : (y : Term) -> Deriv (eqF (ap1 redRoot (ad# ze# y)) y)
redRoot_rO y =
  let t : Term
      t = ad# ze# y

      sel : Deriv (eqF (ap1 redRoot t) (ap1 falseB t))
      sel = fireF trueB falseB flag t (flag_rO y)

      -- falseB t = g2 t = Snd (Snd t) = secondArg = y.
      eB : Deriv (eqF (ap1 falseB t) y)
      eB = ruleTrans (compose1U_eq Snd Snd t) (ad2 ze# y)
  in ruleTrans sel eB

------------------------------------------------------------------------
-- rS :  redRoot (ad# (su# x) y)  =  su# (ad# x y) .

redRoot_rS :
  (x y : Term) ->
  Deriv (eqF (ap1 redRoot (ad# (su# x) y)) (su# (ad# x y)))
redRoot_rS x y =
  let t : Term
      t = ad# (su# x) y

      sel : Deriv (eqF (ap1 redRoot t) (ap1 trueB t))
      sel = fireT trueB falseB flag t (flag_rS x y)

      -- g1 t = Snd (Fst (Snd t)) = Snd (firstArg t) = Snd (su# x) = x.
      eg1 : Deriv (eqF (ap1 g1 t) x)
      eg1 =
        ruleTrans (compose1U_eq Snd (compose1U Fst Snd) t)
          (ruleTrans (cong1 Snd (compose1U_eq Fst Snd t))
            (ruleTrans (cong1 Snd (ad1 (su# x) y)) (ar_su x)))

      -- g2 t = Snd (Snd t) = secondArg = y.
      eg2 : Deriv (eqF (ap1 g2 t) y)
      eg2 = ruleTrans (compose1U_eq Snd Snd t) (ad2 (su# x) y)

      -- Unfold  trueB t  =  Pair tagSu (Pair tagAd (Pair (g1 t) (g2 t))).
      eUnfold :
        Deriv (eqF (ap1 trueB t)
                   (ap2 Pair tagSu
                        (ap2 Pair tagAd (ap2 Pair (ap1 g1 t) (ap1 g2 t)))))
      eUnfold =
        ruleTrans (ax_C Pair (constN 1) (C Pair (constN 2) (C Pair g1 g2)) t)
          (ruleTrans (congL Pair (ap1 (C Pair (constN 2) (C Pair g1 g2)) t)
                              (constN_eq 1 t))
            (congR Pair tagSu
              (ruleTrans (ax_C Pair (constN 2) (C Pair g1 g2) t)
                (ruleTrans (congL Pair (ap1 (C Pair g1 g2) t) (constN_eq 2 t))
                  (congR Pair tagAd (ax_C Pair g1 g2 t))))))

      -- Rewrite the inner pair  Pair (g1 t) (g2 t)  to  Pair x y .
      eInner : Deriv (eqF (ap2 Pair (ap1 g1 t) (ap1 g2 t)) (ap2 Pair x y))
      eInner = ruleTrans (congL Pair (ap1 g2 t) eg1) (congR Pair x eg2)

      eVal : Deriv (eqF (ap2 Pair tagSu
                            (ap2 Pair tagAd (ap2 Pair (ap1 g1 t) (ap1 g2 t))))
                        (su# (ad# x y)))
      eVal = congR Pair tagSu (congR Pair tagAd eInner)
  in ruleTrans sel (ruleTrans eUnfold eVal)

------------------------------------------------------------------------
-- Architecture demonstration: ONE fuel-iteration step of  redRoot
-- performs the root contraction.  This is the  iter  pattern in action
--   ( ap2 (iter f) x (s O) = f (ap2 (iter f) x O) = f x ) ,
-- the termination-free vehicle for the reduction relation.

iter_rO_oneStep :
  (y : Term) -> Deriv (eqF (ap2 (iter redRoot) (ad# ze# y) (ap1 s O)) y)
iter_rO_oneStep y =
  let t : Term
      t = ad# ze# y

      st : Deriv (eqF (ap2 (iter redRoot) t (ap1 s O))
                      (ap1 redRoot (ap2 (iter redRoot) t O)))
      st = iter_step redRoot t O closed_O

      bs : Deriv (eqF (ap1 redRoot (ap2 (iter redRoot) t O)) (ap1 redRoot t))
      bs = cong1 redRoot (iter_base redRoot t)
  in ruleTrans st (ruleTrans bs (redRoot_rO y))

iter_rS_oneStep :
  (x y : Term) ->
  Deriv (eqF (ap2 (iter redRoot) (ad# (su# x) y) (ap1 s O)) (su# (ad# x y)))
iter_rS_oneStep x y =
  let t : Term
      t = ad# (su# x) y

      st : Deriv (eqF (ap2 (iter redRoot) t (ap1 s O))
                      (ap1 redRoot (ap2 (iter redRoot) t O)))
      st = iter_step redRoot t O closed_O

      bs : Deriv (eqF (ap1 redRoot (ap2 (iter redRoot) t O)) (ap1 redRoot t))
      bs = cong1 redRoot (iter_base redRoot t)
  in ruleTrans st (ruleTrans bs (redRoot_rS x y))
