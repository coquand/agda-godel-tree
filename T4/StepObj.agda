{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.StepObj -- STAGE I2 of attempt3 §11 (internalising CR in BRA),
-- FIRST PART: the object form of the toy TRS's ROOT reduction.
--
-- The toy TRS (cf. T4.ChurchRosserProto) has two root rules
--     rO :  ad ze     y  ->  y
--     rS :  ad (su x) y  ->  su (ad x y)
-- and the congruence closure (cSu / cA1 / cA2).  This file internalises
-- the COMPUTATIONAL HEART -- the root contraction -- as an OBJECT
-- function on the Goedel codes of T4.TrsCodeObj, with its two defining
-- equations proved as  Deriv .  This is the object analog of
-- ChurchRosserProto's  rO / rS  (the redex contractions that the
-- parallel-reduction relation  Par  is built from).
--
-- Design (mirrors BRA3.Dispatch's meta-combinator + condFork method):
--   devRootExpr : Term -> Term      -- given the code of an  ad#-node,
--                                      returns the code of its root
--                                      contractum.
-- It DISPATCHES on the head tag of the node's first subterm:
--   * tag 0 (ze) -> the ze-rule  rO , result = second subterm ;
--   * tag 1 (su) -> the su-rule  rS , result = su# (ad# (ar firstArg) snd).
-- The tag test is the project's  eqAtT  ("1 <= head tag"); the branch
-- selection is the project's  condFork  ("if-then-else").
--
-- NO induction (ruleIndNat) yet: root contraction is non-recursive.
-- The full one-step / parallel relations  stepCh / parCh  (with
-- congruence + course-of-values recursion via cov_spec) and the
-- complete-development  devF  (I3) build on this substrate.
--
-- Everything is proved from  axFst / axSnd  (Pair algebra),  condFork
-- and  eqAtT  closure lemmas -- no postulates, no holes.

module T4.StepObj where

open import T4.Base
open import T4.TrsCodeObj
open import BRA3.Dispatch using ( eqAtT ; eqAtT_match ; eqAtT_above )

------------------------------------------------------------------------
-- Structural accessors for an  ad#-node  t = ad# a b  (object Terms).
--
--   firstArg  t = Fst (Snd t)   -- the code  a  of the first subterm,
--   secondArg t = Snd (Snd t)   -- the code  b  of the second subterm,
--   hdArg     t = Fst (firstArg t) = head tag of the first subterm.
--
-- (For  t = ad# a b  these reduce, by  ad1 / ad2 , to  a / b .)

firstArg : Term -> Term
firstArg t = ap1 Fst (ap1 Snd t)

secondArg : Term -> Term
secondArg t = ap1 Snd (ap1 Snd t)

hdArg : Term -> Term
hdArg t = ap1 Fst (firstArg t)

------------------------------------------------------------------------
-- The two branches and the conditional bit.

-- su-branch  =  su# (ad# (ar firstArg) secondArg)  -- the rS contractum.
suBr : Term -> Term
suBr t = su# (ad# (ap1 Snd (firstArg t)) (secondArg t))

-- condBit t = O  iff  head tag of firstArg < 1   (i.e. firstArg is ze),
--           = s O iff  head tag of firstArg >= 1 (i.e. firstArg is su).
condBit : Term -> Term
condBit t = ap1 (eqAtT 1) (hdArg t)

------------------------------------------------------------------------
-- The object root-contraction.
--
--   devRootExpr t = condFork (Pair (suBr t) (secondArg t)) (condBit t)
--
-- condFork z (s _) = Fst z = suBr t      (su head -> rS),
-- condFork z  O    = Snd z = secondArg t (ze head -> rO).

devRootExpr : Term -> Term
devRootExpr t =
  ap2 condFork (ap2 Pair (suBr t) (secondArg t)) (condBit t)

------------------------------------------------------------------------
-- Head-tag recognizer  isAdBit  -- the redex guard.
--
--   isAdBit t = s O  iff  head tag of t  >= 2  (i.e. t is an ad#-node),
--             = O    iff  head tag of t  <  2  (ze# or su#).
-- This gates  devRootExpr  (which is only meaningful on ad#-nodes); the
-- forthcoming  parCh  dispatch reuses it.

isAdBit : Term -> Term
isAdBit t = ap1 (eqAtT 2) (hd t)

isAdBit_ze : Deriv (eqF (isAdBit ze#) O)
isAdBit_ze = ruleTrans (cong1 (eqAtT 2) hd_ze) (eqAtT_above 1 0)

isAdBit_su : (t : Term) -> Deriv (eqF (isAdBit (su# t)) O)
isAdBit_su t = ruleTrans (cong1 (eqAtT 2) (hd_su t)) (eqAtT_above 0 1)

isAdBit_ad : (a b : Term) -> Deriv (eqF (isAdBit (ad# a b)) (ap1 s O))
isAdBit_ad a b = ruleTrans (cong1 (eqAtT 2) (hd_ad a b)) (eqAtT_match 2)

------------------------------------------------------------------------
-- rO :  devRootExpr (ad# ze# y)  =  y .

devRoot_rO : (y : Term) -> Deriv (eqF (devRootExpr (ad# ze# y)) y)
devRoot_rO y =
  let t : Term
      t = ad# ze# y

      z : Term
      z = ap2 Pair (suBr t) (secondArg t)

      -- firstArg t  =  ze#  (the coded first subterm).
      eA0 : Deriv (eqF (firstArg t) ze#)
      eA0 = ad1 ze# y

      -- head tag of firstArg  =  tagZe.
      eHd0 : Deriv (eqF (hdArg t) tagZe)
      eHd0 = ruleTrans (cong1 Fst eA0) hd_ze

      -- condBit t  =  O  (ze branch selected): eqAtT 1 (natCode 0) = O.
      eCond0 : Deriv (eqF (condBit t) O)
      eCond0 = ruleTrans (cong1 (eqAtT 1) eHd0) (eqAtT_above 0 0)

      -- condFork z O  =  Snd z  =  secondArg t.
      chain1 : Deriv (eqF (devRootExpr t) (secondArg t))
      chain1 =
        ruleTrans (congR condFork z eCond0)
          (ruleTrans (condFork_false z)
                     (axSnd (suBr t) (secondArg t)))

      -- secondArg (ad# ze# y)  =  y.
      eB0 : Deriv (eqF (secondArg t) y)
      eB0 = ad2 ze# y
  in ruleTrans chain1 eB0

------------------------------------------------------------------------
-- rS :  devRootExpr (ad# (su# x) y)  =  su# (ad# x y) .

devRoot_rS :
  (x y : Term) ->
  Deriv (eqF (devRootExpr (ad# (su# x) y)) (su# (ad# x y)))
devRoot_rS x y =
  let t : Term
      t = ad# (su# x) y

      z : Term
      z = ap2 Pair (suBr t) (secondArg t)

      -- firstArg t  =  su# x.
      eA : Deriv (eqF (firstArg t) (su# x))
      eA = ad1 (su# x) y

      -- head tag of firstArg  =  tagSu.
      eHd : Deriv (eqF (hdArg t) tagSu)
      eHd = ruleTrans (cong1 Fst eA) (hd_su x)

      -- condBit t  =  s O  (su branch selected): eqAtT 1 (natCode 1) = s O.
      eCond : Deriv (eqF (condBit t) (ap1 s O))
      eCond = ruleTrans (cong1 (eqAtT 1) eHd) (eqAtT_match 1)

      -- condFork z (s O)  =  Fst z  =  suBr t.
      chain1 : Deriv (eqF (devRootExpr t) (suBr t))
      chain1 =
        ruleTrans (congR condFork z eCond)
          (ruleTrans (condFork_true_nc z O)
                     (axFst (suBr t) (secondArg t)))

      -- Now reduce  suBr t  =  su# (ad# (Snd firstArg) secondArg)
      --                     to  su# (ad# x y).

      -- Snd (firstArg t)  =  Snd (su# x)  =  x.
      e1 : Deriv (eqF (ap1 Snd (firstArg t)) x)
      e1 = ruleTrans (cong1 Snd eA) (ar_su x)

      -- secondArg t  =  y.
      e2 : Deriv (eqF (secondArg t) y)
      e2 = ad2 (su# x) y

      -- inner pair  Pair (Snd firstArg) secondArg  =  Pair x y.
      eInner : Deriv (eqF (ap2 Pair (ap1 Snd (firstArg t)) (secondArg t))
                          (ap2 Pair x y))
      eInner = ruleTrans (congL Pair (secondArg t) e1)
                         (congR Pair x e2)

      -- lift through the  ad#  tag, then the  su#  tag.
      eAd : Deriv (eqF (ad# (ap1 Snd (firstArg t)) (secondArg t))
                       (ad# x y))
      eAd = congR Pair tagAd eInner

      eSu : Deriv (eqF (suBr t) (su# (ad# x y)))
      eSu = congR Pair tagSu eAd
  in ruleTrans chain1 eSu
