{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DefInd -- the concrete object-level "define" indicator and its fold,
-- the computational core of surprise-GII's characteristic program CK.
-- (Task (a), subtask 2 of T4/SURPRISE-GII-HANDOFF.md: the genuine "= O"
-- computation, the long-pole residual; Kr is NOT abstract.)
--
-- clos-corrected.md's  CK : Fun2  satisfies  ap2 CK u x = O  iff some program
-- p in the finite set  S = enum  defines  u  in  x  steps, i.e. CK folds the
-- DISJUNCTION over  S .  We build it from the shipped counting fold
-- ( T4.CountingObj.sumRec , which sums an indicator over an index range with
-- PROVED unfold lemmas) composed with one  isZero  flip (native convention is
-- O = false / s O = true, so "some p matches" -> nonzero sum -> isZero = O,
-- matching clos's  O = "compressible" ).
--
-- The genuinely new piece is the per-program indicator
--
--   defInd : Fun2 ,
--   ap2 defInd p q  =  natEqF (runProg p (Snd q)) (s (Fst q))               (PROVED)
--
-- read with the packaged argument  q = pi u x  ( u = Fst q  the subject,
-- x = Snd q  the run-length): it tests "running program  p  for  x  steps
-- yields output  u " ( = define_p(u,x) ; cf.  T4.Kdef.definable ).  As a closed
-- BRA combinator
--
--   defInd = Fan (Fan Const (Lift2 Snd) runProg) (Lift2 (compose1U s Fst)) natEqF .
--
-- The indicator's VALUE-correctness (that it is  s O  exactly when  p  halts
-- with the right output) needs the run to halt, and is established only at the
-- specific witnesses (Step 1 RunMono / Step 4 thm13-dPos), NOT here -- here we
-- provide the closed combinator and its reduction skeleton, plus the fold's
-- unfold lemmas, all machine-checked.
--
-- The disjunction fold over a (concrete) enumerator  idx : Fun1  is
--
--   defCount idx : Fun2 ,
--   ap2 (defCount idx) (pi u x) (natCode N)  =  sum_{j=0}^{N} defInd(idx j, pi u x) ,
--
-- and CK is then  Post isZero (Fan pi (Lift1 (constN N)) (defCount idx)) ; that
-- final wiring + the run-witness correctness are the next increment.

module T4.DefInd where

open import T4.Base
open import T4.Kdef using ( runProg )
open import BRA3.Church using ( sigma )
open import BRA3.SubT.NatEq using ( natEqF )
open import T4.CountingObj using ( sumRec ; sumRec_at_O ; sumRec_succ )

------------------------------------------------------------------------
-- SECTION 1.  The indicator's two argument-shaping functors.
--   defRunF  : ap2 defRunF p q = ap2 runProg p (ap1 Snd q)   (run p for Snd q steps)
--   defTgtF  : ap2 defTgtF p q = ap1 s (ap1 Fst q)            (target output s(Fst q))

defRunF : Fun2
defRunF = Fan Const (Lift2 Snd) runProg

defTgtF : Fun2
defTgtF = Lift2 (compose1U s Fst)

defRunF_eq :
  (p q : Term) ->
  Deriv (eqF (ap2 defRunF p q) (ap2 runProg p (ap1 Snd q)))
defRunF_eq p q =
  let e0 : Deriv (eqF (ap2 defRunF p q)
                      (ap2 runProg (ap2 Const p q) (ap2 (Lift2 Snd) p q)))
      e0 = axFan Const (Lift2 Snd) runProg p q

      e1 : Deriv (eqF (ap2 runProg (ap2 Const p q) (ap2 (Lift2 Snd) p q))
                      (ap2 runProg p (ap2 (Lift2 Snd) p q)))
      e1 = congL runProg (ap2 (Lift2 Snd) p q) (axConst p q)

      e2 : Deriv (eqF (ap2 runProg p (ap2 (Lift2 Snd) p q))
                      (ap2 runProg p (ap1 Snd q)))
      e2 = congR runProg p (axLift2 Snd p q)
  in ruleTrans e0 (ruleTrans e1 e2)

defTgtF_eq :
  (p q : Term) ->
  Deriv (eqF (ap2 defTgtF p q) (ap1 s (ap1 Fst q)))
defTgtF_eq p q =
  ruleTrans (axLift2 (compose1U s Fst) p q) (axComp s Fst q)

------------------------------------------------------------------------
-- SECTION 2.  The define indicator and its reduction skeleton.

defInd : Fun2
defInd = Fan defRunF defTgtF natEqF

defInd_eq :
  (p q : Term) ->
  Deriv (eqF (ap2 defInd p q)
             (ap2 natEqF (ap2 runProg p (ap1 Snd q)) (ap1 s (ap1 Fst q))))
defInd_eq p q =
  let e0 : Deriv (eqF (ap2 defInd p q)
                      (ap2 natEqF (ap2 defRunF p q) (ap2 defTgtF p q)))
      e0 = axFan defRunF defTgtF natEqF p q

      e1 : Deriv (eqF (ap2 natEqF (ap2 defRunF p q) (ap2 defTgtF p q))
                      (ap2 natEqF (ap2 runProg p (ap1 Snd q)) (ap2 defTgtF p q)))
      e1 = congL natEqF (ap2 defTgtF p q) (defRunF_eq p q)

      e2 : Deriv (eqF (ap2 natEqF (ap2 runProg p (ap1 Snd q)) (ap2 defTgtF p q))
                      (ap2 natEqF (ap2 runProg p (ap1 Snd q)) (ap1 s (ap1 Fst q))))
      e2 = congR natEqF (ap2 runProg p (ap1 Snd q)) (defTgtF_eq p q)
  in ruleTrans e0 (ruleTrans e1 e2)

------------------------------------------------------------------------
-- SECTION 3.  The disjunction fold over a concrete enumerator  idx : Fun1 .
--   ap2 (defCount idx) q (natCode N) = sum_{j=0}^{N} defInd(idx j, q) ,
--   q = pi u x .  (Base/step are the shipped sumRec unfold lemmas at defInd.)

module _ (idx : Fun1) where

  defCount : Fun2
  defCount = sumRec defInd idx

  defCount_at_O :
    (q : Term) ->
    Deriv (eqF (ap2 defCount q O) (ap2 defInd (ap1 idx O) q))
  defCount_at_O q = sumRec_at_O defInd idx q

  defCount_succ :
    (q m : Term) ->
    Deriv (eqF (ap2 defCount q (ap1 s m))
               (ap2 sigma (ap2 defCount q m)
                          (ap2 defInd (ap1 idx (ap1 s m)) q)))
  defCount_succ q m = sumRec_succ defInd idx q m
