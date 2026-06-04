{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DefIndN -- the number-code "define" indicator and its fold, the
-- computational core of surprise-GII's counting atom on the NUMBER-CODE base.
--
-- This is the number-code mirror of  T4.DefInd  (SURPRISE-GII-NUMBERCODE-HANDOFF
-- S3.1) with two changes that make surprise-GII much simpler:
--   * the decoder is  runProgN  (program NUMBER, T4.ParseN) instead of  runProg ;
--   * the candidate enumeration is the IDENTITY -- the  k-th program is the
--     number  k -- so the fold index  idx := I  (the identity  Fun1 ), NOT the
--     old  enum  table.  defCountN  bakes this in.
--
--   defIndN : Fun2 ,
--   ap2 defIndN p q  =  natEqF (runProgN p (Snd q)) (s (Fst q))               (PROVED)
--
-- read with  q = pi u x  ( u = Fst q  the subject,  x = Snd q  the run-length):
-- "running the program NUMBER  p  for  x  steps yields output  u ".
--
--   defCountN : Fun2 ,
--   ap2 defCountN (pi u x) (natCode N)  =  sum_{j=0}^{N} defIndN(j, pi u x)
--
-- ( idx = I , so  idx j = j  -- the simplification ).

module T4.DefIndN where

open import T4.Base
open import T4.ParseN using ( runProgN )
open import BRA3.Church using ( sigma )
open import BRA3.SubT.NatEq using ( natEqF )
open import T4.CountingObj using ( sumRec ; sumRec_at_O ; sumRec_succ )

------------------------------------------------------------------------
-- SECTION 1.  The indicator's two argument-shaping functors.
--   defRunFN p q = runProgN p (Snd q)   (run number p for Snd q steps)
--   defTgtFN p q = s (Fst q)            (target output s(Fst q))

defRunFN : Fun2
defRunFN = Fan Const (Lift2 Snd) runProgN

defTgtFN : Fun2
defTgtFN = Lift2 (compose1U s Fst)

defRunFN_eq :
  (p q : Term) ->
  Deriv (eqF (ap2 defRunFN p q) (ap2 runProgN p (ap1 Snd q)))
defRunFN_eq p q =
  let e0 : Deriv (eqF (ap2 defRunFN p q)
                      (ap2 runProgN (ap2 Const p q) (ap2 (Lift2 Snd) p q)))
      e0 = axFan Const (Lift2 Snd) runProgN p q

      e1 : Deriv (eqF (ap2 runProgN (ap2 Const p q) (ap2 (Lift2 Snd) p q))
                      (ap2 runProgN p (ap2 (Lift2 Snd) p q)))
      e1 = congL runProgN (ap2 (Lift2 Snd) p q) (axConst p q)

      e2 : Deriv (eqF (ap2 runProgN p (ap2 (Lift2 Snd) p q))
                      (ap2 runProgN p (ap1 Snd q)))
      e2 = congR runProgN p (axLift2 Snd p q)
  in ruleTrans e0 (ruleTrans e1 e2)

defTgtFN_eq :
  (p q : Term) ->
  Deriv (eqF (ap2 defTgtFN p q) (ap1 s (ap1 Fst q)))
defTgtFN_eq p q =
  ruleTrans (axLift2 (compose1U s Fst) p q) (axComp s Fst q)

------------------------------------------------------------------------
-- SECTION 2.  The define indicator and its reduction skeleton.

defIndN : Fun2
defIndN = Fan defRunFN defTgtFN natEqF

defIndN_eq :
  (p q : Term) ->
  Deriv (eqF (ap2 defIndN p q)
             (ap2 natEqF (ap2 runProgN p (ap1 Snd q)) (ap1 s (ap1 Fst q))))
defIndN_eq p q =
  let e0 : Deriv (eqF (ap2 defIndN p q)
                      (ap2 natEqF (ap2 defRunFN p q) (ap2 defTgtFN p q)))
      e0 = axFan defRunFN defTgtFN natEqF p q

      e1 : Deriv (eqF (ap2 natEqF (ap2 defRunFN p q) (ap2 defTgtFN p q))
                      (ap2 natEqF (ap2 runProgN p (ap1 Snd q)) (ap2 defTgtFN p q)))
      e1 = congL natEqF (ap2 defTgtFN p q) (defRunFN_eq p q)

      e2 : Deriv (eqF (ap2 natEqF (ap2 runProgN p (ap1 Snd q)) (ap2 defTgtFN p q))
                      (ap2 natEqF (ap2 runProgN p (ap1 Snd q)) (ap1 s (ap1 Fst q))))
      e2 = congR natEqF (ap2 runProgN p (ap1 Snd q)) (defTgtFN_eq p q)
  in ruleTrans e0 (ruleTrans e1 e2)

------------------------------------------------------------------------
-- SECTION 3.  The counting fold over the IDENTITY index  idx := I .
--   ap2 defCountN q (natCode N) = sum_{j=0}^{N} defIndN(I j, q) ,
--   q = pi u x ,  and  I j = j  ( the enum = identity simplification ).

defCountN : Fun2
defCountN = sumRec defIndN I

defCountN_at_O :
  (q : Term) ->
  Deriv (eqF (ap2 defCountN q O) (ap2 defIndN (ap1 I O) q))
defCountN_at_O q = sumRec_at_O defIndN I q

defCountN_succ :
  (q m : Term) ->
  Deriv (eqF (ap2 defCountN q (ap1 s m))
             (ap2 sigma (ap2 defCountN q m)
                        (ap2 defIndN (ap1 I (ap1 s m)) q)))
defCountN_succ q m = sumRec_succ defIndN I q m
