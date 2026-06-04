{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KrFoldN -- the per-step characteristic  Kr : Fun1  of surprise-GII's
-- inductive step ( clos line 57 :  "we write K(x0,p(r+1),...,pN) as Kr x0 = 0" ).
--
-- Given the FIXED describing programs  picks  for days  [r+1..N] , the day-d
-- conjunct of  K  is  describeAtN (picks d) d fuel = ( runProgN (natCode (picks d))
-- fuel = s (natCode d) ) ,  whose per-day FAIL indicator
--
--   failTermN d : Fun1 ,
--   ap1 (failTermN d) fuel = isZero ( defIndN (natCode (picks d)) (pi (natCode d) fuel) )
--
-- is  O  exactly when day  d  IS described ( defIndN = s O )  and  s O  when it is
-- not.   Folding the fails with  sigma  over days  [start..start+k]  gives
--
--   KrFold start k : Fun1 ,
--   ap1 (KrFold start k) fuel = sum_{d=start}^{start+k} (failTermN d) fuel ,
--
-- so  ap1 (KrFold start k) fuel = O  iff every fail is  O  iff every fixed program
-- describes its day -- i.e.  Kr fuel = O  <=>  K(fuel, p(r+1),...,pN) .   ( The
-- "<=>" is the converse sigma-zero  T4.SigmaZeroN , discharged at the recogniser. )
--
--   Kr r k = KrFold (suc r) k   ( days  r+1 .. r+1+k ;  k := N - (r+1) downstream ).
--
-- This is the SUM-of-fails dual of  T4.DefIndN.defCountN  ( sum-of-hits ) ;  the
-- sum polarity lets the projection reuse  sumProjN / SigmaZeroN  directly.

open import T4.Base
open import BRA3.Church   using ( isZero ; pi ; sigma )
open import T4.DefIndN    using ( defIndN )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq )

module T4.KrFoldN (picks : Nat -> Nat) where

------------------------------------------------------------------------
-- SECTION 1.  The per-day FAIL indicator as a Fun1 of the run-length.

-- dayPkg d : fuel |-> pi (natCode d) fuel .
dayPkg : Nat -> Fun1
dayPkg d = C pi (constN d) I

dayPkg_eq :
  (d : Nat) (fuel : Term) ->
  Deriv (eqF (ap1 (dayPkg d) fuel) (ap2 pi (natCode d) fuel))
dayPkg_eq d fuel =
  let e0 : Deriv (eqF (ap1 (dayPkg d) fuel)
                      (ap2 pi (ap1 (constN d) fuel) (ap1 I fuel)))
      e0 = ax_C pi (constN d) I fuel
  in ruleTrans e0
       (ruleTrans (congL pi (ap1 I fuel) (constN_eq d fuel))
                  (congR pi (natCode d) (axI fuel)))

-- defTermD d : fuel |-> defIndN (natCode (picks d)) (pi (natCode d) fuel) .
defTermD : Nat -> Fun1
defTermD d = C defIndN (compose1U (constN (picks d)) o) (dayPkg d)

defTermD_eq :
  (d : Nat) (fuel : Term) ->
  Deriv (eqF (ap1 (defTermD d) fuel)
             (ap2 defIndN (natCode (picks d)) (ap2 pi (natCode d) fuel)))
defTermD_eq d fuel =
  let Hd : Fun1
      Hd = compose1U (constN (picks d)) o
      hd_eq : Deriv (eqF (ap1 Hd fuel) (natCode (picks d)))
      hd_eq = ruleTrans (compose1U_eq (constN (picks d)) o fuel)
                (ruleTrans (cong1 (constN (picks d)) (ax_o fuel))
                           (constN_eq (picks d) O))
      e0 : Deriv (eqF (ap1 (defTermD d) fuel)
                      (ap2 defIndN (ap1 Hd fuel) (ap1 (dayPkg d) fuel)))
      e0 = ax_C defIndN Hd (dayPkg d) fuel
  in ruleTrans e0
       (ruleTrans (congL defIndN (ap1 (dayPkg d) fuel) hd_eq)
                  (congR defIndN (natCode (picks d)) (dayPkg_eq d fuel)))

-- failTermN d : fuel |-> isZero ( defIndN (natCode (picks d)) (pi (natCode d) fuel) ) .
failTermN : Nat -> Fun1
failTermN d = compose1U isZero (defTermD d)

failTermN_eq :
  (d : Nat) (fuel : Term) ->
  Deriv (eqF (ap1 (failTermN d) fuel)
             (ap1 isZero (ap2 defIndN (natCode (picks d)) (ap2 pi (natCode d) fuel))))
failTermN_eq d fuel =
  ruleTrans (compose1U_eq isZero (defTermD d) fuel)
            (cong1 isZero (defTermD_eq d fuel))

------------------------------------------------------------------------
-- SECTION 2.  The sum-of-fails fold over days  [start .. start+k]  and  Kr .
--   RIGHT-nested ( head = smallest day  start ), to parallel  bigConjCountN
--   exactly so the conj-bridge ( T4.KrBridgeN ) is an aligned induction.

KrFold : Nat -> Nat -> Fun1
KrFold start zero    = failTermN start
KrFold start (suc k) = C sigma (failTermN start) (KrFold (suc start) k)

-- base ( k = 0 ) :  the single day  start .
KrFold_at_O :
  (start : Nat) (fuel : Term) ->
  Deriv (eqF (ap1 (KrFold start zero) fuel)
             (ap1 isZero (ap2 defIndN (natCode (picks start)) (ap2 pi (natCode start) fuel))))
KrFold_at_O start fuel = failTermN_eq start fuel

-- step ( k -> k+1 ) :  split off the HEAD day  start  fail.
KrFold_succ :
  (start k : Nat) (fuel : Term) ->
  Deriv (eqF (ap1 (KrFold start (suc k)) fuel)
             (ap2 sigma (ap1 (failTermN start) fuel)
                        (ap1 (KrFold (suc start) k) fuel)))
KrFold_succ start k fuel =
  ax_C sigma (failTermN start) (KrFold (suc start) k) fuel

------------------------------------------------------------------------
-- SECTION 3.  The per-step characteristic  Kr r k = KrFold (suc r) k
--   ( days  r+1 .. r+1+k ;  Kr fuel = O  <=>  K(fuel, p(r+1),...,pN) ).

Kr : Nat -> Nat -> Fun1
Kr r k = KrFold (suc r) k
