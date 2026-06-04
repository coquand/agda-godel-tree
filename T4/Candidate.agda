{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Candidate -- the constant-code candidate ENUMERATOR  candidate : Fun1 ,
--
--   candidate := C (iter nextString) Z I ,
--   candidate (natCode k) = nextString^k (O)   ( the k-th flat tag-string ).
--
-- This is the small-code drop-in replacement for the table-lookup
--  T4.EnumProg.enum (= lookupFrom 0 progs , whose code embeds the whole program
-- list).  candidate's code is CONSTANT ( a fixed  iter  of the fixed  nextString
-- fold ), with NO  Lstar  inside, so a Chaitin diagonal embedding  candidate
-- stays  O(1) .  The enumerated order is bijective-base-3, least-significant
-- digit outermost:
--
--   k :  0   1    2    3    4     5     ...
--        O  "1"  "2"  "3"  "11"  "21"   ...           ( "d" = cons (natCode d) )
--
-- so EVERY flat tag-{1,2,3} string occurs exactly once -- the finite Chaitin
-- candidate family  { candidate(k) : k < N }  is precisely the strings of
-- length  < log_3 N , N symbolic.

module T4.Candidate where

open import T4.Base
open import T4.NextString using ( nextString ; next_at_O ; cons )

open import BRA3.PairAlgebra    using ( Z ; axZ ; I ; axI )
open import BRA3.CourseOfValues using ( iter ; iterMeta ; iter_natCode )

------------------------------------------------------------------------
-- The enumerator.

-- SEALED ( abstract ) so that  codeFun1 candidate  / codeFun2 runProgN  stay
-- NEUTRAL downstream ( candidate = C (iter nextString) Z I  embeds the huge
-- nextString fold;  unsealed, its code is renormalised wherever the diagonal /
-- clash mention  runProgN , blowing past the 20s budget ).  All laws live in
-- the same abstract block ( they unfold candidate );  downstream consumes only
-- the laws + the opaque  candidate .
abstract
  candidate : Fun1
  candidate = C (iter nextString) Z I

  -- candidate k = iter nextString O k   ( fix the first iterand to O ).
  candidate_unfold :
    (k : Term) -> Deriv (eqF (ap1 candidate k) (ap2 (iter nextString) O k))
  candidate_unfold k =
    ruleTrans (ax_C (iter nextString) Z I k)
      (ruleTrans (congL (iter nextString) (ap1 I k) (axZ k))
                 (congR (iter nextString) O (axI k)))

  -- candidate (natCode k) = nextString^k (O)   ( the k-th string ).
  candidate_natCode :
    (k : Nat) -> Deriv (eqF (ap1 candidate (natCode k)) (iterMeta nextString O k))
  candidate_natCode k =
    ruleTrans (candidate_unfold (natCode k)) (iter_natCode nextString O k)

  -- candidate (natCode 0) = O .
  candidate_at_O : Deriv (eqF (ap1 candidate (natCode zero)) O)
  candidate_at_O = candidate_natCode zero

  -- candidate (natCode (suc k)) = nextString (candidate (natCode k)) .
  candidate_step :
    (k : Nat) ->
    Deriv (eqF (ap1 candidate (natCode (suc k)))
               (ap1 nextString (ap1 candidate (natCode k))))
  candidate_step k =
    ruleTrans (candidate_natCode (suc k))
              (cong1 nextString (ruleSym (candidate_natCode k)))

  -- candidate (natCode 1) = cons tag1 O   ( sanity: the first nonempty string ).
  candidate_at_one : Deriv (eqF (ap1 candidate (natCode (suc zero))) (cons (natCode (suc zero)) O))
  candidate_at_one =
    ruleTrans (candidate_step zero)
              (ruleTrans (cong1 nextString candidate_at_O) next_at_O)
