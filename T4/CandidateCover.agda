{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CandidateCover -- the STRUCTURAL generator law that drives enumeration
-- coverage WITHOUT iterating  k  times :
--
--   candidate (natCode (idx d r)) = cons (natCode d) (candidate (natCode r))
--        ( idx d r = d + 3 r ,  d in {1,2,3} )
--
-- i.e. the index  d + 3 r  prepends digit  d  onto the  r -th string.  Proved by
-- induction on  r  using the closed law
--
--   nextString^3 (cons d s) = cons d (nextString s)            ( next3x )
--
-- ( advancing a tail by one costs exactly 3 successor steps -- one full
-- bijective-base-3 carry cycle ).   Coverage ( every flat string = candidate of
-- its base-3 rank ) and the diagonal membership  enc gL = candidate(k0)  follow
-- by structural recursion on the string, NEVER by a  k0 -fold iteration.

module T4.CandidateCover where

open import T4.Base
open import T4.NextString using
  ( nextString ; cons ; next_at_O ; next_at_tag1 ; next_at_tag2 ; next_at_tag3 )
open import T4.Candidate using
  ( candidate ; candidate_natCode ; candidate_at_O ; candidate_step ; candidate_at_one )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 0.  Abbreviations.

-- n3 t = nextString (nextString (nextString t)).
n3 : Term -> Term
n3 t = ap1 nextString (ap1 nextString (ap1 nextString t))

tag1 tag2 tag3 : Term
tag1 = natCode (suc zero)
tag2 = natCode (suc (suc zero))
tag3 = natCode (suc (suc (suc zero)))

------------------------------------------------------------------------
-- SECTION 1.  nextString^3 (cons d s) = cons d (nextString s) , d in {1,2,3}.
-- One full carry cycle returns the same lead digit and advances the tail once.

next3x : (b : Term) -> Deriv (eqF (n3 (cons tag1 b)) (cons tag1 (ap1 nextString b)))
next3x b =
  ruleTrans (cong1 nextString (cong1 nextString (next_at_tag1 b)))
    (ruleTrans (cong1 nextString (next_at_tag2 b))
               (next_at_tag3 b))

next3y : (b : Term) -> Deriv (eqF (n3 (cons tag2 b)) (cons tag2 (ap1 nextString b)))
next3y b =
  ruleTrans (cong1 nextString (cong1 nextString (next_at_tag2 b)))
    (ruleTrans (cong1 nextString (next_at_tag3 b))
               (next_at_tag1 (ap1 nextString b)))

next3z : (b : Term) -> Deriv (eqF (n3 (cons tag3 b)) (cons tag3 (ap1 nextString b)))
next3z b =
  ruleTrans (cong1 nextString (cong1 nextString (next_at_tag3 b)))
    (ruleTrans (cong1 nextString (next_at_tag1 (ap1 nextString b)))
               (next_at_tag2 (ap1 nextString b)))

------------------------------------------------------------------------
-- SECTION 2.  candidate at  suc^3 k  = nextString^3 (candidate at k).

cand_step3 :
  (k : Nat) ->
  Deriv (eqF (ap1 candidate (natCode (suc (suc (suc k)))))
             (n3 (ap1 candidate (natCode k))))
cand_step3 k =
  ruleTrans (candidate_step (suc (suc k)))
    (cong1 nextString
      (ruleTrans (candidate_step (suc k))
        (cong1 nextString (candidate_step k))))

------------------------------------------------------------------------
-- SECTION 3.  The bases  candidate (natCode d) = cons d O ,  d in {1,2,3}.

base1 : Deriv (eqF (ap1 candidate (natCode (suc zero))) (cons tag1 O))
base1 = candidate_at_one

base2 : Deriv (eqF (ap1 candidate (natCode (suc (suc zero)))) (cons tag2 O))
base2 =
  ruleTrans (candidate_step (suc zero))
    (ruleTrans (cong1 nextString base1) (next_at_tag1 O))

base3 : Deriv (eqF (ap1 candidate (natCode (suc (suc (suc zero))))) (cons tag3 O))
base3 =
  ruleTrans (candidate_step (suc (suc zero)))
    (ruleTrans (cong1 nextString base2) (next_at_tag2 O))

------------------------------------------------------------------------
-- SECTION 4.  idx d r = d + 3 r ,  so that idx d (suc r) = suc^3 (idx d r).

idx : Nat -> Nat -> Nat
idx d zero    = d
idx d (suc r) = suc (suc (suc (idx d r)))

------------------------------------------------------------------------
-- SECTION 5.  The three structural laws ( one per lead digit ), each by
-- induction on  r .  candidate (natCode (idx d r)) = cons d (candidate r).

candidateConsA :
  (r : Nat) ->
  Deriv (eqF (ap1 candidate (natCode (idx (suc zero) r)))
             (cons tag1 (ap1 candidate (natCode r))))
candidateConsA zero =
  ruleTrans base1 (congR pi tag1 (ruleSym candidate_at_O))
candidateConsA (suc r) =
  ruleTrans (cand_step3 (idx (suc zero) r))
    (ruleTrans (cong1 nextString (cong1 nextString (cong1 nextString (candidateConsA r))))
      (ruleTrans (next3x (ap1 candidate (natCode r)))
                 (congR pi tag1 (ruleSym (candidate_step r)))))

candidateConsB :
  (r : Nat) ->
  Deriv (eqF (ap1 candidate (natCode (idx (suc (suc zero)) r)))
             (cons tag2 (ap1 candidate (natCode r))))
candidateConsB zero =
  ruleTrans base2 (congR pi tag2 (ruleSym candidate_at_O))
candidateConsB (suc r) =
  ruleTrans (cand_step3 (idx (suc (suc zero)) r))
    (ruleTrans (cong1 nextString (cong1 nextString (cong1 nextString (candidateConsB r))))
      (ruleTrans (next3y (ap1 candidate (natCode r)))
                 (congR pi tag2 (ruleSym (candidate_step r)))))

candidateConsC :
  (r : Nat) ->
  Deriv (eqF (ap1 candidate (natCode (idx (suc (suc (suc zero))) r)))
             (cons tag3 (ap1 candidate (natCode r))))
candidateConsC zero =
  ruleTrans base3 (congR pi tag3 (ruleSym candidate_at_O))
candidateConsC (suc r) =
  ruleTrans (cand_step3 (idx (suc (suc (suc zero))) r))
    (ruleTrans (cong1 nextString (cong1 nextString (cong1 nextString (candidateConsC r))))
      (ruleTrans (next3z (ap1 candidate (natCode r)))
                 (congR pi tag3 (ruleSym (candidate_step r)))))

------------------------------------------------------------------------
-- SECTION 6.  Enumeration COVERAGE.   A ternary string is a list of digits
-- {1,2,3}; its rank is its bijective-base-3 value (least-significant first).
-- coverage :  candidate (natCode (rank xs)) = toStr xs  -- every string is the
-- candidate at its own rank, by structural recursion ( NO k-fold iteration ).

data Tri : Set where
  t1 t2 t3 : Tri

triVal : Tri -> Nat
triVal t1 = suc zero
triVal t2 = suc (suc zero)
triVal t3 = suc (suc (suc zero))

data TStr : Set where
  tnil  : TStr
  tcons : Tri -> TStr -> TStr

toStr : TStr -> Term
toStr tnil         = O
toStr (tcons t xs) = cons (natCode (triVal t)) (toStr xs)

rank : TStr -> Nat
rank tnil         = zero
rank (tcons t xs) = idx (triVal t) (rank xs)

coverage :
  (xs : TStr) -> Deriv (eqF (ap1 candidate (natCode (rank xs))) (toStr xs))
coverage tnil            = candidate_at_O
coverage (tcons t1 xs) =
  ruleTrans (candidateConsA (rank xs)) (congR pi tag1 (coverage xs))
coverage (tcons t2 xs) =
  ruleTrans (candidateConsB (rank xs)) (congR pi tag2 (coverage xs))
coverage (tcons t3 xs) =
  ruleTrans (candidateConsC (rank xs)) (congR pi tag3 (coverage xs))
