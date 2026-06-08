{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KolmEvalMeta -- a small META-evaluation library for the reference
-- semantics  evalN1 / evalN2  (T4.EvalUCorrect), used to drive the Berry
-- search program of the non-computability proof.
--
-- Two kinds of lemma:
--
--   * STRUCTURAL  ( no consistency ):  the  evalN  of the raw-built
--     combinators  Lift1 ,  Lift2 ,  compose1U ,  compose1 ,  sub ,  isZero ,
--     condFork  is computed directly from the six  evalN  clauses by
--     induction.  ( e.g.  evalN2 (Lift1 f) a b = evalN1 f a , independent of
--     b , because  Lift1 f = R f v v  ignores its recursion argument. )
--
--   * REFLECTIVE  ( needs simple consistency  con ):  the  evalN  of the
--     CANTOR-coded combinators  Fst , Snd , pi(=Pair)  and the iterator
--     exp3  is pinned via the existing OBJECT equations ( axFst / axSnd /
--     exp3_natCode ) plus  evalN_sound  and numeral reflection  numReflect .
--     This avoids unfolding the cantor-pairing arithmetic at the meta level.
--
-- From these,  fanMeta / postMeta  give the meta law of the  Fan / Post
-- combinators, which is what the search step  gStep  is assembled from.

module T4.KolmEvalMeta where

open import T4.Base
open import T4.EvalUCorrect using
  ( evalN1 ; evalN2 ; evalN1_sound ; evalN2_sound )
open import BRA3.Church  using ( sub ; isZero ; p_aux ; isZeroAux )
open import BRA3.Dispatch using ( compose1 )
open import BRA3.Fan      using ( Fan_wf )
open import T4.Exp3      using ( exp3 ; exp3_natCode )
open import T4.TreeDigitsSize using ( pow3 )
open import T4.Code      using ( falseF )
open import T4.KolmNumReflect  using ( numEqToFalse )
open import T4.SurpriseG2.NumNeq using ( Not )
open import T4.SurpriseG2.MetaPigeonhole using
  ( NatDec ; natYes ; natNo ; natDecEq )

------------------------------------------------------------------------
-- Meta helper functions.

predN : Nat -> Nat
predN zero    = zero
predN (suc k) = k

monus : Nat -> Nat -> Nat
monus a zero    = a
monus a (suc b) = predN (monus a b)

iszN : Nat -> Nat
iszN zero    = suc zero
iszN (suc _) = zero

-- caseNat z a b :  a  if  z = 0 ,  b  otherwise.
caseNat : Nat -> Nat -> Nat -> Nat
caseNat zero    a b = a
caseNat (suc _) a b = b

eqCong2 :
  {A B C : Set} (g : A -> B -> C) {a a' : A} {b b' : B} ->
  Eq a a' -> Eq b b' -> Eq (g a b) (g a' b')
eqCong2 g refl refl = refl

------------------------------------------------------------------------
-- SECTION 1.  Structural meta lemmas (no consistency).

-- Lift1 f = R f v v : ignores the recursion argument, applies f to the first.
evalN2_Lift1 : (f : Fun1) (a b : Nat) -> Eq (evalN2 (Lift1 f) a b) (evalN1 f a)
evalN2_Lift1 f a zero    = refl
evalN2_Lift1 f a (suc k) = evalN2_Lift1 f a k

-- compose1U f g = C (Lift1 f) g u .
evalN1_compose1U :
  (f g : Fun1) (n : Nat) -> Eq (evalN1 (compose1U f g) n) (evalN1 f (evalN1 g n))
evalN1_compose1U f g n = evalN2_Lift1 f (evalN1 g n) n

-- compose1 f g = C (R f v v) g u  (BRA3.Dispatch form).
evalN1_compose1 :
  (f g : Fun1) (n : Nat) -> Eq (evalN1 (compose1 f g) n) (evalN1 f (evalN1 g n))
evalN1_compose1 f g n = evalN2_Lift1 f (evalN1 g n) n

-- Lift2 f = iter_step_fun f : applies f to the SECOND argument.
evalN2_Lift2 : (f : Fun1) (a b : Nat) -> Eq (evalN2 (Lift2 f) a b) (evalN1 f b)
evalN2_Lift2 f a zero    = evalN1_compose1 f o a
evalN2_Lift2 f a (suc k) =
  eqTrans (evalN2_Lift1 (compose1 f s) k (evalN2 (Lift2 f) a k))
          (evalN1_compose1 f s k)

-- p_aux = R o w v :  predecessor of the SECOND argument.
evalN2_p_aux : (x m : Nat) -> Eq (evalN2 p_aux x m) (predN m)
evalN2_p_aux x zero    = refl
evalN2_p_aux x (suc k) = evalN2_Lift1 u k (evalN2 p_aux x k)

-- sub = R u p_aux v :  truncated subtraction  a - b .
evalN2_sub : (a b : Nat) -> Eq (evalN2 sub a b) (monus a b)
evalN2_sub a zero    = refl
evalN2_sub a (suc k) =
  eqTrans (evalN2_p_aux k (evalN2 sub a k)) (eqCong predN (evalN2_sub a k))

-- isZeroAux = R cone zeroFn v :  ignores first argument, iszN of the second.
evalN2_isZeroAux : (x n : Nat) -> Eq (evalN2 isZeroAux x n) (iszN n)
evalN2_isZeroAux x zero    = evalN2_Lift1 s zero (suc x)
evalN2_isZeroAux x (suc k) = evalN2_Lift1 o k (evalN2 isZeroAux x k)

-- isZero = C isZeroAux o u .
evalN1_isZero : (n : Nat) -> Eq (evalN1 isZero n) (iszN n)
evalN1_isZero n = evalN2_isZeroAux zero n

-- condFork = R Snd w (R Fst v v) :  Snd at 0 , Fst at a successor.
evalN2_condFork0 : (z : Nat) -> Eq (evalN2 condFork z zero) (evalN1 Snd z)
evalN2_condFork0 z = refl

evalN2_condForkS : (z k : Nat) -> Eq (evalN2 condFork z (suc k)) (evalN1 Fst z)
evalN2_condForkS z k =
  eqTrans (evalN2_Lift1 u (evalN2 (Lift1 Fst) z k) (evalN2 condFork z k))
          (evalN2_Lift1 Fst z k)

------------------------------------------------------------------------
-- SECTION 2.  Numeral reflection (needs simple consistency).

numReflect :
  Not (Deriv falseF) -> (m n : Nat) ->
  Deriv (eqF (natCode m) (natCode n)) -> Eq m n
numReflect con m n h = decide (natDecEq m n)
  where
    decide : NatDec m n -> Eq m n
    decide (natYes e)  = e
    decide (natNo  ne) = emptyElim (con (numEqToFalse m n ne h))

-- General reflection:  an object equation  f (natCode k) = natCode val
-- pins the meta value  evalN1 f k = val .
metaRefl1 :
  Not (Deriv falseF) -> (f : Fun1) (k val : Nat) ->
  Deriv (eqF (ap1 f (natCode k)) (natCode val)) -> Eq (evalN1 f k) val
metaRefl1 con f k val h =
  numReflect con (evalN1 f k) val (ruleTrans (evalN1_sound f k) h)

------------------------------------------------------------------------
-- SECTION 3.  Cantor-pairing meta inverses (via reflection).

fstP : Not (Deriv falseF) -> (a b : Nat) -> Eq (evalN1 Fst (evalN2 Pair a b)) a
fstP con a b =
  let sa = evalN1_sound Fst (evalN2 Pair a b)
      sp = evalN2_sound Pair a b
      ax = axFst (natCode a) (natCode b)
      chain = ruleTrans sa (ruleTrans (cong1 Fst sp) ax)
  in numReflect con (evalN1 Fst (evalN2 Pair a b)) a chain

sndP : Not (Deriv falseF) -> (a b : Nat) -> Eq (evalN1 Snd (evalN2 Pair a b)) b
sndP con a b =
  let sa = evalN1_sound Snd (evalN2 Pair a b)
      sp = evalN2_sound Pair a b
      ax = axSnd (natCode a) (natCode b)
      chain = ruleTrans sa (ruleTrans (cong1 Snd sp) ax)
  in numReflect con (evalN1 Snd (evalN2 Pair a b)) b chain

-- exp3 computes pow3 at the meta level.
evalN1_exp3 : Not (Deriv falseF) -> (k : Nat) -> Eq (evalN1 exp3 k) (pow3 k)
evalN1_exp3 con k = metaRefl1 con exp3 k (pow3 k) (exp3_natCode k)

------------------------------------------------------------------------
-- SECTION 4.  Fan / Post meta laws (need con, via fstP/sndP).

-- Fan h1 h2 h :  ap2 ... a b = h (h1 a b) (h2 a b) .
fanMeta :
  Not (Deriv falseF) -> (h1 h2 h : Fun2) (a b : Nat) ->
  Eq (evalN2 (Fan h1 h2 h) a b) (evalN2 h (evalN2 h1 a b) (evalN2 h2 a b))
fanMeta con h1 h2 h a zero    = refl
fanMeta con h1 h2 h a (suc k) =
  let P : Nat
      P = evalN2 Pair a k
      eFst : Eq (evalN1 Fst P) a
      eFst = fstP con a k
      eG : Eq (evalN1 (compose1U s Snd) P) (suc k)
      eG = eqTrans (evalN1_compose1U s Snd P) (eqCong suc (sndP con a k))
      inner1 : Eq (evalN2 h1 (evalN1 Fst P) (evalN1 (compose1U s Snd) P))
                  (evalN2 h1 a (suc k))
      inner1 = eqCong2 (evalN2 h1) eFst eG
      inner2 : Eq (evalN2 h2 (evalN1 Fst P) (evalN1 (compose1U s Snd) P))
                  (evalN2 h2 a (suc k))
      inner2 = eqCong2 (evalN2 h2) eFst eG
      outer : Eq (evalN2 h (evalN2 h1 (evalN1 Fst P) (evalN1 (compose1U s Snd) P))
                           (evalN2 h2 (evalN1 Fst P) (evalN1 (compose1U s Snd) P)))
                 (evalN2 h (evalN2 h1 a (suc k)) (evalN2 h2 a (suc k)))
      outer = eqCong2 (evalN2 h) inner1 inner2
  in eqTrans (evalN2_Lift1 (Fan_wf h1 h2 h) P (evalN2 (Fan h1 h2 h) a k)) outer

-- Post f hh :  ap2 ... a b = f (hh a b) .
postMeta :
  Not (Deriv falseF) -> (f : Fun1) (hh : Fun2) (a b : Nat) ->
  Eq (evalN2 (Post f hh) a b) (evalN1 f (evalN2 hh a b))
postMeta con f hh a b =
  eqTrans (fanMeta con hh v (Lift1 f) a b)
          (evalN2_Lift1 f (evalN2 hh a b) (evalN2 v a b))
