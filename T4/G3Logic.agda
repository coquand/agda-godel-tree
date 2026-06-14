{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.G3Logic -- the LOGICAL LAYER of attempt3 §8/§9, packaged per §13:
-- the Ketonen/Kleene G3p calculus (quantifier-free, classical, propositional,
-- fragment ->, _|_; other connectives analogous) for which the structural
-- rules and CUT are ADMISSIBLE.
--
-- Derivations are HEIGHT-INDEXED (Der n G D = derivable with height <= n) so the
-- admissibility lemmas are genuinely height-preserving and the contraction / cut
-- recursions terminate on the height.  No induction rule appears (T0 is
-- induction-free) -> there is NO e0; every proof here is a finite structural /
-- height recursion.
--
-- This file delivers (attempt3 §13.6 stages G1-G2-G3, GREEN, no holes/postulates):
--   * datatypes: Form (at / bot / imp), contexts as List, Mem (membership),
--     Del (delete-one-occurrence), Perm (permutation); the G3p relation Der with
--     principal formulas located by Del (genuinely context-sharing, order-free);
--   * monotonicity in height (mono);
--   * EXCHANGE (derPermA / derPermS): derivations respect permutation;
--   * WEAKENING (wkA / wkS): height-preserving;
--   * height-preserving INVERTIBILITY of (R->) (invR) and (L->) (invLl / invLr);
--   * CONTRACTION (ctrA / ctrS): admissible, height-preserving;
--   * CUT ADMISSIBILITY (cut / cutP): the cut formula dispatches structurally --
--     imp reduces to two SMALLER cuts via invertibility (no commuting cases!),
--     bot via botElimS, atom via cutAtom (commute on d1, terminating on height).
-- NEXT (attempt3 §13.2 / G4): add the equational/recursor axioms as atomic
-- rules, then (Cons) [subformula property of cut-free proofs] and (EqSound).
--
-- Parametric in the atom type Atom (for the consistency application atoms are
-- closed equations; the logical layer does not care).  Initial sequents are
-- ATOMIC (the G3 restriction).  ASCII, --safe --without-K --exact-split.

module T4.G3Logic (Atom : Set) where

------------------------------------------------------------------------
-- Minimal prelude

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

Not : Set -> Set
Not A = A -> Empty

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSig
  field
    fst : A
    snd : B fst
open Sigma public

data And (A B : Set) : Set where
  mkAnd : A -> B -> And A B

andL : {A B : Set} -> And A B -> A
andL (mkAnd a _) = a

andR : {A B : Set} -> And A B -> B
andR (mkAnd _ b) = b

data Or (A B : Set) : Set where
  inl : A -> Or A B
  inr : B -> Or A B

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

------------------------------------------------------------------------
-- Formulas (fragment -> , _|_ ; others analogous, attempt3 §1)

data Form : Set where
  at  : Atom -> Form
  bot : Form
  imp : Form -> Form -> Form

------------------------------------------------------------------------
-- Contexts as lists

data List : Set where
  []   : List
  _::_ : Form -> List -> List

infixr 8 _::_

------------------------------------------------------------------------
-- Membership

data Mem (x : Form) : List -> Set where
  memHd : {xs : List}            -> Mem x (x :: xs)
  memTl : {y : Form} {xs : List} -> Mem x xs -> Mem x (y :: xs)

------------------------------------------------------------------------
-- Delete one occurrence:  Del x G G0  means  G0 = G with one x removed.

data Del (x : Form) : List -> List -> Set where
  delHd : {xs : List}                                -> Del x (x :: xs) xs
  delTl : {y : Form} {xs xs' : List} -> Del x xs xs' -> Del x (y :: xs) (y :: xs')

------------------------------------------------------------------------
-- Permutation (transposition closure)

data Perm : List -> List -> Set where
  permNil   : Perm [] []
  permSkip  : {x : Form} {xs ys : List} -> Perm xs ys -> Perm (x :: xs) (x :: ys)
  permSwap  : {x y : Form} {xs : List} -> Perm (x :: y :: xs) (y :: x :: xs)
  permTrans : {xs ys zs : List} -> Perm xs ys -> Perm ys zs -> Perm xs zs

permRefl : (xs : List) -> Perm xs xs
permRefl []        = permNil
permRefl (x :: xs) = permSkip (permRefl xs)

permSym : {xs ys : List} -> Perm xs ys -> Perm ys xs
permSym permNil          = permNil
permSym (permSkip p)     = permSkip (permSym p)
permSym permSwap         = permSwap
permSym (permTrans p q)  = permTrans (permSym q) (permSym p)

------------------------------------------------------------------------
-- Permutation transports membership and deletion

permMem : {xs ys : List} {a : Form} -> Perm xs ys -> Mem a xs -> Mem a ys
permMem permNil          ()
permMem (permSkip p)     memHd               = memHd
permMem (permSkip p)     (memTl m)           = memTl (permMem p m)
permMem permSwap         memHd               = memTl memHd
permMem permSwap         (memTl memHd)       = memHd
permMem permSwap         (memTl (memTl m))   = memTl (memTl m)
permMem (permTrans p q)  m                   = permMem q (permMem p m)

permDel : {xs ys xs0 : List} {a : Form} ->
          Perm xs ys -> Del a xs xs0 ->
          Sigma List (\ ys0 -> And (Del a ys ys0) (Perm xs0 ys0))
permDel permNil          ()
permDel (permSkip p)     delHd       = mkSig _ (mkAnd delHd p)
permDel (permSkip p)     (delTl d)   =
  let r = permDel p d
  in mkSig _ (mkAnd (delTl (andL (snd r))) (permSkip (andR (snd r))))
permDel (permSwap {x} {y} {xs}) delHd             = mkSig _ (mkAnd (delTl delHd) (permRefl (y :: xs)))
permDel (permSwap {x} {y} {xs}) (delTl delHd)     = mkSig _ (mkAnd delHd (permRefl (x :: xs)))
permDel (permSwap {x} {y})      (delTl (delTl d)) = mkSig _ (mkAnd (delTl (delTl d)) permSwap)
permDel (permTrans p q)  d          =
  let r1 = permDel p d
      r2 = permDel q (andL (snd r1))
  in mkSig _ (mkAnd (andL (snd r2)) (permTrans (andR (snd r1)) (andR (snd r2))))

-- Membership contraction:  a in (x :: x :: G)  ->  a in (x :: G).
memCtr : {a x : Form} {G : List} -> Mem a (x :: x :: G) -> Mem a (x :: G)
memCtr memHd               = memHd
memCtr (memTl memHd)       = memHd
memCtr (memTl (memTl m))   = memTl m

-- A deletion is a particular permutation: Del x G G0 makes G a permutation of
-- (x :: G0).  Used to reduce "principal anywhere" to "principal at the head".
delPerm : {x : Form} {G G0 : List} -> Del x G G0 -> Perm G (x :: G0)
delPerm delHd     = permRefl _
delPerm (delTl d) = permTrans (permSkip (delPerm d)) permSwap

------------------------------------------------------------------------
-- The G3p derivation relation, height-indexed.  Leaves at any (suc n); each
-- rule lifts premises at n to a conclusion at (suc n).

data Der : Nat -> List -> List -> Set where
  init : {n : Nat} (p : Atom) {G D : List} -> Mem (at p) G -> Mem (at p) D -> Der (suc n) G D
  lbot : {n : Nat} {G D : List} -> Mem bot G -> Der (suc n) G D
  limp : {n : Nat} {A B : Form} {G G0 D : List} ->
         Del (imp A B) G G0 -> Der n G0 (A :: D) -> Der n (B :: G0) D -> Der (suc n) G D
  rimp : {n : Nat} {A B : Form} {G D D0 : List} ->
         Del (imp A B) D D0 -> Der n (A :: G) (B :: D0) -> Der (suc n) G D

------------------------------------------------------------------------
-- Monotonicity in height

mono : {n : Nat} {G D : List} -> Der n G D -> Der (suc n) G D
mono (init p i j)     = init p i j
mono (lbot i)         = lbot i
mono (limp del d1 d2) = limp del (mono d1) (mono d2)
mono (rimp del d)     = rimp del (mono d)

------------------------------------------------------------------------
-- EXCHANGE: derivations respect permutation of either zone (height-preserving).

derPermA : {n : Nat} {G G' D : List} -> Perm G G' -> Der n G D -> Der n G' D
derPermS : {n : Nat} {G D D' : List} -> Perm D D' -> Der n G D -> Der n G D'

derPermA perm (init p i j) = init p (permMem perm i) j
derPermA perm (lbot i)     = lbot (permMem perm i)
derPermA perm (limp del d1 d2) =
  let r = permDel perm del
  in limp (andL (snd r))
          (derPermA (andR (snd r)) d1)
          (derPermA (permSkip (andR (snd r))) d2)
derPermA perm (rimp del d) =
  rimp del (derPermA (permSkip perm) d)

derPermS perm (init p i j) = init p i (permMem perm j)
derPermS perm (lbot i)     = lbot i
derPermS perm (limp del d1 d2) =
  limp del (derPermS (permSkip perm) d1) (derPermS perm d2)
derPermS perm (rimp del d) =
  let r = permDel perm del
  in rimp (andL (snd r)) (derPermS (permSkip (andR (snd r))) d)

------------------------------------------------------------------------
-- WEAKENING (height-preserving): add a formula to the front of either zone.

wkA : {n : Nat} {G D : List} (A : Form) -> Der n G D -> Der n (A :: G) D
wkS : {n : Nat} {G D : List} (A : Form) -> Der n G D -> Der n G (A :: D)

wkA A (init p i j)     = init p (memTl i) j
wkA A (lbot i)         = lbot (memTl i)
wkA A (limp del d1 d2) = limp (delTl del) (wkA A d1) (derPermA permSwap (wkA A d2))
wkA A (rimp del d)     = rimp del (derPermA permSwap (wkA A d))

wkS A (init p i j)     = init p i (memTl j)
wkS A (lbot i)         = lbot i
wkS A (limp del d1 d2) = limp del (derPermS permSwap (wkS A d1)) (wkS A d2)
wkS A (rimp del d)     = rimp (delTl del) (derPermS permSwap (wkS A d))

------------------------------------------------------------------------
-- INVERTIBILITY (height-preserving).  Proved in HEAD form (principal at the
-- head of its zone), recursing on the height n so termination is on n.  The
-- general (principal-anywhere, Del-located) forms follow by delPerm + exchange.

invR'  : (n : Nat) {A B : Form} {G D0 : List} ->
         Der n G (imp A B :: D0) -> Der n (A :: G) (B :: D0)
invLl' : (n : Nat) {A B : Form} {G D : List} ->
         Der n (imp A B :: G) D -> Der n G (A :: D)
invLr' : (n : Nat) {A B : Form} {G D : List} ->
         Der n (imp A B :: G) D -> Der n (B :: G) D

-- invR' : invert an implication at the HEAD of the succedent.
invR' zero ()
invR' (suc n0) (init p i (memTl j0)) = init p (memTl i) (memTl j0)
invR' (suc n0) (lbot i)              = lbot (memTl i)
invR' (suc n0) (limp del' d1 d2) =
  limp (delTl del')
       (derPermS permSwap (invR' n0 (derPermS permSwap d1)))
       (derPermA permSwap (invR' n0 d2))
invR' (suc n0) (rimp delHd d')        = mono d'
invR' (suc n0) (rimp (delTl del'') d') =
  rimp (delTl del'')
       (derPermA permSwap (derPermS permSwap (invR' n0 (derPermS permSwap d'))))

-- invLl' : invert an implication at the HEAD of the antecedent, LEFT premise.
invLl' zero ()
invLl' (suc n0) (init p (memTl i0) j) = init p i0 (memTl j)
invLl' (suc n0) (lbot (memTl i0))     = lbot i0
invLl' (suc n0) (rimp del' d') =
  rimp (delTl del') (derPermS permSwap (invLl' n0 (derPermA permSwap d')))
invLl' (suc n0) (limp delHd d1 d2)        = mono d1
invLl' (suc n0) (limp (delTl del'') d1 d2) =
  limp del''
       (derPermS permSwap (invLl' n0 d1))
       (invLl' n0 (derPermA permSwap d2))

-- invLr' : invert an implication at the HEAD of the antecedent, RIGHT premise.
invLr' zero ()
invLr' (suc n0) (init p (memTl i0) j) = init p (memTl i0) j
invLr' (suc n0) (lbot (memTl i0))     = lbot (memTl i0)
invLr' (suc n0) (rimp del' d') =
  rimp del' (derPermA permSwap (invLr' n0 (derPermA permSwap d')))
invLr' (suc n0) (limp delHd d1 d2)        = mono d2
invLr' (suc n0) (limp (delTl del'') d1 d2) =
  limp (delTl del'')
       (invLr' n0 d1)
       (derPermA permSwap (invLr' n0 (derPermA permSwap d2)))

-- General (principal-anywhere) inversions: permute the principal to the head.
invR : {n : Nat} {A B : Form} {G D D0 : List} ->
       Del (imp A B) D D0 -> Der n G D -> Der n (A :: G) (B :: D0)
invR del d = invR' _ (derPermS (delPerm del) d)

invLl : {n : Nat} {A B : Form} {G G0 D : List} ->
        Del (imp A B) G G0 -> Der n G D -> Der n G0 (A :: D)
invLl del d = invLl' _ (derPermA (delPerm del) d)

invLr : {n : Nat} {A B : Form} {G G0 D : List} ->
        Del (imp A B) G G0 -> Der n G D -> Der n (B :: G0) D
invLr del d = invLr' _ (derPermA (delPerm del) d)

------------------------------------------------------------------------
-- CONTRACTION (admissible, height-preserving): merge two copies of a formula
-- in either zone.  Mutually recursive on the height n; the principal cases use
-- invertibility (invLl'/invLr'/invR') to expose components before contracting.

ctrA : (n : Nat) {A : Form} {G D : List} -> Der n (A :: A :: G) D -> Der n (A :: G) D
ctrS : (n : Nat) {A : Form} {G D : List} -> Der n G (A :: A :: D) -> Der n G (A :: D)

-- antecedent contraction
ctrA zero ()
ctrA (suc n0) (init p i j) = init p (memCtr i) j
ctrA (suc n0) (lbot i)     = lbot (memCtr i)
-- principal = the first contracted copy
ctrA (suc n0) (limp delHd d1 d2) =
  limp delHd
       (ctrS n0 (invLl' n0 d1))
       (ctrA n0 (invLr' n0 (derPermA permSwap d2)))
-- principal = the second contracted copy (same remaining premises)
ctrA (suc n0) (limp (delTl delHd) d1 d2) =
  limp delHd
       (ctrS n0 (invLl' n0 d1))
       (ctrA n0 (invLr' n0 (derPermA permSwap d2)))
-- principal lies deeper in G: contract in the premises, reapply L->
ctrA (suc n0) (limp (delTl (delTl d')) d1 d2) =
  limp (delTl d')
       (ctrA n0 d1)
       (derPermA permSwap
         (ctrA n0 (derPermA (permTrans permSwap (permSkip permSwap)) d2)))
ctrA (suc n0) (rimp del d') =
  rimp del
       (derPermA permSwap
         (ctrA n0 (derPermA (permTrans permSwap (permSkip permSwap)) d')))

-- succedent contraction
ctrS zero ()
ctrS (suc n0) (init p i j) = init p i (memCtr j)
ctrS (suc n0) (lbot i)     = lbot i
ctrS (suc n0) (limp del d1 d2) =
  limp del
       (derPermS permSwap
         (ctrS n0 (derPermS (permTrans permSwap (permSkip permSwap)) d1)))
       (ctrS n0 d2)
-- principal = the first contracted copy
ctrS (suc n0) (rimp delHd d') =
  rimp delHd (ctrS n0 (ctrA n0 (invR' n0 (derPermS permSwap d'))))
-- principal = the second contracted copy
ctrS (suc n0) (rimp (delTl delHd) d') =
  rimp delHd (ctrS n0 (ctrA n0 (invR' n0 (derPermS permSwap d'))))
-- principal lies deeper in D
ctrS (suc n0) (rimp (delTl (delTl del3)) d') =
  rimp (delTl del3)
       (derPermS permSwap
         (ctrS n0 (derPermS (permTrans permSwap (permSkip permSwap)) d')))

------------------------------------------------------------------------
-- CUT ADMISSIBILITY (stage G3) -- the approach actually used (cleaner than a
-- full Gentzen commuting-conversion enumeration):
--
--   cut dispatches on the CUT FORMULA A (structural recursion on Form):
--     A = imp A1 A2 : INVERT.  invR' d1, invLl' d2, invLr' d2 expose the three
--         immediate premises; two cuts on the SMALLER A1, A2 finish.  No height
--         induction, NO commuting cases -- the invertibility lemmas already did
--         that work, height-preservingly.
--     A = bot      : botElimS (bot is never principal on the right).
--     A = at p     : cutAtom -- the ONLY part needing commuting.  An atom is
--         never principal in a logical rule, so we commute on d1's last rule
--         ALONE (d2 carried whole), recursing on d1's HEIGHT; the one leaf that
--         uses the head atom is an init, which contracts d2.  Two commuting
--         constructions (limp, rimp), each: weaken the premise to d1's context,
--         cut (smaller height), recombine with the rule on a fresh principal,
--         contract the duplicate.
--
-- CONSEQUENCE for attempt3 (Cons): a cut-free Der of a closed ATOM has, by the
-- subformula property, only atomic sequents -- the ATOMIC DERIVATION AtDer that
-- (EqSound) feeds to the CR terminal's Conv (attempt3 §13.4).

------------------------------------------------------------------------
-- Towards CUT (stage G3).  Height arithmetic + Prov (existential output height).

data Le : Nat -> Nat -> Set where
  leRefl : {n : Nat} -> Le n n
  leStep : {n m : Nat} -> Le n m -> Le n (suc m)

leZero : (m : Nat) -> Le zero m
leZero zero    = leRefl
leZero (suc m) = leStep (leZero m)

leSuc : {n m : Nat} -> Le n m -> Le (suc n) (suc m)
leSuc leRefl      = leRefl
leSuc (leStep le) = leStep (leSuc le)

maxN : Nat -> Nat -> Nat
maxN zero    m       = m
maxN (suc n) zero    = suc n
maxN (suc n) (suc m) = suc (maxN n m)

leMaxL : (n m : Nat) -> Le n (maxN n m)
leMaxL zero    m       = leZero m
leMaxL (suc n) zero    = leRefl
leMaxL (suc n) (suc m) = leSuc (leMaxL n m)

leMaxR : (n m : Nat) -> Le m (maxN n m)
leMaxR zero    m       = leRefl
leMaxR (suc n) zero    = leZero (suc n)
leMaxR (suc n) (suc m) = leSuc (leMaxR n m)

monoLe : {n m : Nat} {G D : List} -> Le n m -> Der n G D -> Der m G D
monoLe leRefl      d = d
monoLe (leStep le) d = mono (monoLe le d)

Prov : List -> List -> Set
Prov G D = Sigma Nat (\ n -> Der n G D)

limpP : {A' B' : Form} {G G0 D : List} ->
        Del (imp A' B') G G0 -> Prov G0 (A' :: D) -> Prov (B' :: G0) D -> Prov G D
limpP del (mkSig m1 p1) (mkSig m2 p2) =
  mkSig (suc (maxN m1 m2)) (limp del (monoLe (leMaxL m1 m2) p1) (monoLe (leMaxR m1 m2) p2))

rimpP : {A' B' : Form} {G D D0 : List} ->
        Del (imp A' B') D D0 -> Prov (A' :: G) (B' :: D0) -> Prov G D
rimpP del (mkSig m p) = mkSig (suc m) (rimp del p)

provPermA : {G G' D : List} -> Perm G G' -> Prov G D -> Prov G' D
provPermA perm (mkSig m p) = mkSig m (derPermA perm p)

provPermS : {G D D' : List} -> Perm D D' -> Prov G D -> Prov G D'
provPermS perm (mkSig m p) = mkSig m (derPermS perm p)

provCtrA : {A : Form} {G D : List} -> Prov (A :: A :: G) D -> Prov (A :: G) D
provCtrA (mkSig m p) = mkSig m (ctrA m p)

provCtrS : {A : Form} {G D : List} -> Prov G (A :: A :: D) -> Prov G (A :: D)
provCtrS (mkSig m p) = mkSig m (ctrS m p)

memToDel : {a : Form} {G : List} -> Mem a G -> Sigma List (\ G0 -> Del a G G0)
memToDel memHd     = mkSig _ delHd
memToDel (memTl m) = let r = memToDel m in mkSig _ (delTl (snd r))

-- Drop a bot from the head of the succedent (bot is never principal on the
-- right).  Height-preserving; this is the cut on the formula bot.
botElimS : (n : Nat) {G D : List} -> Der n G (bot :: D) -> Der n G D
botElimS zero ()
botElimS (suc n0) (init p i (memTl j0))   = init p i j0
botElimS (suc n0) (lbot i)                = lbot i
botElimS (suc n0) (limp del e1 e2)        =
  limp del (botElimS n0 (derPermS permSwap e1)) (botElimS n0 e2)
botElimS (suc n0) (rimp (delTl del'') e)  =
  rimp del'' (botElimS n0 (derPermS permSwap e))

------------------------------------------------------------------------
-- ATOMIC CUT (cut on an atom at p).  The atom is never principal in a logical
-- rule, so we just commute on d1's last rule (recursing on d1's height); the
-- only leaf that uses the head atom is an init, which contracts d2.

cutAtom : (p : Atom) (n1 n2 : Nat) {G D : List} ->
          Der n1 G (at p :: D) -> Der n2 (at p :: G) D -> Prov G D
cutAtom p (suc m1) n2 (lbot i)              d2 = mkSig (suc zero) (lbot i)
cutAtom p (suc m1) n2 (init q i (memTl j0)) d2 = mkSig (suc zero) (init q i j0)
cutAtom p (suc m1) n2 (init q i memHd)      d2 =
  let r   = memToDel i
      del = snd r
  in mkSig n2 (derPermA (permSym (delPerm del))
                 (ctrA n2 (derPermA (permSkip (delPerm del)) d2)))
cutAtom p (suc m1) n2 (limp {A = B1} {B = B2} del e1 e2) d2 =
  let e1w = derPermA (permSym (delPerm del)) (wkA (imp B1 B2) e1)
      e2w = derPermA (permTrans permSwap (permSkip (permSym (delPerm del))))
                     (wkA (imp B1 B2) e2)
      L   = cutAtom p m1 n2 (derPermS permSwap e1w) (wkS B1 d2)
      R   = cutAtom p m1 n2 e2w (derPermA permSwap (wkA B2 d2))
  in provPermA (permSym (delPerm del))
       (provCtrA (provPermA (permSkip (delPerm del)) (limpP delHd L R)))
cutAtom p (suc m1) n2 (rimp {A = B1} {B = B2} (delTl del'') e) d2 =
  let leftArr  = derPermS (permTrans (permSkip permSwap)
                            (permTrans permSwap (permSkip permSwap)))
                          (wkS (imp B1 B2) e)
      rightArr = derPermS (permSkip (delPerm del''))
                          (wkS B2 (derPermA permSwap (wkA B1 d2)))
      M = cutAtom p m1 n2 leftArr rightArr
  in provPermS (permSym (delPerm del'')) (provCtrS (rimpP delHd M))

------------------------------------------------------------------------
-- CUT ADMISSIBILITY.  Dispatch on the cut formula A (structural recursion):
--   imp -> two SMALLER cuts via invertibility (no commuting);
--   bot -> botElimS;  atom -> cutAtom.

cut : (A : Form) (n1 n2 : Nat) {G D : List} ->
      Der n1 G (A :: D) -> Der n2 (A :: G) D -> Prov G D
cut (at p)      n1 n2 d1 d2 = cutAtom p n1 n2 d1 d2
cut bot         n1 n2 d1 d2 = mkSig n1 (botElimS n1 d1)
cut (imp A1 A2) n1 n2 d1 d2 =
  let d1' = invR'  n1 d1     -- Der n1 (A1 :: G) (A2 :: D)
      f1  = invLl' n2 d2     -- Der n2 G (A1 :: D)
      f2  = invLr' n2 d2     -- Der n2 (A2 :: G) D
      g   = cut A1 n2 n1 (derPermS permSwap (wkS A2 f1)) d1'  -- Prov G (A2 :: D)
  in cut A2 (fst g) n2 (snd g) f2

-- Prov-level cut (existential heights on both sides) -- the convenient form for
-- the (Cons)/(EqSound) assembly: provability is closed under cut.
cutP : (A : Form) {G D : List} -> Prov G (A :: D) -> Prov (A :: G) D -> Prov G D
cutP A (mkSig n1 p1) (mkSig n2 p2) = cut A n1 n2 p1 p2
