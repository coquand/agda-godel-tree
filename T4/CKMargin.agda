{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CKMargin -- surprise-GII task (a), SUBTASK 3: the pigeonhole margin +
-- the day-range  r..N  restriction of the characteristic fold, instantiated
-- at the concrete enumerator  T4.EnumProg.enum .
--
-- This file finishes task (a) of  T4/SURPRISE-GII-HANDOFF.md  by wiring the
-- shipped pieces ( T4.DefInd.defInd ,  T4.CKProg 's  Post/isZero  flip ,
-- T4.CKFold 's  r..r+k  range discipline ,  T4.EnumProg 's  enum / Bnat /
-- coverage / size lemmas ) into:
--
--   (i)   the parameter instantiation   enum := EnumProg.enum ,  N := Bnat ,
--         M := Bnat - 1 ,  with a proof  Lt M N  ( the meta-pigeonhole margin :
--         strictly more days  0..N  than program slots  0..M ).
--   (ii)  the DAY-RANGE value fold  defCountFrom enum r k : Fun1  summing the
--         define-indicator over enum indices  r .. r+k  ( the shipped
--         T4.DefInd.defCount  folds the FIXED range  0..N ; the external
--         induction of clos-corrected.md peels programs one at a time and so
--         needs the SHRINKING range  r..N , exactly CKFold's  r..r+k
--         discipline applied at the VALUE level ), with its proved unfold
--         lemmas, and the per-day characteristic  CKFrom enum r k : Fun2  +
--         its bare-argument atom  ( cAp2f , two bare vars, as in  CKProg ).
--   (iii) the wiring of  enum_cover  ( re-exported ) and  enum_short
--         composed against the Lstar bridge to land on the object threshold
--         Lstar  used by the Chaitin/Size machinery.
--   (iv)  the  Lstar_meta <-> KGodel1BridgeDef.Lstar  bridge ( ENUM-SHIPPED.md
--         residual #1 ).  Per the slow-typecheck discipline
--         ( feedback_slow_typecheck_means_abstract_constants ) and because the
--         literal  Lstar = ap1 exp2 (natCode (fst boundDef))  must stay
--         SYMBOLIC -- forcing  exp2_natCode  would materialise the
--         astronomical  natCode (2 ^ fst boundDef)  -- the bridge is carried as
--         an explicit parameter  lstarLe : Deriv (leq (natCode Lstar_meta)
--         Lstar)  ( residual #1's recommended  leq  form ), keeping
--         Lstar_meta  abstract so  enum / progs  never unfold.  The wireup
--         ( task (d) ) discharges  lstarLe  at the concrete  Lstar_meta .
--
-- Reuses the shipped  defInd  ( T4.DefInd ),  isZero / Post / Fan / pi  shape
-- of  CKProg , and the  cAp2f / cVarc / cEqTm  code skeletons; the only new
-- content is the range index discipline and the meta-pigeonhole margin.

open import T4.Base
open import BRA3.ChurchLeq        using ( leq )
open import T4.KGodel1BridgeDef   using ( Lstar )

-- Lstar_meta : the abstract size budget ( = #-nodes bound of the enumerated
--              program codes ;  KGodel1BridgeDef.Lstar  is its object form ).
-- lstarLe    : the bridge  natCode Lstar_meta <= Lstar  ( residual #1 ).
module T4.CKMargin
  (Lstar_meta : Nat)
  (lstarLe    : Deriv (leq (natCode Lstar_meta) Lstar))
  where

open import BRA3.Church           using ( isZero ; pi ; sigma )
open import T4.LenR               using ( lenR )
open import T4.LeqMono            using ( leq_trans )
open import T4.Num                using ( num )
open import T4.Code               using ( codeFormula ; codeTerm )
open import T4.DefWit             using ( cEqTm ; cNeg )
open import T4.CgiClash           using ( cAp2f ; cVarc )
open import T4.DefInd             using ( defInd ; defInd_eq )
open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS ; ltSelf )

-- The concrete enumerator + its three correctness lemmas (Deriv-level), all
-- re-exported so downstream margin consumers see them through this module.
open import T4.EnumProg Lstar_meta public
  using ( enum ; Bnat ; Lst ; lnil ; lcons ; llen ; strsExact ; strsUpTo ; lapp
        ; enum_inAlph ; enum_short ; enum_cover )

------------------------------------------------------------------------
-- SECTION 0.  Local meta index addition (mirrors CKFold.natAdd, 3 lines).

natAdd : Nat -> Nat -> Nat
natAdd zero    m = m
natAdd (suc n) m = suc (natAdd n m)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 1.  The pigeonhole margin   N := Bnat ,  M := Bnat - 1 ,  Lt M N .
--
-- Bnat = llen (strsUpTo Lstar_meta)  is the number of enumerated program
-- codes (index range  Lt k Bnat ).  It is positive ( strsUpTo always contains
-- at least the leaf string  O ), so it has a predecessor  M = Bnat - 1 ;  the
-- margin  Lt M Bnat  is then  ltSelf M  transported along  Bnat = suc M .

-- Bnat is positive:  Lt zero Bnat .  (Pure structural list induction; with
-- Lstar_meta abstract,  strsUpTo Lstar_meta  stays symbolic -- the base case
-- O  string and the  lapp  cons-head carry the witness without unfolding.)
llen_lapp_pos :
  (xs ys : Lst Term) -> Lt zero (llen ys) -> Lt zero (llen (lapp xs ys))
llen_lapp_pos lnil         ys h = h
llen_lapp_pos (lcons z zs) ys h = ltZ (llen (lapp zs ys))

strsUpTo_pos : (n : Nat) -> Lt zero (llen (strsUpTo n))
strsUpTo_pos zero     = ltZ zero
strsUpTo_pos (suc n') = llen_lapp_pos (strsExact (suc n')) (strsUpTo n') (strsUpTo_pos n')

Bpos : Lt zero Bnat
Bpos = strsUpTo_pos Lstar_meta

-- The predecessor of a positive Nat, extracted from the  Lt zero _  proof.
predOf : (n : Nat) -> Lt zero n -> Nat
predOf (suc m) (ltZ .m) = m

predEq : (n : Nat) (h : Lt zero n) -> Eq n (suc (predOf n h))
predEq (suc m) (ltZ .m) = refl

-- The margin constants and the strict inequality.
N : Nat
N = Bnat

M : Nat
M = predOf Bnat Bpos

ltMN : Lt M N
ltMN = eqSubst (\ z -> Lt M z) (eqSym (predEq Bnat Bpos)) (ltSelf M)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 2.  enum_short, bridged to the object threshold  Lstar .
--   The size lemma  enum_short  targets  natCode Lstar_meta ;  composing with
--   the carried bridge  lstarLe  via  leq  transitivity lands on the object
--   Lstar  the Chaitin/Size machinery consumes ( residual #1 ).

enum_short_Lstar :
  (k : Nat) -> Lt k Bnat ->
  Deriv (leq (ap1 lenR (ap1 enum (natCode k))) Lstar)
enum_short_Lstar k klt =
  leq_trans (ap1 lenR (ap1 enum (natCode k))) (natCode Lstar_meta) Lstar
            (enum_short k klt) lstarLe

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 3.  The DAY-RANGE value fold  ( r .. r+k ),  reusing  defInd .
--
--   summandFrom idx j   : Fun1 ,  ap1 (summandFrom idx j) q
--                                 = defInd (idx (natCode j)) q          (PROVED)
--   defCountFrom idx r k: Fun1 ,  the running sum  sum_{j=r}^{r+k}
--                                 defInd(idx (natCode j), q)            (unfolds)
--
-- This is exactly  CKFold 's  KExpFrom / KCodeFrom  range discipline ( meta
-- recursion on the conjunct count  k ), but at the genuine "= O" VALUE level
-- (object  sigma  fold of  defInd ) rather than the formula-code level.  The
-- shipped  T4.DefInd.defCount = sumRec defInd idx  folds the FIXED range
-- 0..m  (object  m ); here the range  r..r+k  is META, so  defCountFrom  is a
-- Fun1  of the packaged argument  q = pi u x .

-- the  j-th summand as a  Fun1  of  q :   q |-> defInd (idx (natCode j)) q .
summandFrom : Fun1 -> Nat -> Fun1
summandFrom idx j = C defInd (compose1U idx (constN j)) I

summandFrom_eq :
  (idx : Fun1) (j : Nat) (q : Term) ->
  Deriv (eqF (ap1 (summandFrom idx j) q) (ap2 defInd (ap1 idx (natCode j)) q))
summandFrom_eq idx j q =
  let e0 : Deriv (eqF (ap1 (summandFrom idx j) q)
                      (ap2 defInd (ap1 (compose1U idx (constN j)) q) (ap1 I q)))
      e0 = ax_C defInd (compose1U idx (constN j)) I q

      headEq : Deriv (eqF (ap1 (compose1U idx (constN j)) q) (ap1 idx (natCode j)))
      headEq = ruleTrans (axComp idx (constN j) q) (cong1 idx (constN_eq j q))

      e1 : Deriv (eqF (ap2 defInd (ap1 (compose1U idx (constN j)) q) (ap1 I q))
                      (ap2 defInd (ap1 idx (natCode j)) (ap1 I q)))
      e1 = congL defInd (ap1 I q) headEq

      e2 : Deriv (eqF (ap2 defInd (ap1 idx (natCode j)) (ap1 I q))
                      (ap2 defInd (ap1 idx (natCode j)) q))
      e2 = congR defInd (ap1 idx (natCode j)) (axI q)
  in ruleTrans e0 (ruleTrans e1 e2)

-- the running sum over the range  r .. r+k  ( k+1 summands , largest index
-- outermost , mirroring  CKFold.KExpFrom 's orientation ).
defCountFrom : Fun1 -> Nat -> Nat -> Fun1
defCountFrom idx r zero    = summandFrom idx r
defCountFrom idx r (suc k) =
  C sigma (defCountFrom idx r k) (summandFrom idx (natAdd r (suc k)))

-- base ( k = 0 ):  the single summand at index  r .
defCountFrom_at_O :
  (idx : Fun1) (r : Nat) (q : Term) ->
  Deriv (eqF (ap1 (defCountFrom idx r zero) q) (ap2 defInd (ap1 idx (natCode r)) q))
defCountFrom_at_O idx r q = summandFrom_eq idx r q

-- step ( k -> k+1 ):  add the summand at the running top index  r+(k+1) .
defCountFrom_succ :
  (idx : Fun1) (r k : Nat) (q : Term) ->
  Deriv (eqF (ap1 (defCountFrom idx r (suc k)) q)
             (ap2 sigma (ap1 (defCountFrom idx r k) q)
                        (ap2 defInd (ap1 idx (natCode (natAdd r (suc k)))) q)))
defCountFrom_succ idx r k q =
  let e0 : Deriv (eqF (ap1 (defCountFrom idx r (suc k)) q)
                      (ap2 sigma (ap1 (defCountFrom idx r k) q)
                                 (ap1 (summandFrom idx (natAdd r (suc k))) q)))
      e0 = ax_C sigma (defCountFrom idx r k) (summandFrom idx (natAdd r (suc k))) q
  in ruleTrans e0
       (congR sigma (ap1 (defCountFrom idx r k) q)
              (summandFrom_eq idx (natAdd r (suc k)) q))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- SECTION 4.  The per-day characteristic  CKFrom : Fun2  and its atom.
--   ap2 (CKFrom idx r k) u x = isZero ( defCountFrom idx r k (pi u x) )
--   = O  iff some  p_j  ( r <= j <= r+k )  defines  u  in  x  steps
--   ( the  isZero  flip, native  O = false / s O = true , as in  CKProg ).
--   The atom is  cAp2f  ( BOTH vars bare ), matching  CKProg.charAtom2 .

CKFrom : Fun1 -> Nat -> Nat -> Fun2
CKFrom idx r k = Post isZero (Post (defCountFrom idx r k) pi)

CKFrom_eq :
  (idx : Fun1) (r k : Nat) (uT xT : Term) ->
  Deriv (eqF (ap2 (CKFrom idx r k) uT xT)
             (ap1 isZero (ap1 (defCountFrom idx r k) (ap2 pi uT xT))))
CKFrom_eq idx r k uT xT =
  let eOut : Deriv (eqF (ap2 (CKFrom idx r k) uT xT)
                        (ap1 isZero (ap2 (Post (defCountFrom idx r k) pi) uT xT)))
      eOut = axPost isZero (Post (defCountFrom idx r k) pi) uT xT

      eIn : Deriv (eqF (ap2 (Post (defCountFrom idx r k) pi) uT xT)
                       (ap1 (defCountFrom idx r k) (ap2 pi uT xT)))
      eIn = axPost (defCountFrom idx r k) pi uT xT
  in ruleTrans eOut (cong1 isZero eIn)

------------------------------------------------------------------------
-- SECTION 5.  The bare-argument atom over the CONCRETE enumerator.
--   CKr r k = CKFrom enum r k  is the day-r characteristic (program range
--   r..r+k of the finite set  enum ); the wireup (task (d)) takes  k := M - r
--   per day so the range is  r..M = r..(Bnat-1) .  Code identities by  refl
--   ( codeFormula / codeTerm match  cEqTm / cAp2f / cVarc ;  cO = O ).

CKr : Nat -> Nat -> Fun2
CKr = CKFrom enum

charAtomR : Nat -> Nat -> Nat -> Nat -> Formula
charAtomR r k i0 i1 = eqF (ap2 (CKr r k) (var i0) (var i1)) O

charAtomCodeR : Nat -> Nat -> Term -> Term -> Term
charAtomCodeR r k s0 s1 = cEqTm (cAp2f (CKr r k) s0 s1) O

-- both subjects sit as bare  cVarc  leaves under  cAp2f (CKr r k) .
charAtomR_at_vars :
  (r k i0 i1 : Nat) ->
  Eq (codeFormula (charAtomR r k i0 i1)) (charAtomCodeR r k (cVarc i0) (cVarc i1))
charAtomR_at_vars r k i0 i1 = refl

-- Step-2 target: subject installed num-raw  ap1 num x0 , run-length still
-- coded  cVarc x1  ( sbt_at_var_match  on x0,  sbt_at_var_nomatch  on x1).
charAtomCodeR_num_subj :
  (r k : Nat) (x0 : Term) (i1 : Nat) ->
  Eq (charAtomCodeR r k (ap1 num x0) (cVarc i1))
     (cEqTm (cAp2f (CKr r k) (ap1 num x0) (cVarc i1)) O)
charAtomCodeR_num_subj r k x0 i1 = refl

-- the negated atom -- the stage-predicate body  S(r) .
charNegR : Nat -> Nat -> Nat -> Nat -> Formula
charNegR r k i0 i1 = neg (charAtomR r k i0 i1)

charNegR_at_vars :
  (r k i0 i1 : Nat) ->
  Eq (codeFormula (charNegR r k i0 i1))
     (cNeg (cEqTm (cAp2f (CKr r k) (cVarc i0) (cVarc i1)) O))
charNegR_at_vars r k i0 i1 = refl
