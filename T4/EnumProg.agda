{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.EnumProg -- the foundational enumerator  enum : Fun1  of the
-- size-<= -L*  program CODES, with its three correctness lemmas.
--
-- This is the corrected, machine-buildable form of the  ENUM-PROBLEM
-- (see  T4/ENUM-STEP0-FINDINGS.md ).  STEP 0 established that the
-- literal  enum_cover  over  { c : InAlph c , lenR c <= L* }  is over an
-- INFINITE set (cell payloads in  ap1 s A  heads are unbounded and
-- uncounted), hence unprovable.  We enumerate over the  enc -image instead:
-- the program CODES  { enc t : nodes t <= L* } , equivalently the flat
-- right-nested tag-strings of length  <= L*  over the 3-symbol alphabet
--   Sigma_enc = { natCode tagLeaf , natCode tagUnary , natCode tagBinary } .
-- On this set  lenR  cleanly counts the length (=  nodes ; ProgEnc.lenR_enc).
--
-- DESIGN (per the findings, over-generate flat strings -> pure list induction):
--   * meta  strsExact n  : ALL flat tag-strings of length exactly  n ;
--     strsUpTo n  : their union for lengths  0..n .  ( strsUpTo Lstar_meta
--     is  progs , the program list. )
--   * meta membership  LMem  + the load-bearing coverage induction
--     enc_mem : enc t  IS one of the generated strings ( in  strsExact (nodes t) ).
--   * object  enum := lookupFrom 0 progs  : a uniform table-lookup  Fun1
--     ( index test by  natEqF ; entry returned by  constTermFun1 ), with
--     enum (natCode k) = progs[k]  PROVABLE.   Lstar_meta is kept ABSTRACT
--     (a Nat module parameter), so  progs / enum  never unfold to the
--     astronomical concrete table -- they stay symbolic and the proofs go
--     through by structural induction.
--
-- Lemmas (over the  enc -code domain;  Bnat = number of programs, index < Bnat):
--   enum_inAlph : the  k -th slot equals a genuine  InAlph  string.
--   enum_short  : the  k -th slot has  lenR <= natCode Lstar_meta .
--   enum_cover  : every  enc t  with  nodes t <= Lstar_meta  IS some slot.
--
-- This  enum / enum_correct  is the foundational input for the surprise-GII
-- proof; see  T4/clos-corrected.md  for how it is consumed (`CK` folds the
-- disjunction over the finite  S = enum ; the meta-pigeonhole bound  N  comes
-- from the finite index range).

open import T4.Base

module T4.EnumProg (Lstar_meta : Nat) where

open import T4.LenR        using ( lenR ; lenR_at_O ; lenR_at_node )
open import T4.ProgParse   using ( InAlph ; iaO ; iaS ; iaPi )
open import T4.ProgEnc     using ( enc ; encApp ; nodes
                                   ; tagLeaf ; tagUnary ; tagBinary ; addN_assoc )
open import T4.Thm12.ConstTermFun1 using
  ( NoVar ; NoVar_natCode ; NoVarAnd ; mkAnd ; constTermFun1 ; constTermFun1_eq )

open import BRA3.Church        using ( pi ; sub )
open import BRA3.ChurchLeq     using ( leq ; T76 )
open import BRA3.Code.Tag      using ( addN )
open import BRA3.Code.NatLemmas using ( addN_zero_right ; addN_suc_right )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq ; NatNeqWitness ; gtW )
open import BRA3.RuleInst2     using ( NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right )

open import T4.SurpriseG2.MetaPigeonhole using ( Lt ; ltZ ; ltS ; ltAbsurd ; ltPred )
open import T4.PHP           using ( succ_mono ; leq_eqL )

------------------------------------------------------------------------
-- SECTION 0.  Local meta-logic (Sigma / And / Or) and lists.

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

And : Set -> Set -> Set
And P Q = Sigma P (\ _ -> Q)

data Or (P Q : Set) : Set where
  inl : P -> Or P Q
  inr : Q -> Or P Q

data Lst (A : Set) : Set where
  lnil  : Lst A
  lcons : A -> Lst A -> Lst A

lapp : {A : Set} -> Lst A -> Lst A -> Lst A
lapp lnil         ys = ys
lapp (lcons x xs) ys = lcons x (lapp xs ys)

llen : {A : Set} -> Lst A -> Nat
llen lnil         = zero
llen (lcons _ xs) = suc (llen xs)

data LMem {A : Set} (x : A) : Lst A -> Set where
  lhere  : (xs : Lst A) -> LMem x (lcons x xs)
  lthere : (y : A) (xs : Lst A) -> LMem x xs -> LMem x (lcons y xs)

-- the k-th element (default  O  out of range).
nthD : Lst Term -> Nat -> Term
nthD lnil         k       = O
nthD (lcons p ps) zero    = p
nthD (lcons p ps) (suc k) = nthD ps k

-- list-membership of  lapp .
lapp_mem :
  (x : Term) (xs ys : Lst Term) ->
  LMem x (lapp xs ys) -> Or (LMem x xs) (LMem x ys)
lapp_mem x lnil         ys mem               = inr mem
lapp_mem x (lcons z zs) ys (lhere .(lapp zs ys)) = inl (lhere zs)
lapp_mem x (lcons z zs) ys (lthere .z .(lapp zs ys) m) with lapp_mem x zs ys m
... | inl mz = inl (lthere z zs mz)
... | inr my = inr my

lapp_introL :
  (x : Term) (xs ys : Lst Term) -> LMem x xs -> LMem x (lapp xs ys)
lapp_introL x .(lcons x zs)  ys (lhere zs)        = lhere (lapp zs ys)
lapp_introL x .(lcons y zs)  ys (lthere y zs m)   = lthere y (lapp zs ys) (lapp_introL x zs ys m)

lapp_introR :
  (x : Term) (xs ys : Lst Term) -> LMem x ys -> LMem x (lapp xs ys)
lapp_introR x lnil         ys m = m
lapp_introR x (lcons z zs) ys m = lthere z (lapp zs ys) (lapp_introR x zs ys m)

-- nthD is a member when the index is in range.
nthD_mem :
  (ps : Lst Term) (k : Nat) -> Lt k (llen ps) -> LMem (nthD ps k) ps
nthD_mem lnil         k       lt = ltAbsurd lt
nthD_mem (lcons p ps) zero    lt = lhere ps
nthD_mem (lcons p ps) (suc k) lt = lthere p ps (nthD_mem ps k (ltPred lt))

-- a member yields a concrete index with  nthD ps k = x .
memToIndex :
  (ps : Lst Term) (x : Term) -> LMem x ps ->
  Sigma Nat (\ k -> And (Lt k (llen ps)) (Eq (nthD ps k) x))
memToIndex .(lcons x xs)  x (lhere xs)        = mkSigma zero (mkSigma (ltZ (llen xs)) refl)
memToIndex .(lcons y xs)  x (lthere y xs m)   with memToIndex xs x m
... | mkSigma k (mkSigma lt eq) = mkSigma (suc k) (mkSigma (ltS k (llen xs) lt) eq)

------------------------------------------------------------------------
-- SECTION 1.  The string generator.   cons sigma c = ap2 pi sigma c .

cons : Term -> Term -> Term
cons a b = ap2 pi a b

tag1 tag2 tag3 : Term
tag1 = natCode tagLeaf
tag2 = natCode tagUnary
tag3 = natCode tagBinary

-- the three one-symbol extensions of a tail  c .
block3 : Term -> Lst Term
block3 c = lcons (cons tag1 c) (lcons (cons tag2 c) (lcons (cons tag3 c) lnil))

-- prepend each of the 3 tags to each tail.
extendAll : Lst Term -> Lst Term
extendAll lnil         = lnil
extendAll (lcons c cs) = lapp (block3 c) (extendAll cs)

strsExact : Nat -> Lst Term
strsExact zero    = lcons O lnil
strsExact (suc m) = extendAll (strsExact m)

strsUpTo : Nat -> Lst Term
strsUpTo zero    = strsExact zero
strsUpTo (suc n) = lapp (strsExact (suc n)) (strsUpTo n)

------------------------------------------------------------------------
-- SECTION 2.  Membership in the generator -- elimination.

block3_mem :
  (x c : Term) -> LMem x (block3 c) ->
  Or (Eq x (cons tag1 c)) (Or (Eq x (cons tag2 c)) (Eq x (cons tag3 c)))
block3_mem _ c (lhere _)                          = inl refl
block3_mem _ c (lthere _ _ (lhere _))             = inr (inl refl)
block3_mem _ c (lthere _ _ (lthere _ _ (lhere _))) = inr (inr refl)
block3_mem _ c (lthere _ _ (lthere _ _ (lthere _ _ ())))

extendAll_mem :
  (x : Term) (cs : Lst Term) -> LMem x (extendAll cs) ->
  Sigma Term (\ c -> And (LMem c cs)
    (Or (Eq x (cons tag1 c)) (Or (Eq x (cons tag2 c)) (Eq x (cons tag3 c)))))
extendAll_mem x lnil ()
extendAll_mem x (lcons c cs) mem with lapp_mem x (block3 c) (extendAll cs) mem
... | inl mb = mkSigma c (mkSigma (lhere cs) (block3_mem x c mb))
... | inr mr with extendAll_mem x cs mr
...   | mkSigma c0 (mkSigma memc0 tagOr0) =
        mkSigma c0 (mkSigma (lthere c cs memc0) tagOr0)

------------------------------------------------------------------------
-- SECTION 3.  Membership in the generator -- introduction (coverage).

extendAll_intro1 :
  (c : Term) (cs : Lst Term) -> LMem c cs -> LMem (cons tag1 c) (extendAll cs)
extendAll_intro1 c .(lcons c xs) (lhere xs) =
  lapp_introL (cons tag1 c) (block3 c) (extendAll xs) (lhere _)
extendAll_intro1 c .(lcons y xs) (lthere y xs m) =
  lapp_introR (cons tag1 c) (block3 y) (extendAll xs) (extendAll_intro1 c xs m)

extendAll_intro2 :
  (c : Term) (cs : Lst Term) -> LMem c cs -> LMem (cons tag2 c) (extendAll cs)
extendAll_intro2 c .(lcons c xs) (lhere xs) =
  lapp_introL (cons tag2 c) (block3 c) (extendAll xs) (lthere _ _ (lhere _))
extendAll_intro2 c .(lcons y xs) (lthere y xs m) =
  lapp_introR (cons tag2 c) (block3 y) (extendAll xs) (extendAll_intro2 c xs m)

extendAll_intro3 :
  (c : Term) (cs : Lst Term) -> LMem c cs -> LMem (cons tag3 c) (extendAll cs)
extendAll_intro3 c .(lcons c xs) (lhere xs) =
  lapp_introL (cons tag3 c) (block3 c) (extendAll xs) (lthere _ _ (lthere _ _ (lhere _)))
extendAll_intro3 c .(lcons y xs) (lthere y xs m) =
  lapp_introR (cons tag3 c) (block3 y) (extendAll xs) (extendAll_intro3 c xs m)

-- enc t  is one of the generated strings.   ( encApp -threaded form,
-- exactly mirroring  ProgEnc.lenR_encApp . )
encApp_mem :
  (t rest : Term) (n : Nat) ->
  LMem rest (strsExact n) -> LMem (encApp t rest) (strsExact (addN (nodes t) n))
encApp_mem O          rest n mem = extendAll_intro1 rest (strsExact n) mem
encApp_mem (var k)    rest n mem = extendAll_intro1 rest (strsExact n) mem
encApp_mem (ap1 f t)  rest n mem =
  extendAll_intro2 (encApp t rest) (strsExact (addN (nodes t) n))
                   (encApp_mem t rest n mem)
encApp_mem (ap2 g a b) rest n mem =
  let inner_a : LMem (encApp a (encApp b rest))
                     (strsExact (addN (nodes a) (addN (nodes b) n)))
      inner_a = encApp_mem a (encApp b rest) (addN (nodes b) n)
                          (encApp_mem b rest n mem)
      inner_a' : LMem (encApp a (encApp b rest))
                      (strsExact (addN (addN (nodes a) (nodes b)) n))
      inner_a' = eqSubst (\ z -> LMem (encApp a (encApp b rest)) (strsExact z))
                         (addN_assoc (nodes a) (nodes b) n) inner_a
  in extendAll_intro3 (encApp a (encApp b rest))
                      (strsExact (addN (addN (nodes a) (nodes b)) n)) inner_a'

enc_mem : (t : Term) -> LMem (enc t) (strsExact (nodes t))
enc_mem t =
  eqSubst (\ mm -> LMem (encApp t O) (strsExact mm))
          (addN_zero_right (nodes t))
          (encApp_mem t O zero (lhere lnil))

-- strsExact m  is contained in  strsUpTo n  when  m <= n .
leZeroEq : (m : Nat) -> NatLe m zero -> Eq m zero
leZeroEq zero     le = refl
leZeroEq (suc m') ()

leSucCase : (m n : Nat) -> NatLe m (suc n) -> Or (Eq m (suc n)) (NatLe m n)
leSucCase zero     n le           = inr (le-zero n)
leSucCase (suc m') zero (le-suc h) = inl (eqCong suc (leZeroEq m' h))
leSucCase (suc m') (suc n') (le-suc h) with leSucCase m' n' h
... | inl e  = inl (eqCong suc e)
... | inr l  = inr (le-suc l)

exactSub :
  (m n : Nat) -> NatLe m n -> (x : Term) ->
  LMem x (strsExact m) -> LMem x (strsUpTo n)
exactSub m zero    le x mem =
  eqSubst (\ mm -> LMem x (strsExact mm)) (leZeroEq m le) mem
exactSub m (suc n') le x mem with leSucCase m n' le
... | inl eqM =
      lapp_introL x (strsExact (suc n')) (strsUpTo n')
        (eqSubst (\ mm -> LMem x (strsExact mm)) eqM mem)
... | inr le' =
      lapp_introR x (strsExact (suc n')) (strsUpTo n')
        (exactSub m n' le' x mem)

------------------------------------------------------------------------
-- SECTION 4.  Entry properties:  every generated string is  InAlph ,
-- NoVar , and has  lenR = its length.

Props : Term -> Nat -> Set
Props x m = And (InAlph x) (And (NoVar x) (Deriv (eqF (ap1 lenR x) (natCode m))))

-- per-tag:  cons tagj c  is  InAlph / NoVar , and  lenR (cons tagj c) = s (lenR c) .
propsCons1 :
  (m' : Nat) (c : Term) -> InAlph c -> NoVar c ->
  Deriv (eqF (ap1 lenR c) (natCode m')) -> Props (cons tag1 c) (suc m')
propsCons1 m' c iac nvc lrc =
  mkSigma (iaPi tag1 c (iaS O iaO) iac)
    (mkSigma (mkAnd (NoVar_natCode tagLeaf) nvc)
             (ruleTrans (lenR_at_node O c) (cong1 s lrc)))

propsCons2 :
  (m' : Nat) (c : Term) -> InAlph c -> NoVar c ->
  Deriv (eqF (ap1 lenR c) (natCode m')) -> Props (cons tag2 c) (suc m')
propsCons2 m' c iac nvc lrc =
  mkSigma (iaPi tag2 c (iaS (ap1 s O) (iaS O iaO)) iac)
    (mkSigma (mkAnd (NoVar_natCode tagUnary) nvc)
             (ruleTrans (lenR_at_node (ap1 s O) c) (cong1 s lrc)))

propsCons3 :
  (m' : Nat) (c : Term) -> InAlph c -> NoVar c ->
  Deriv (eqF (ap1 lenR c) (natCode m')) -> Props (cons tag3 c) (suc m')
propsCons3 m' c iac nvc lrc =
  mkSigma (iaPi tag3 c (iaS (ap1 s (ap1 s O)) (iaS (ap1 s O) (iaS O iaO))) iac)
    (mkSigma (mkAnd (NoVar_natCode tagBinary) nvc)
             (ruleTrans (lenR_at_node (ap1 s (ap1 s O)) c) (cong1 s lrc)))

exactProps :
  (m : Nat) (x : Term) -> LMem x (strsExact m) -> Props x m
exactProps zero    .O (lhere .lnil)        = mkSigma iaO (mkSigma tt lenR_at_O)
exactProps zero    x  (lthere .O .lnil ())
exactProps (suc m') x mem with extendAll_mem x (strsExact m') mem
... | mkSigma c (mkSigma memc tagOr) with exactProps m' c memc
...   | mkSigma iac (mkSigma nvc lrc) with tagOr
...     | inl e1 =
          eqSubst (\ z -> Props z (suc m')) (eqSym e1) (propsCons1 m' c iac nvc lrc)
...     | inr (inl e2) =
          eqSubst (\ z -> Props z (suc m')) (eqSym e2) (propsCons2 m' c iac nvc lrc)
...     | inr (inr e3) =
          eqSubst (\ z -> Props z (suc m')) (eqSym e3) (propsCons3 m' c iac nvc lrc)

-- lift to  strsUpTo : InAlph , NoVar , and  lenR = natCode m  for some  m <= n .
UpProps : Nat -> Term -> Set
UpProps n x =
  And (InAlph x)
    (And (NoVar x)
      (Sigma Nat (\ m -> And (NatLe m n) (Deriv (eqF (ap1 lenR x) (natCode m))))))

upToProps : (n : Nat) (x : Term) -> LMem x (strsUpTo n) -> UpProps n x
upToProps zero x mem with exactProps zero x mem
... | mkSigma iac (mkSigma nvc lr) =
      mkSigma iac (mkSigma nvc (mkSigma zero (mkSigma (le-zero zero) lr)))
upToProps (suc n') x mem with lapp_mem x (strsExact (suc n')) (strsUpTo n') mem
... | inl mE with exactProps (suc n') x mE
...   | mkSigma iac (mkSigma nvc lr) =
        mkSigma iac (mkSigma nvc
          (mkSigma (suc n') (mkSigma (le-refl (suc n')) lr)))
upToProps (suc n') x mem | inr mU with upToProps n' x mU
... | mkSigma iac (mkSigma nvc (mkSigma m (mkSigma lem lr))) =
      mkSigma iac (mkSigma nvc (mkSigma m (mkSigma (le-suc-right lem) lr)))

------------------------------------------------------------------------
-- SECTION 5.  The object table-lookup  Fun1 .

-- index equality test :  ap1 (isEqF i) (natCode k) = natEqF (natCode k) (natCode i) .
isEqF : Nat -> Fun1
isEqF i = C natEqF I (constN i)

isEqF_eq :
  (i k : Nat) ->
  Deriv (eqF (ap1 (isEqF i) (natCode k)) (ap2 natEqF (natCode k) (natCode i)))
isEqF_eq i k =
  ruleTrans (ax_C natEqF I (constN i) (natCode k))
    (ruleTrans (congL natEqF (ap1 (constN i) (natCode k)) (axI (natCode k)))
               (congR natEqF (natCode k) (constN_eq i (natCode k))))

isEqF_match : (i : Nat) -> Deriv (eqF (ap1 (isEqF i) (natCode i)) (ap1 s O))
isEqF_match i = ruleTrans (isEqF_eq i i) (natEq_eq i)

isEqF_neq :
  (i k : Nat) -> NatNeqWitness k i -> Deriv (eqF (ap1 (isEqF i) (natCode k)) O)
isEqF_neq i k w = ruleTrans (isEqF_eq i k) (natEqF_at_neq k i w)

-- the table.   lookupFrom i ps  tests  index == i ?  return head : recurse .
lookupFrom : Nat -> Lst Term -> Fun1
lookupFrom i lnil         = Z
lookupFrom i (lcons p ps) =
  C condFork (C pi (constTermFun1 p) (lookupFrom (suc i) ps)) (isEqF i)

-- lookupFrom i ps  at index  addN k i  returns  nthD ps k  ( k in range ).
lookupFrom_at :
  (ps : Lst Term) (i k : Nat) -> Lt k (llen ps) ->
  ((c : Term) -> LMem c ps -> NoVar c) ->
  Deriv (eqF (ap1 (lookupFrom i ps) (natCode (addN k i))) (nthD ps k))
lookupFrom_at lnil i k lt nv = ltAbsurd lt
lookupFrom_at (lcons p ps) i zero lt nv =
  let Z' : Fun1
      Z' = C pi (constTermFun1 p) (lookupFrom (suc i) ps)
      b1 : Deriv (eqF (ap1 (lookupFrom i (lcons p ps)) (natCode i))
                       (ap2 condFork (ap1 Z' (natCode i)) (ap1 (isEqF i) (natCode i))))
      b1 = ax_C condFork Z' (isEqF i) (natCode i)
      b2 : Deriv (eqF (ap2 condFork (ap1 Z' (natCode i)) (ap1 (isEqF i) (natCode i)))
                       (ap2 condFork (ap1 Z' (natCode i)) (ap1 s O)))
      b2 = congR condFork (ap1 Z' (natCode i)) (isEqF_match i)
      b3 : Deriv (eqF (ap2 condFork (ap1 Z' (natCode i)) (ap1 s O))
                       (ap1 Fst (ap1 Z' (natCode i))))
      b3 = condFork_true_nc (ap1 Z' (natCode i)) O
      b4 : Deriv (eqF (ap1 Z' (natCode i))
                       (ap2 pi (ap1 (constTermFun1 p) (natCode i))
                               (ap1 (lookupFrom (suc i) ps) (natCode i))))
      b4 = ax_C pi (constTermFun1 p) (lookupFrom (suc i) ps) (natCode i)
      b5 : Deriv (eqF (ap1 Fst (ap1 Z' (natCode i)))
                       (ap1 (constTermFun1 p) (natCode i)))
      b5 = ruleTrans (cong1 Fst b4)
                     (axFst (ap1 (constTermFun1 p) (natCode i))
                            (ap1 (lookupFrom (suc i) ps) (natCode i)))
      b6 : Deriv (eqF (ap1 (constTermFun1 p) (natCode i)) p)
      b6 = constTermFun1_eq p (nv p (lhere ps)) (natCode i)
  in ruleTrans b1 (ruleTrans b2 (ruleTrans b3 (ruleTrans b5 b6)))
lookupFrom_at (lcons p ps) i (suc k') lt nv =
  let idx : Nat
      idx = suc (addN k' i)            -- = addN (suc k') i
      Z' : Fun1
      Z' = C pi (constTermFun1 p) (lookupFrom (suc i) ps)
      ihRaw : Deriv (eqF (ap1 (lookupFrom (suc i) ps) (natCode (addN k' (suc i))))
                          (nthD ps k'))
      ihRaw = lookupFrom_at ps (suc i) k' (ltPred lt)
                            (\ c m -> nv c (lthere p ps m))
      ih : Deriv (eqF (ap1 (lookupFrom (suc i) ps) (natCode idx)) (nthD ps k'))
      ih = eqSubst (\ z -> Deriv (eqF (ap1 (lookupFrom (suc i) ps) (natCode z))
                                       (nthD ps k')))
                   (addN_suc_right k' i) ihRaw
      e1 : Deriv (eqF (ap1 (lookupFrom i (lcons p ps)) (natCode idx))
                       (ap2 condFork (ap1 Z' (natCode idx)) (ap1 (isEqF i) (natCode idx))))
      e1 = ax_C condFork Z' (isEqF i) (natCode idx)
      e2 : Deriv (eqF (ap2 condFork (ap1 Z' (natCode idx)) (ap1 (isEqF i) (natCode idx)))
                       (ap2 condFork (ap1 Z' (natCode idx)) O))
      e2 = congR condFork (ap1 Z' (natCode idx)) (isEqF_neq i idx (gtW k' refl))
      e3 : Deriv (eqF (ap2 condFork (ap1 Z' (natCode idx)) O)
                       (ap1 Snd (ap1 Z' (natCode idx))))
      e3 = condFork_false (ap1 Z' (natCode idx))
      e4 : Deriv (eqF (ap1 Z' (natCode idx))
                       (ap2 pi (ap1 (constTermFun1 p) (natCode idx))
                               (ap1 (lookupFrom (suc i) ps) (natCode idx))))
      e4 = ax_C pi (constTermFun1 p) (lookupFrom (suc i) ps) (natCode idx)
      e5 : Deriv (eqF (ap1 Snd (ap1 Z' (natCode idx)))
                       (ap1 (lookupFrom (suc i) ps) (natCode idx)))
      e5 = ruleTrans (cong1 Snd e4)
                     (axSnd (ap1 (constTermFun1 p) (natCode idx))
                            (ap1 (lookupFrom (suc i) ps) (natCode idx)))
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans e5 ih)))

------------------------------------------------------------------------
-- SECTION 6.  The enumerator and its three correctness lemmas.

progs : Lst Term
progs = strsUpTo Lstar_meta

enum : Fun1
enum = lookupFrom zero progs

Bnat : Nat
Bnat = llen progs

allNVprogs : (c : Term) -> LMem c progs -> NoVar c
allNVprogs c mem = fst (snd (upToProps Lstar_meta c mem))

-- enum (natCode k) = progs[k]  ( k in range ).
enumAt :
  (k : Nat) -> Lt k Bnat -> Deriv (eqF (ap1 enum (natCode k)) (nthD progs k))
enumAt k klt =
  eqSubst (\ z -> Deriv (eqF (ap1 (lookupFrom zero progs) (natCode z)) (nthD progs k)))
          (addN_zero_right k)
          (lookupFrom_at progs zero k klt allNVprogs)

-- numeric helper :  NatLe m n  ->  Deriv (leq (natCode m) (natCode n)) .
leqZero : (n : Nat) -> Deriv (leq O (natCode n))
leqZero n = ruleInst 0 (natCode n) T76

leqNatCode : (m n : Nat) -> NatLe m n -> Deriv (leq (natCode m) (natCode n))
leqNatCode zero     n        _         = leqZero n
leqNatCode (suc m') zero     ()
leqNatCode (suc m') (suc n') (le-suc h) =
  succ_mono (natCode m') (natCode n') (leqNatCode m' n' h)

------------------------------------------------------------------------
-- enum_inAlph :  the  k -th slot equals a genuine  InAlph  string.

enum_inAlph :
  (k : Nat) -> Lt k Bnat ->
  Sigma Term (\ c -> And (InAlph c) (Deriv (eqF (ap1 enum (natCode k)) c)))
enum_inAlph k klt =
  mkSigma (nthD progs k)
    (mkSigma (fst (upToProps Lstar_meta (nthD progs k) (nthD_mem progs k klt)))
             (enumAt k klt))

------------------------------------------------------------------------
-- enum_short :  the  k -th slot has  lenR <= natCode Lstar_meta .

enum_short :
  (k : Nat) -> Lt k Bnat ->
  Deriv (leq (ap1 lenR (ap1 enum (natCode k))) (natCode Lstar_meta))
enum_short k klt with upToProps Lstar_meta (nthD progs k) (nthD_mem progs k klt)
... | mkSigma _ (mkSigma _ (mkSigma m (mkSigma lem lr))) =
      let eqLR : Deriv (eqF (ap1 lenR (ap1 enum (natCode k))) (natCode m))
          eqLR = ruleTrans (cong1 lenR (enumAt k klt)) lr
      in leq_eqL (ap1 lenR (ap1 enum (natCode k))) (natCode m) (natCode Lstar_meta)
                 eqLR (leqNatCode m Lstar_meta lem)

------------------------------------------------------------------------
-- enum_cover :  every  enc t  with  nodes t <= Lstar_meta  IS some slot.
-- (The load-bearing property.)

enum_cover :
  (t : Term) -> InAlph t -> NatLe (nodes t) Lstar_meta ->
  Sigma Nat (\ k -> And (Lt k Bnat) (Deriv (eqF (ap1 enum (natCode k)) (enc t))))
enum_cover t iat le with
  memToIndex progs (enc t)
    (exactSub (nodes t) Lstar_meta le (enc t) (enc_mem t))
... | mkSigma k (mkSigma klt eqk) =
      mkSigma k (mkSigma klt
        (eqSubst (\ z -> Deriv (eqF (ap1 enum (natCode k)) z)) eqk (enumAt k klt)))
