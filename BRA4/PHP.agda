{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.PHP -- the (P1) object pigeonhole spike for Gate-1
-- (see GATE1-COUNTING-FORMULATION.md).
--
-- PURPOSE.  De-risk the combinatorial heart of the counting argument: does
-- a finite-pigeonhole-style fact have a CLEAN, quantifier-free BRA `Deriv`?
-- We answer YES for the MONOTONE pigeonhole, which is the core engine:
--
--   * dom      : a strictly-increasing object function dominates the
--                identity --  n <= g n  -- proved by induction.
--   * mono_php : hence  g  cannot map  {0,...,n}  into  {0,...,n-1}
--                (i.e.  g n < n  is contradictory) -- the pigeonhole.
--
-- This is Sigma_1-FREE (no `thmT`, no provability): pure BRA arithmetic
-- (`leq` / `T76` / `T78` / `T84` / `notLeqSucSelf`).  The full
-- arbitrary-injection PHP reduces to this via a sort/rank step (deferred);
-- and the Sigma_1 layer (P2) + Con-injectivity (P3) sit on top, per the
-- formulation note.  The point of THIS file is only that the counting core
-- itself is clean BRA -- it is.
--
-- The strict-increase hypothesis is supplied as a meta-family `ginc`
--   (n : Nat) -> Deriv (leq (s (g (natCode n))) (g (natCode (suc n)))) ,
-- i.e.  g(n) < g(n+1)  at every numeral, and  g  is an arbitrary `Fun1`.
-- Induction is on the meta `Nat`, mirroring the project's `natCode`
-- meta-inductions (lenR_binMeta / exp2_natCode); the variable-bound object
-- form needed by (P2) uses the established c-renaming pattern (BRA4.Stability).

module BRA4.PHP where

open import BRA4.Base
open import BRA4.Code     using ( falseF )
open import BRA4.LeqMono  using ( leq_trans )

open import BRA3.Church       using ( sub ; sigma ; T33 )
open import BRA3.ChurchLeq    using ( leq ; T76 )
open import BRA3.ChurchSubSucc using ( T_sub_O ; T57sub )
open import BRA3.ChurchT73    using ( T73 )
open import BRA3.ChurchT78    using ( T78 )
open import BRA3.ChurchT87    using ( notLeqSucSelf )
open import BRA3.Numerals     using ( sigma_natCode ; numEq )
open import BRA3.Code.Tag     using ( addN )
open import BRA3.RuleInst2    using
  ( ruleInst2 ; NatLe ; le-zero ; le-suc ; le-refl ; le-suc-right )
open import BRA3.Logic        using ( eqSymImp )
open import BRA3.Contrapositive using
  ( axExFalso ; axContrapos ; DNE ; bComb ; liftP )

------------------------------------------------------------------------
-- succ_mono :  leq a b  ->  leq (s a) (s b) , for ANY terms a, b.
--
-- T78 has only var 0, var 1, so the simultaneous ruleInst2 substitutes
-- them by  a, b  verbatim -- no capture even if a, b mention var 0/1.

succ_mono :
  (a b : Term) -> Deriv (leq a b) -> Deriv (leq (ap1 s a) (ap1 s b))
succ_mono a b lab = mp (ruleInst2 0 a 1 b refl T78) lab

------------------------------------------------------------------------
-- dom :  a strictly-increasing  g  dominates the identity.
--
--   leq (natCode n) (ap1 g (natCode n))    for every  n .
--
-- Base  n = 0 :  leq O (g O)  -- 0 is below everything (T76).
-- Step  n+1   :  natCode (suc n) = s (natCode n) , and
--   s (natCode n) <= s (g (natCode n))            [succ_mono on IH]
--               <= g (natCode (suc n))            [ginc n]
--   so by leq_trans  s (natCode n) <= g (natCode (suc n)) .

dom :
  (g : Fun1) ->
  (ginc : (n : Nat) ->
    Deriv (leq (ap1 s (ap1 g (natCode n))) (ap1 g (natCode (suc n))))) ->
  (n : Nat) ->
  Deriv (leq (natCode n) (ap1 g (natCode n)))
dom g ginc zero =
  ruleInst 0 (ap1 g O) T76
dom g ginc (suc m) =
  let ih : Deriv (leq (natCode m) (ap1 g (natCode m)))
      ih = dom g ginc m

      s1 : Deriv (leq (ap1 s (natCode m)) (ap1 s (ap1 g (natCode m))))
      s1 = succ_mono (natCode m) (ap1 g (natCode m)) ih

      s2 : Deriv (leq (ap1 s (ap1 g (natCode m))) (ap1 g (natCode (suc m))))
      s2 = ginc m
  in leq_trans (ap1 s (natCode m))
               (ap1 s (ap1 g (natCode m)))
               (ap1 g (natCode (suc m)))
               s1 s2

------------------------------------------------------------------------
-- mono_php :  the pigeonhole.  A strictly-increasing  g  cannot squeeze
-- {0,...,n} into {0,...,n-1}:  the hypothesis  g(n) < n  (i.e.
--  leq (s (g n)) n ) is contradictory.
--
--   dom n           :  n <= g n
--   hyp             :  s (g n) <= n
--   leq_trans       :  s (g n) <= g n           -- i.e.  g n < g n
--   notLeqSucSelf   :  neg (leq (s (g n)) (g n))
--   axExFalso       :  contradiction  ->  falseF

mono_php :
  (g : Fun1) ->
  (ginc : (n : Nat) ->
    Deriv (leq (ap1 s (ap1 g (natCode n))) (ap1 g (natCode (suc n))))) ->
  (n : Nat) ->
  Deriv (leq (ap1 s (ap1 g (natCode n))) (natCode n)) ->
  Deriv falseF
mono_php g ginc n hyp =
  let gn : Term
      gn = ap1 g (natCode n)

      dn : Deriv (leq (natCode n) gn)
      dn = dom g ginc n

      -- s (g n) <= n <= g n  =>  s (g n) <= g n.
      bad : Deriv (leq (ap1 s gn) gn)
      bad = leq_trans (ap1 s gn) (natCode n) gn hyp dn

      -- neg (leq (s (g n)) (g n)).
      irr : Deriv (neg (leq (ap1 s gn) gn))
      irr = ruleInst 0 gn notLeqSucSelf

      exF : Deriv (imp (leq (ap1 s gn) gn) (imp (neg (leq (ap1 s gn) gn)) falseF))
      exF = axExFalso (leq (ap1 s gn) gn) falseF
  in mp (mp exF bad) irr

------------------------------------------------------------------------
------------------------------------------------------------------------
-- ARBITRARY-INJECTION pigeonhole via route R3 (count-below + induction).
--
-- See GATE1-COUNTING-FORMULATION.md (P1) and the memory note
-- project_bra4_krivine_models_inside_models.md ("GATE-1 (a)-FORK
-- RESOLVED").  The injection  idx  arising in the Berry argument is NOT
-- monotone (ranks of adversarial naming formulas), so  mono_php  above
-- does not suffice; we need the arbitrary-injection pigeonhole.
--
-- Route R3:  count below  t .  For an arbitrary  idx : Fun1  and a
-- numeral codomain bound  N  define
--
--    C(t)  =  #{ j <= N : idx j < t }   =   sum_{j=0}^{N} [ idx j < t ]
--
-- as a sum of object 0/1 INDICATORS (Skolem 1923, BRA4/Skolem23.pdf,
-- Df. 2:  (a < b+1) = (a < b) + (a = b) -- recursive 0/1 predicates).
-- The three facts
--    C(0) = 0 ;
--    C(t+1) <= s (C t)        [unit step -- consumes INJECTIVITY] ;
--    C(N)  = s (natCode N)    [range bound -- consumes  mapsBelow ] ;
-- give, by induction on  t ,  C(t) <= t ; at  t = N  this reads
-- s (natCode N) <= natCode N , i.e.  leq (s N) N , a contradiction
-- (notLeqSucSelf), exactly the  mono_php  finish.
--
-- This file does the count by META-recursion on the numeral bound  N
-- (mirroring  mono_php / dom , and per the project rule that numeral
-- meta-induction is the clean form here; the object var-bound  Fun1
-- recursor is the (P2) upgrade).  Sigma_1-FREE: no  thmT , no provability.

------------------------------------------------------------------------
-- The strict-less-than indicator.
--
--   indLt a b  =  sub (s O) (sub (s a) b)        in {0, 1} :
--     a <  b  ==>  sub (s a) b = 0  ==>  indLt a b = sub (s O) O = 1 ;
--     a >= b  ==>  sub (s a) b >= 1 ==>  indLt a b = sub (s O) (>=1) = 0 .

indLt : Term -> Term -> Term
indLt a b = ap2 sub (ap1 s O) (ap2 sub (ap1 s a) b)

-- indLt a O = O   (nothing is  < 0 ).  Universal in  a .
--   sub (s a) O = s a            [T_sub_O]
--   sub (s O) (s a) = sub O a    [T57sub at v0:=O, v1:=a]
--   sub O a = O                  [T76 at a]

indLt_at_O : (a : Term) -> Deriv (eqF (indLt a O) O)
indLt_at_O a =
  let e1 : Deriv (eqF (indLt a O) (ap2 sub (ap1 s O) (ap1 s a)))
      e1 = congR sub (ap1 s O) (T_sub_O (ap1 s a))

      e2 : Deriv (eqF (ap2 sub (ap1 s O) (ap1 s a)) (ap2 sub O a))
      e2 = ruleInst2 0 O 1 a refl T57sub

      e3 : Deriv (eqF (ap2 sub O a) O)
      e3 = ruleInst 0 a T76
  in ruleTrans e1 (ruleTrans e2 e3)

-- indLt a b = 1  when  a < b  (i.e.  leq (s a) b ).
--   leq (s a) b  =  (sub (s a) b = O)
--   indLt a b = sub (s O) (sub (s a) b) = sub (s O) O = s O   [T_sub_O].

indLt_at_lt :
  (a b : Term) -> Deriv (leq (ap1 s a) b) -> Deriv (eqF (indLt a b) (ap1 s O))
indLt_at_lt a b lt =
  ruleTrans (congR sub (ap1 s O) lt) (T_sub_O (ap1 s O))

------------------------------------------------------------------------
-- The count  C(t) = sum_{j=0}^{N} [ idx j < t ] , by meta-recursion on  N .

Csum : Fun1 -> Nat -> Term -> Term
Csum idx zero    t = indLt (ap1 idx (natCode zero)) t
Csum idx (suc N) t =
  ap2 sigma (Csum idx N t) (indLt (ap1 idx (natCode (suc N))) t)

------------------------------------------------------------------------
-- C(0) = 0 :  every summand is 0 , and a sum of zeros is 0 .

C0 : (idx : Fun1) (N : Nat) -> Deriv (eqF (Csum idx N O) O)
C0 idx zero    = indLt_at_O (ap1 idx (natCode zero))
C0 idx (suc N) =
  let ih : Deriv (eqF (Csum idx N O) O)
      ih = C0 idx N

      tailZ : Deriv (eqF (indLt (ap1 idx (natCode (suc N))) O) O)
      tailZ = indLt_at_O (ap1 idx (natCode (suc N)))

      e1 : Deriv (eqF (ap2 sigma (Csum idx N O) (indLt (ap1 idx (natCode (suc N))) O))
                       (ap2 sigma O (indLt (ap1 idx (natCode (suc N))) O)))
      e1 = congL sigma (indLt (ap1 idx (natCode (suc N))) O) ih

      e2 : Deriv (eqF (ap2 sigma O (indLt (ap1 idx (natCode (suc N))) O))
                       (ap2 sigma O O))
      e2 = congR sigma O tailZ

      e3 : Deriv (eqF (ap2 sigma O O) O)
      e3 = T33 O
  in ruleTrans e1 (ruleTrans e2 e3)

------------------------------------------------------------------------
-- mapsBelow  (the range bound, as a meta-family of object facts):
--   for every  j <= N ,  idx j < N , i.e.  leq (s (idx j)) (natCode N) .

MapsBelow : Fun1 -> Nat -> Set
MapsBelow idx N =
  (j : Nat) -> NatLe j N ->
  Deriv (leq (ap1 s (ap1 idx (natCode j))) (natCode N))

-- Meta helper:  addN m 1 = suc m .

addN_one : (m : Nat) -> Eq (addN m (suc zero)) (suc m)
addN_one zero    = refl
addN_one (suc m) = eqCong suc (addN_one m)

-- NatLe predecessor on the left.

le-pred-right : {m n : Nat} -> NatLe (suc m) n -> NatLe m n
le-pred-right (le-suc l) = le-suc-right l

------------------------------------------------------------------------
-- C(N) = N + 1 :  under  mapsBelow  every  idx j  (j <= N) is  < N , so
-- every summand is 1 , and  sum_{j=0}^{M} 1 = natCode (suc M) .
--
-- Proved for the partial sums  Csum idx M (natCode N)  with  M <= N
-- (so  mapsBelow  applies at each index  j = M ), by induction on  M .

CrangePartial :
  (idx : Fun1) (N : Nat) -> MapsBelow idx N ->
  (M : Nat) -> NatLe M N ->
  Deriv (eqF (Csum idx M (natCode N)) (natCode (suc M)))
CrangePartial idx N mb zero leMN =
  -- Csum idx 0 (natCode N) = indLt (idx 0) (natCode N) = s O = natCode 1.
  indLt_at_lt (ap1 idx (natCode zero)) (natCode N) (mb zero leMN)
CrangePartial idx N mb (suc M) leMN =
  let ih : Deriv (eqF (Csum idx M (natCode N)) (natCode (suc M)))
      ih = CrangePartial idx N mb M (le-pred-right leMN)

      tail1 : Deriv (eqF (indLt (ap1 idx (natCode (suc M))) (natCode N)) (ap1 s O))
      tail1 = indLt_at_lt (ap1 idx (natCode (suc M))) (natCode N) (mb (suc M) leMN)

      e1 : Deriv (eqF (ap2 sigma (Csum idx M (natCode N))
                                  (indLt (ap1 idx (natCode (suc M))) (natCode N)))
                       (ap2 sigma (natCode (suc M))
                                  (indLt (ap1 idx (natCode (suc M))) (natCode N))))
      e1 = congL sigma (indLt (ap1 idx (natCode (suc M))) (natCode N)) ih

      e2 : Deriv (eqF (ap2 sigma (natCode (suc M))
                                  (indLt (ap1 idx (natCode (suc M))) (natCode N)))
                       (ap2 sigma (natCode (suc M)) (ap1 s O)))
      e2 = congR sigma (natCode (suc M)) tail1

      e3 : Deriv (eqF (ap2 sigma (natCode (suc M)) (natCode (suc zero)))
                       (natCode (addN (suc M) (suc zero))))
      e3 = sigma_natCode (suc M) (suc zero)

      e4 : Deriv (eqF (natCode (addN (suc M) (suc zero))) (natCode (suc (suc M))))
      e4 = numEq (addN (suc M) (suc zero)) (suc (suc M)) (addN_one (suc M))
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))

Crange :
  (idx : Fun1) (N : Nat) -> MapsBelow idx N ->
  Deriv (eqF (Csum idx N (natCode N)) (natCode (suc N)))
Crange idx N mb = CrangePartial idx N mb N (le-refl N)

------------------------------------------------------------------------
-- Two leq-rewriting helpers, via the substitutivity axiom  ax_eqCongL
-- (takes explicit Term args, so no  ruleInst  capture issues).
--   leq a c  ==  eqF (sub a c) O .

-- from  a = b  and  b <= c  derive  a <= c .
leq_eqL : (a b c : Term) -> Deriv (eqF a b) -> Deriv (leq b c) -> Deriv (leq a c)
leq_eqL a b c ab bc =
  ruleTrans (mp (ax_eqCongL sub a b c) ab) bc

-- from  a = b  and  a <= c  derive  b <= c .
leq_substL : (a b c : Term) -> Deriv (eqF a b) -> Deriv (leq a c) -> Deriv (leq b c)
leq_substL a b c ab ac =
  ruleTrans (ruleSym (mp (ax_eqCongL sub a b c) ab)) ac

------------------------------------------------------------------------
------------------------------------------------------------------------
-- CLASSICAL BY-CASES, via reductio through  falseF .
--
-- The naive "by cases" combinator reduces to consequentia mirabilis
-- (neg C -> C) -> C , which needs the raw Lukasiewicz derivation.  But
-- BRA has the Peano axiom  ax_succ_nonzero : neg (s O = O) , hence
-- neg falseF  (falseF = (O = s O)) by symmetry, so we can do reductio
-- THROUGH falseF (the ndw2.pdf / Carneiro deduction-theorem reductio):
--   negIntro :  P -> Q  and  P -> neg Q  give  neg P
-- (under P derive both Q and neg Q, hence falseF, hence neg P via the
-- contrapositive of  neg falseF ), and  byCases  follows with  DNE .
-- No raw consequentia mirabilis required.

-- neg falseF :  O = s O  is false (symmetry of  ax_succ_nonzero ).

negFalseF : Deriv (neg falseF)
negFalseF =
  mp (mp (axContrapos (eqF O (ap1 s O)) (eqF (ap1 s O) O))
         (eqSymImp O (ap1 s O)))
     ax_succ_nonzero

-- from  X -> falseF  derive  neg X  (contrapositive against  neg falseF ).

impFalseToNeg : (X : Formula) -> Deriv (imp X falseF) -> Deriv (neg X)
impFalseToNeg X xf =
  mp (mp (axContrapos X falseF) xf) negFalseF

-- negation introduction:  (P -> Q) -> (P -> neg Q) -> neg P .

negIntro :
  (P Q : Formula) ->
  Deriv (imp P Q) -> Deriv (imp P (neg Q)) -> Deriv (neg P)
negIntro P Q h1 h2 =
  let pf : Deriv (imp P falseF)
      pf = bComb (bComb (liftP P (axExFalso Q falseF)) h1) h2
  in impFalseToNeg P pf

-- by-cases:  (A -> C) -> (neg A -> C) -> C .

byCases :
  (A Goal : Formula) ->
  Deriv (imp A Goal) -> Deriv (imp (neg A) Goal) -> Deriv Goal
byCases A Goal h1 h2 =
  let e1 : Deriv (imp (neg Goal) (neg A))
      e1 = mp (axContrapos A Goal) h1

      e2 : Deriv (imp (neg Goal) (neg (neg A)))
      e2 = mp (axContrapos (neg A) Goal) h2

      nng : Deriv (neg (neg Goal))
      nng = negIntro (neg Goal) (neg A) e1 e2
  in mp (DNE Goal) nng

------------------------------------------------------------------------
-- The unit step, as a meta-family (provided by  unit_step  below from
-- INJECTIVITY -- this is where Con-injectivity enters in the application):
--
--   C(t+1) <= s (C t)     at  t = natCode k  for every  k <= N .

UnitStep : Fun1 -> Nat -> Set
UnitStep idx N =
  (k : Nat) -> NatLe k N ->
  Deriv (leq (Csum idx N (ap1 s (natCode k))) (ap1 s (Csum idx N (natCode k))))

------------------------------------------------------------------------
-- C(t) <= t  by induction on  t = natCode k  (k <= N) :
--   base   C(0) = 0 <= 0 ;
--   step   C(k+1) <= s (C k)        [unit step]
--               <= s k              [succ_mono on IH] .

Cbound :
  (idx : Fun1) (N : Nat) -> UnitStep idx N ->
  (k : Nat) -> NatLe k N ->
  Deriv (leq (Csum idx N (natCode k)) (natCode k))
Cbound idx N us zero leKN =
  leq_eqL (Csum idx N O) O O (C0 idx N) (ruleInst 0 O T73)
Cbound idx N us (suc k) leKN =
  let ih : Deriv (leq (Csum idx N (natCode k)) (natCode k))
      ih = Cbound idx N us k (le-pred-right leKN)

      sm : Deriv (leq (ap1 s (Csum idx N (natCode k))) (ap1 s (natCode k)))
      sm = succ_mono (Csum idx N (natCode k)) (natCode k) ih

      ust : Deriv (leq (Csum idx N (ap1 s (natCode k)))
                        (ap1 s (Csum idx N (natCode k))))
      ust = us k (le-pred-right leKN)
  in leq_trans (Csum idx N (ap1 s (natCode k)))
               (ap1 s (Csum idx N (natCode k)))
               (ap1 s (natCode k))
               ust sm

------------------------------------------------------------------------
-- The pigeonhole, modulo the unit step:  at  t = N ,  C(N) <= N  but
-- C(N) = N + 1 , so  s (natCode N) <= natCode N , contradiction.

php_via_unit_step :
  (idx : Fun1) (N : Nat) ->
  MapsBelow idx N -> UnitStep idx N ->
  Deriv falseF
php_via_unit_step idx N mb us =
  let cb : Deriv (leq (Csum idx N (natCode N)) (natCode N))
      cb = Cbound idx N us N (le-refl N)

      cr : Deriv (eqF (Csum idx N (natCode N)) (natCode (suc N)))
      cr = Crange idx N mb

      -- natCode (suc N) = s (natCode N) , so this is  leq (s N) N .
      bridge : Deriv (leq (natCode (suc N)) (natCode N))
      bridge = leq_substL (Csum idx N (natCode N)) (natCode (suc N)) (natCode N) cr cb

      irr : Deriv (neg (leq (ap1 s (natCode N)) (natCode N)))
      irr = ruleInst 0 (natCode N) notLeqSucSelf

      exF : Deriv (imp (leq (ap1 s (natCode N)) (natCode N))
                       (imp (neg (leq (ap1 s (natCode N)) (natCode N))) falseF))
      exF = axExFalso (leq (ap1 s (natCode N)) (natCode N)) falseF
  in mp (mp exF bridge) irr

------------------------------------------------------------------------
------------------------------------------------------------------------
-- STATUS (Gate-1 step 1).
--
-- DONE + typechecked above: the FULL combinatorial skeleton of the
-- arbitrary-injection pigeonhole + the CLASSICAL by-cases combinator.
-- `php_via_unit_step` derives  falseF  from  MapsBelow  (range bound) and
-- UnitStep  (the count grows by <= 1).  So the entire route R3 is reduced
-- to ONE lemma:
--
--   unit_step : InjBelow idx N -> UnitStep idx N
--
-- i.e.  leq (Csum idx N (s t)) (s (Csum idx N t))  for  t = natCode k ,
-- the place where Con-INJECTIVITY is consumed.
--
-- CONCEPTUAL BLOCKER RESOLVED: the object-level case analysis on
-- "idx(s M') = t" needs a classical by-cases combinator, which naively
-- reduces to consequentia mirabilis  (neg C -> C) -> C  (NOT in corpus,
-- every shortcut loops).  But  ax_succ_nonzero : neg (s O = O)  gives
-- neg falseF , so we do reductio THROUGH falseF (ndw2.pdf / Carneiro
-- deduction-theorem reductio): see  negFalseF / impFalseToNeg / negIntro /
-- byCases  above -- all typecheck.  NO raw consequentia mirabilis needed.
--
-- REMAINING (mechanical arithmetic, ~250-300 LoC; NEXT-SESSION-PHP-UNITSTEP.md):
--   (1) eqInd a t (equality indicator) + eqInd_le_one, eqInd_at_neq
--       (neg (eqF a t) -> eqInd a t = O), and the Df.2 termwise split
--       indLt a (s t) = sigma (indLt a t) (eqInd a t).  Needs a few corpus
--       arithmetic lemmas to build (indicator monotone in upper arg via
--       T88; reassembly  y<=x -> sigma y (sub x y) = x ; antisymmetry-ish
--       for eqInd_at_neq) -- none present, build from T68/T82/T87/T88.
--   (2) EqSum idx N t = sum_{j<=N} eqInd(idx j, t) ;
--       Csum_succ_split : Csum N (s t) = sigma (Csum N t) (EqSum N t) ;
--       EqSum_le_one : InjBelow -> EqSum N t <= 1  by induction with
--       byCases on  eqF (idx(s M')) t ; the "hit" branch uses
--       prefix_no_hit (injectivity + negIntro give  idx i /= t  for i<=M',
--       so EqSum prefix = O).
--   (3) assemble  unit_step  + the final
--       no_injection_into_smaller = php_via_unit_step ... (unit_step ...).
