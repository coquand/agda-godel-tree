{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.MetaPigeonhole -- the META pigeonhole utility used by
-- the surprise-G2 stage_r recursion's base case.
--
-- Statement (pure Nat-only combinatorics):
--
--   Given  ix : Nat -> Nat  with the bound
--          (i : Nat) -> Lt i (suc N) -> Lt (ix i) (suc M)
--   ("ix maps the N+1 indices [0..N] into the M+1 values [0..M]")
--   and  Lt M N  ("N+1 > M+1, i.e., strictly more pigeons than holes"),
--   produce  Collide ix N  : a pair  (i_idx, j_idx)  with
--   i_idx /= j_idx ,  both  <= N , and  ix i_idx = ix j_idx .
--
-- Proof : induction on  N .
--   * N = 0    : Lt M 0 is uninhabited.   Absurd.
--   * N = suc N' :
--       Look at  vTgt := ix (suc N') . Search for a duplicate of  vTgt  among
--       indices [0..N'] :
--         - If  i  found with  ix i = vTgt  and  i <= N' : collision  (i, suc N') .
--         - Otherwise (no  i  <= N'  has  ix i = vTgt ) :
--           "renumber" the codomain to skip  vTgt :  ix' i = if ix i < vTgt
--           then ix i else pred (ix i) .  Then  ix' : [0..N'] -> [0..M-1] .
--           Apply IH at  (ix', N', pred M)  to get a collision in  ix' ,
--           translate back via the renumbering-is-injective lemma.
--           ( M = 0  in this branch is impossible: all values are then  0 ,
--             so  vTgt = 0 = ix 0  and  0 <= N' , contradicting "no  i  <= N'
--             has  ix i = vTgt ".)
--
-- The whole proof is self-contained meta-arithmetic, with no BRA-internal
-- machinery.  The only outside import is  T4.Base  for  Nat / Eq /
-- emptyElim , plus  T4.SurpriseG2.NumNeq  for the  Not  alias.

module T4.SurpriseG2.MetaPigeonhole where

open import T4.Base
open import T4.SurpriseG2.NumNeq using ( Not )

------------------------------------------------------------------------
-- SECTION 1.  Lt -- local definition (same shape as T4.EvalUMu.Lt,
-- avoided here to keep this module standalone).

data Lt : Nat -> Nat -> Set where
  ltZ : (n : Nat) -> Lt zero (suc n)
  ltS : (m n : Nat) -> Lt m n -> Lt (suc m) (suc n)

ltAbsurd : {A : Set} {n : Nat} -> Lt n zero -> A
ltAbsurd ()

-- Lt n m  ->  Lt n (suc m)  ("weaken").
ltWeaken : {n m : Nat} -> Lt n m -> Lt n (suc m)
ltWeaken (ltZ m)     = ltZ (suc m)
ltWeaken (ltS i j h) = ltS i (suc j) (ltWeaken h)

-- Lt n (suc n)  ("strict-less-than-successor").
ltSelf : (n : Nat) -> Lt n (suc n)
ltSelf zero    = ltZ zero
ltSelf (suc n) = ltS n (suc n) (ltSelf n)

-- "predecessor of an Lt":  Lt (suc i) (suc j) -> Lt i j .
ltPred : {i j : Nat} -> Lt (suc i) (suc j) -> Lt i j
ltPred (ltS _ _ h) = h

-- Ordinary  Lt  transitivity.
ltTrans : {a b c : Nat} -> Lt a b -> Lt b c -> Lt a c
ltTrans (ltZ _)        (ltS _ c' _)  = ltZ c'
ltTrans (ltS a' b' h1) (ltS _ c' h2) = ltS a' c' (ltTrans h1 h2)

-- Lt a (suc b)  ->  Or (Lt a b) (Eq a b) .
data Or (P Q : Set) : Set where
  inl : P -> Or P Q
  inr : Q -> Or P Q

ltSucCasesStep :
  {a b : Nat} -> Or (Lt a b) (Eq a b) ->
  Or (Lt (suc a) (suc b)) (Eq (suc a) (suc b))
ltSucCasesStep {a} {b} (inl hab) = inl (ltS a b hab)
ltSucCasesStep {a} {b} (inr eq)  = inr (eqCong suc eq)

ltSucCases : {a b : Nat} -> Lt a (suc b) -> Or (Lt a b) (Eq a b)
ltSucCases {zero}  {zero}  (ltZ _)     = inr refl
ltSucCases {zero}  {suc b} (ltZ _)     = inl (ltZ b)
ltSucCases {suc a} {zero}  (ltS _ _ h) = ltAbsurd h
ltSucCases {suc a} {suc b} (ltS _ _ h) = ltSucCasesStep (ltSucCases h)

-- "Strict" transitivity bridge :  Lt x vTgt -> Lt vTgt (suc M) -> Lt x M .
ltStrictTransStep :
  {x vTgt M : Nat} -> Lt x vTgt -> Or (Lt vTgt M) (Eq vTgt M) -> Lt x M
ltStrictTransStep lxv (inl ltvM) = ltTrans lxv ltvM
ltStrictTransStep lxv (inr eqvM) = eqSubst (\ z -> Lt _ z) eqvM lxv

ltStrictTrans : {x vTgt M : Nat} -> Lt x vTgt -> Lt vTgt (suc M) -> Lt x M
ltStrictTrans lxv lvM = ltStrictTransStep lxv (ltSucCases lvM)

-- Lt n (suc zero)  ->  Eq n zero .
ltOneZero : {n : Nat} -> Lt n (suc zero) -> Eq n zero
ltOneZero {zero}  (ltZ _)     = refl
ltOneZero {suc n} (ltS _ _ h) = ltAbsurd h

------------------------------------------------------------------------
-- SECTION 2.  Decidable Nat equality.

data NatDec (a b : Nat) : Set where
  natYes : Eq a b -> NatDec a b
  natNo  : Not (Eq a b) -> NatDec a b

sucInj : {n m : Nat} -> Eq (suc n) (suc m) -> Eq n m
sucInj refl = refl

zeroNotSuc : (n : Nat) -> Not (Eq zero (suc n))
zeroNotSuc n ()

sucNotZero : (n : Nat) -> Not (Eq (suc n) zero)
sucNotZero n ()

natDecEqStep : {n m : Nat} -> NatDec n m -> NatDec (suc n) (suc m)
natDecEqStep (natYes eq) = natYes (eqCong suc eq)
natDecEqStep (natNo  ne) = natNo  (\ q -> ne (sucInj q))

natDecEq : (a b : Nat) -> NatDec a b
natDecEq zero    zero    = natYes refl
natDecEq zero    (suc m) = natNo (zeroNotSuc m)
natDecEq (suc n) zero    = natNo (sucNotZero n)
natDecEq (suc n) (suc m) = natDecEqStep (natDecEq n m)

------------------------------------------------------------------------
-- SECTION 3.  3-way Nat comparison.

data NatCmp (a b : Nat) : Set where
  ltC : Lt a b -> NatCmp a b
  eqC : Eq a b -> NatCmp a b
  gtC : Lt b a -> NatCmp a b

natCmpStep : {n m : Nat} -> NatCmp n m -> NatCmp (suc n) (suc m)
natCmpStep {n} {m} (ltC h)  = ltC (ltS n m h)
natCmpStep {n} {m} (eqC eq) = eqC (eqCong suc eq)
natCmpStep {n} {m} (gtC h)  = gtC (ltS m n h)

natCmp : (a b : Nat) -> NatCmp a b
natCmp zero    zero    = eqC refl
natCmp zero    (suc m) = ltC (ltZ m)
natCmp (suc n) zero    = gtC (ltZ n)
natCmp (suc n) (suc m) = natCmpStep (natCmp n m)

------------------------------------------------------------------------
-- SECTION 4.  Search for a duplicate of  vTgt  in  ix [0..k) .

data Search (ix : Nat -> Nat) (vTgt : Nat) (k : Nat) : Set where
  found    : (i : Nat) -> Lt i k -> Eq (ix i) vTgt -> Search ix vTgt k
  notFound : ((i : Nat) -> Lt i k -> Not (Eq (ix i) vTgt)) -> Search ix vTgt k

emptyAtLtZ : (i : Nat) -> Lt i zero -> {A : Set} -> A
emptyAtLtZ i ()

searchDup :
  (ix : Nat -> Nat) (vTgt k : Nat) -> Search ix vTgt k
searchDup ix vTgt zero    = notFound (\ i lt -> emptyAtLtZ i lt)
searchDup ix vTgt (suc k) = searchDupStep ix vTgt k (searchDup ix vTgt k) (natDecEq (ix k) vTgt)
  where
    searchDupStep :
      (ix : Nat -> Nat) (vTgt k : Nat) ->
      Search ix vTgt k ->
      NatDec (ix k) vTgt ->
      Search ix vTgt (suc k)
    searchDupStep ix vTgt k (found i Lti eq) _              = found i (ltWeaken Lti) eq
    searchDupStep ix vTgt k (notFound _)     (natYes eq)    = found k (ltSelf k) eq
    searchDupStep ix vTgt k (notFound np)    (natNo  ne)    = notFound newNp
      where
        newNp : (i : Nat) -> Lt i (suc k) -> Not (Eq (ix i) vTgt)
        newNp i Lti = newNpCase (ltSucCases Lti)
          where
            newNpCase : Or (Lt i k) (Eq i k) -> Not (Eq (ix i) vTgt)
            newNpCase (inl LtIk) = np i LtIk
            newNpCase (inr eqIk) =
              \ eqIxV -> ne (eqSubst (\ z -> Eq (ix z) vTgt) eqIk eqIxV)

------------------------------------------------------------------------
-- SECTION 5.  The renumbering function and its properties.

pred1 : Nat -> Nat
pred1 zero    = zero
pred1 (suc n) = n

renumStep : (vTgt x : Nat) -> NatCmp x vTgt -> Nat
renumStep vTgt x (ltC _) = x
renumStep vTgt x (eqC _) = x        -- never invoked when  x /= vTgt ; arbitrary.
renumStep vTgt x (gtC _) = pred1 x

renum : Nat -> Nat -> Nat
renum vTgt x = renumStep vTgt x (natCmp x vTgt)

-- The renumbered value is bounded by  M  given  x , vTgt  both  <= M  and  x /= vTgt .
--
-- The signature uses  M = suc m  explicitly so the bound is concrete
-- ( Lt (renum vTgt x) (suc m) ).

-- The  gtC  sub-case ( renumStep ... (gtC _) = pred1 x ), split on  x  explicitly.
renumBoundGt :
  (vTgt x m : Nat) ->
  Lt x (suc (suc m)) -> Lt vTgt x ->
  Lt (pred1 x) (suc m)
renumBoundGt vTgt zero    m ltxM ltvx = ltAbsurd ltvx        -- vTgt < 0 impossible.
renumBoundGt vTgt (suc x') m ltxM ltvx = ltPred ltxM          -- pred1 (suc x') = x' .

renumBoundAux :
  (vTgt x m : Nat) ->
  Lt x (suc (suc m)) ->
  Lt vTgt (suc (suc m)) ->
  Not (Eq x vTgt) ->
  (c : NatCmp x vTgt) ->
  Lt (renumStep vTgt x c) (suc m)
renumBoundAux vTgt x m ltxM ltvM ne (ltC ltxv) = ltStrictTrans ltxv ltvM
renumBoundAux vTgt x m ltxM ltvM ne (eqC eq)   = emptyElim (ne eq)
renumBoundAux vTgt x m ltxM ltvM ne (gtC ltvx) = renumBoundGt vTgt x m ltxM ltvx

renumBound :
  (vTgt x m : Nat) ->
  Lt x (suc (suc m)) ->
  Lt vTgt (suc (suc m)) ->
  Not (Eq x vTgt) ->
  Lt (renum vTgt x) (suc m)
renumBound vTgt x m ltxM ltvM ne = renumBoundAux vTgt x m ltxM ltvM ne (natCmp x vTgt)

-- The renumbering is injective on values  /= vTgt .

-- Useful local lemma: Lt n n is impossible.
ltIrrefl : {n : Nat} -> Lt n n -> Empty
ltIrrefl (ltS _ _ h) = ltIrrefl h

-- "ltOfLe": Lt vTgt (suc a) and Lt a vTgt gives Empty (the asymmetry of strict order).
ltAsym : {vTgt a : Nat} -> Lt vTgt (suc a) -> Lt a vTgt -> Empty
ltAsym h1 h2 = ltIrreflAux (ltSucCases h1)
  where
    ltIrreflAux : Or (Lt _ _) (Eq _ _) -> Empty
    ltIrreflAux (inl ltVA) = ltIrrefl (ltTrans h2 ltVA)
    ltIrreflAux (inr eqVA) = ltIrrefl (eqSubst (\ z -> Lt _ z) eqVA h2)

-- Clash helper : a value  below  vTgt cannot equal the renumbering of one  above .
clashLtGt :
  (vTgt a b : Nat) -> Lt a vTgt -> Lt vTgt b -> Eq a (pred1 b) -> Empty
clashLtGt vTgt a zero     lav lvb eqa = ltAbsurd lvb
clashLtGt vTgt a (suc b') lav lvb eqa =
  -- eqa : Eq a b' . lvb : Lt vTgt (suc b') so Lt vTgt (suc a) via eqa.
  ltAsym (eqSubst (\ z -> Lt vTgt (suc z)) (eqSym eqa) lvb) lav

clashGtLt :
  (vTgt a b : Nat) -> Lt vTgt a -> Lt b vTgt -> Eq (pred1 a) b -> Empty
clashGtLt vTgt zero     b lva lbv eqa = ltAbsurd lva
clashGtLt vTgt (suc a') b lva lbv eqa =
  -- eqa : Eq a' b . lva : Lt vTgt (suc a') so Lt vTgt (suc b) via eqa.
  ltAsym (eqSubst (\ z -> Lt vTgt (suc z)) eqa lva) lbv

-- Both values above  vTgt : equal predecessors give equal originals.
predEqG :
  (vTgt a b : Nat) -> Lt vTgt a -> Lt vTgt b -> Eq (pred1 a) (pred1 b) -> Eq a b
predEqG vTgt zero     b        lva lvb eqp = ltAbsurd lva
predEqG vTgt (suc a') zero     lva lvb eqp = ltAbsurd lvb
predEqG vTgt (suc a') (suc b') lva lvb eqp = eqCong suc eqp

-- Injectivity, driven by the two comparison results passed explicitly
-- ( the  with -free replacement for the original nested  with natCmp ... ;
--   stated on  renumStep  so matching  ca / cb  performs the reductions ).
renumInjAux :
  (vTgt a b : Nat) ->
  (ca : NatCmp a vTgt) -> (cb : NatCmp b vTgt) ->
  Not (Eq a vTgt) -> Not (Eq b vTgt) ->
  Eq (renumStep vTgt a ca) (renumStep vTgt b cb) ->
  Eq a b
renumInjAux vTgt a b (eqC ea)  cb        nea neb eq = emptyElim (nea ea)
renumInjAux vTgt a b (ltC _ )  (eqC eb)  nea neb eq = emptyElim (neb eb)
renumInjAux vTgt a b (gtC _ )  (eqC eb)  nea neb eq = emptyElim (neb eb)
renumInjAux vTgt a b (ltC lav) (ltC lbv) nea neb eq = eq
renumInjAux vTgt a b (ltC lav) (gtC lvb) nea neb eq = emptyElim (clashLtGt vTgt a b lav lvb eq)
renumInjAux vTgt a b (gtC lva) (ltC lbv) nea neb eq = emptyElim (clashGtLt vTgt a b lva lbv eq)
renumInjAux vTgt a b (gtC lva) (gtC lvb) nea neb eq = predEqG vTgt a b lva lvb eq

renumInj :
  (vTgt a b : Nat) ->
  Not (Eq a vTgt) -> Not (Eq b vTgt) ->
  Eq (renum vTgt a) (renum vTgt b) ->
  Eq a b
renumInj vTgt a b nea neb eq =
  renumInjAux vTgt a b (natCmp a vTgt) (natCmp b vTgt) nea neb eq

------------------------------------------------------------------------
-- SECTION 6.  The Collide record and the pigeonhole theorem.

record Collide (ix : Nat -> Nat) (N : Nat) : Set where
  constructor mkCollide
  field
    i_idx : Nat
    j_idx : Nat
    i_lt  : Lt i_idx (suc N)
    j_lt  : Lt j_idx (suc N)
    i_neq : Not (Eq i_idx j_idx)
    ix_eq : Eq (ix i_idx) (ix j_idx)

-- The pigeonhole theorem.

pigeonhole :
  (ix : Nat -> Nat) (N M : Nat) ->
  ((i : Nat) -> Lt i (suc N) -> Lt (ix i) (suc M)) ->
  Lt M N ->
  Collide ix N

-- The  notFound  branch : no duplicate of  vTgt = ix (suc N')  among [0..N') .
-- Split on  M  explicitly (the old nested  with M ).
pigeonholeNF :
  (ix : Nat -> Nat) (N' M : Nat) ->
  ((i : Nat) -> Lt i (suc (suc N')) -> Lt (ix i) (suc M)) ->
  Lt M (suc N') ->
  ((i : Nat) -> Lt i (suc N') -> Not (Eq (ix i) (ix (suc N')))) ->
  Collide ix (suc N')
pigeonholeNF ix N' zero bd ltMN np =
    -- All ix values are 0 (since they're < 1).  ix 0 = 0 = vTgt = ix (suc N').
    let ixZ_eq_Z : Eq (ix zero) zero
        ixZ_eq_Z = ltOneZero (bd zero (ltZ (suc N')))

        vTop_eq_Z : Eq (ix (suc N')) zero
        vTop_eq_Z = ltOneZero (bd (suc N') (ltSelf (suc N')))

        ixZ_eq_v : Eq (ix zero) (ix (suc N'))
        ixZ_eq_v = eqTrans ixZ_eq_Z (eqSym vTop_eq_Z)

        LtZ_SN : Lt zero (suc N')
        LtZ_SN = ltZ N'
    in  emptyElim (np zero LtZ_SN ixZ_eq_v)
pigeonholeNF ix N' (suc m) bd ltMN np =
    let vTgt : Nat
        vTgt = ix (suc N')

        ix' : Nat -> Nat
        ix' i = renum vTgt (ix i)

        -- Bound for IH .   bd : (i)(Lt i (suc (suc N'))) -> Lt (ix i) (suc (suc m)) .
        -- We restrict to i in [0..suc N') and apply renumBound.
        ltvM : Lt vTgt (suc (suc m))
        ltvM = bd (suc N') (ltSelf (suc N'))

        bd' : (i : Nat) -> Lt i (suc N') -> Lt (ix' i) (suc m)
        bd' i Lti =
          renumBound vTgt (ix i) m
            (bd i (ltWeaken Lti))
            ltvM
            (np i Lti)

        -- Lt m N' (from ltMN : Lt (suc m) (suc N') = strip suc).
        ltmN' : Lt m N'
        ltmN' = ltPred ltMN

        coll' : Collide ix' N'
        coll' = pigeonhole ix' N' m bd' ltmN'

        i'  = Collide.i_idx coll'
        j'  = Collide.j_idx coll'
        Lti' : Lt i' (suc N')
        Lti' = Collide.i_lt coll'
        Ltj' : Lt j' (suc N')
        Ltj' = Collide.j_lt coll'
        neI'J' : Not (Eq i' j')
        neI'J' = Collide.i_neq coll'
        ix'EQ : Eq (ix' i') (ix' j')
        ix'EQ = Collide.ix_eq coll'

        -- Translate back: ix i' /= vTgt and ix j' /= vTgt from np .
        neIxI'V : Not (Eq (ix i') vTgt)
        neIxI'V = np i' Lti'

        neIxJ'V : Not (Eq (ix j') vTgt)
        neIxJ'V = np j' Ltj'

        ixEQ : Eq (ix i') (ix j')
        ixEQ = renumInj vTgt (ix i') (ix j') neIxI'V neIxJ'V ix'EQ

    in mkCollide i' j' (ltWeaken Lti') (ltWeaken Ltj') neI'J' ixEQ

-- Dispatch on the duplicate search (the old  with searchDup ... ).
pigeonholeStep :
  (ix : Nat -> Nat) (N' M : Nat) ->
  ((i : Nat) -> Lt i (suc (suc N')) -> Lt (ix i) (suc M)) ->
  Lt M (suc N') ->
  Search ix (ix (suc N')) (suc N') ->
  Collide ix (suc N')
pigeonholeStep ix N' M bd ltMN (found i Lti eq_ix_i_v) =
    mkCollide i (suc N') (ltWeaken Lti) (ltSelf (suc N')) i_neq_top eq_ix_i_v
  where
    i_neq_top : Not (Eq i (suc N'))
    i_neq_top eq = ltIrrefl (eqSubst (\ z -> Lt z (suc N')) eq Lti)
pigeonholeStep ix N' M bd ltMN (notFound np) = pigeonholeNF ix N' M bd ltMN np

pigeonhole ix zero    M bd ltMN = ltAbsurd ltMN
pigeonhole ix (suc N') M bd ltMN =
  pigeonholeStep ix N' M bd ltMN (searchDup ix (ix (suc N')) (suc N'))
