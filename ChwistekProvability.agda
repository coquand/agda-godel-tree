{-# OPTIONS --without-K --exact-split #-}

module ChwistekProvability where

open import ChwistekSyntax
open import ChwistekDiagonal

------------------------------------------------------------------------
-- Local infrastructure
------------------------------------------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

and : Bool -> Bool -> Bool
and true  b = b
and false b = false

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

------------------------------------------------------------------------
-- Equality tests
------------------------------------------------------------------------

eqNat : Nat -> Nat -> Bool
eqNat zero    zero    = true
eqNat zero    (suc _) = false
eqNat (suc _) zero    = false
eqNat (suc n) (suc m) = eqNat n m

eqVar : Var -> Var -> Bool
eqVar vz     vz     = true
eqVar vz     (vs _) = false
eqVar (vs _) vz     = false
eqVar (vs x) (vs y) = eqVar x y

eqCVar : CVar -> CVar -> Bool
eqCVar cvz     cvz     = true
eqCVar cvz     (cvs _) = false
eqCVar (cvs _) cvz     = false
eqCVar (cvs x) (cvs y) = eqCVar x y

eqCode : Code -> Code -> Bool
eqCode (catom n)    (catom m)    = eqNat n m
eqCode (catom _)    (cnode _ _)  = false
eqCode (cnode _ _)  (catom _)    = false
eqCode (cnode a b)  (cnode c d)  = and (eqCode a c) (eqCode b d)

eqCExp : CExp -> CExp -> Bool
eqCExp (cvar x)   (cvar y)   = eqCVar x y
eqCExp (cvar _)   (clit _)   = false
eqCExp (cvar _)   (ccheck _) = false
eqCExp (cvar _)   (csub _ _) = false
eqCExp (clit _)   (cvar _)   = false
eqCExp (clit c)   (clit d)   = eqCode c d
eqCExp (clit _)   (ccheck _) = false
eqCExp (clit _)   (csub _ _) = false
eqCExp (ccheck _) (cvar _)   = false
eqCExp (ccheck _) (clit _)   = false
eqCExp (ccheck a) (ccheck b) = eqCExp a b
eqCExp (ccheck _) (csub _ _) = false
eqCExp (csub _ _) (cvar _)   = false
eqCExp (csub _ _) (clit _)   = false
eqCExp (csub _ _) (ccheck _) = false
eqCExp (csub a b) (csub c d) = and (eqCExp a c) (eqCExp b d)

eqTerm : Term -> Term -> Bool
eqTerm (tvar x)  (tvar y)  = eqVar x y
eqTerm (tvar _)  tzero     = false
eqTerm (tvar _)  (tsucc _) = false
eqTerm tzero     (tvar _)  = false
eqTerm tzero     tzero     = true
eqTerm tzero     (tsucc _) = false
eqTerm (tsucc _) (tvar _)  = false
eqTerm (tsucc _) tzero     = false
eqTerm (tsucc s) (tsucc t) = eqTerm s t

eqFormula : Formula -> Formula -> Bool
-- fbot
eqFormula fbot        fbot        = true
eqFormula fbot        (feq _ _)   = false
eqFormula fbot        (fimp _ _)  = false
eqFormula fbot        (fall _)    = false
eqFormula fbot        (fcode _)   = false
eqFormula fbot        (fceq _ _)  = false
eqFormula fbot        (fcAll _)   = false
-- feq
eqFormula (feq _ _)   fbot        = false
eqFormula (feq s t)   (feq u v)   = and (eqTerm s u) (eqTerm t v)
eqFormula (feq _ _)   (fimp _ _)  = false
eqFormula (feq _ _)   (fall _)    = false
eqFormula (feq _ _)   (fcode _)   = false
eqFormula (feq _ _)   (fceq _ _)  = false
eqFormula (feq _ _)   (fcAll _)   = false
-- fimp
eqFormula (fimp _ _)  fbot        = false
eqFormula (fimp _ _)  (feq _ _)   = false
eqFormula (fimp a b)  (fimp c d)  = and (eqFormula a c) (eqFormula b d)
eqFormula (fimp _ _)  (fall _)    = false
eqFormula (fimp _ _)  (fcode _)   = false
eqFormula (fimp _ _)  (fceq _ _)  = false
eqFormula (fimp _ _)  (fcAll _)   = false
-- fall
eqFormula (fall _)    fbot        = false
eqFormula (fall _)    (feq _ _)   = false
eqFormula (fall _)    (fimp _ _)  = false
eqFormula (fall a)    (fall b)    = eqFormula a b
eqFormula (fall _)    (fcode _)   = false
eqFormula (fall _)    (fceq _ _)  = false
eqFormula (fall _)    (fcAll _)   = false
-- fcode
eqFormula (fcode _)   fbot        = false
eqFormula (fcode _)   (feq _ _)   = false
eqFormula (fcode _)   (fimp _ _)  = false
eqFormula (fcode _)   (fall _)    = false
eqFormula (fcode c)   (fcode d)   = eqCode c d
eqFormula (fcode _)   (fceq _ _)  = false
eqFormula (fcode _)   (fcAll _)   = false
-- fceq
eqFormula (fceq _ _)  fbot        = false
eqFormula (fceq _ _)  (feq _ _)   = false
eqFormula (fceq _ _)  (fimp _ _)  = false
eqFormula (fceq _ _)  (fall _)    = false
eqFormula (fceq _ _)  (fcode _)   = false
eqFormula (fceq a b)  (fceq c d)  = and (eqCExp a c) (eqCExp b d)
eqFormula (fceq _ _)  (fcAll _)   = false
-- fcAll
eqFormula (fcAll _)   fbot        = false
eqFormula (fcAll _)   (feq _ _)   = false
eqFormula (fcAll _)   (fimp _ _)  = false
eqFormula (fcAll _)   (fall _)    = false
eqFormula (fcAll _)   (fcode _)   = false
eqFormula (fcAll _)   (fceq _ _)  = false
eqFormula (fcAll a)   (fcAll b)   = eqFormula a b

------------------------------------------------------------------------
-- Maybe helpers
------------------------------------------------------------------------

maybeBind : {A B : Set} -> Maybe A -> (A -> Maybe B) -> Maybe B
maybeBind nothing  f = nothing
maybeBind (just a) f = f a

maybeMap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
maybeMap f nothing  = nothing
maybeMap f (just a) = just (f a)

boolGuard : Bool -> Maybe Formula -> Maybe Formula
boolGuard true  r = r
boolGuard false r = nothing

guardEq : Formula -> Formula -> Maybe Formula -> Maybe Formula
guardEq a b result = boolGuard (eqFormula a b) result

------------------------------------------------------------------------
-- Decoding Code back to syntax
------------------------------------------------------------------------

decVar : Code -> Maybe Var
decVar (catom zero) = just vz
decVar (cnode (catom (suc zero)) c) = maybeMap vs (decVar c)
decVar _ = nothing

decCVar : Code -> Maybe CVar
decCVar (catom n) = h (eqNat n n14)
  where
  h : Bool -> Maybe CVar
  h true  = just cvz
  h false = nothing
decCVar (cnode (catom n) c) = h (eqNat n n15) c
  where
  h : Bool -> Code -> Maybe CVar
  h true c2 = maybeMap cvs (decCVar c2)
  h false _ = nothing
decCVar (cnode (cnode _ _) _) = nothing

decCExp : Code -> Maybe CExp
decCExp (cnode (catom n) rest) = h1 (eqNat n n16) n rest
  where
  h1 : Bool -> Nat -> Code -> Maybe CExp
  h1 true _ r = maybeMap cvar (decCVar r)
  h1 false m r = h2 (eqNat m n17) m r
    where
    h2 : Bool -> Nat -> Code -> Maybe CExp
    h2 true _ r2 = just (clit r2)
    h2 false m2 r2 = h3 (eqNat m2 n18) r2
      where
      h3 : Bool -> Code -> Maybe CExp
      h3 true r3 = maybeMap ccheck (decCExp r3)
      h3 false r3 = h4 (eqNat m2 n19) r3
        where
        h4 : Bool -> Code -> Maybe CExp
        h4 true (cnode e1 e2) =
          maybeBind (decCExp e1) (\ de1 ->
          maybeBind (decCExp e2) (\ de2 ->
          just (csub de1 de2)))
        h4 true (catom _) = nothing
        h4 false (catom _)  = nothing
        h4 false (cnode _ _) = nothing
decCExp (catom _) = nothing
decCExp (cnode (cnode _ _) _) = nothing

decTerm : Code -> Maybe Term
decTerm (catom (suc zero)) = just tzero
decTerm (cnode (catom zero) c) = maybeMap tvar (decVar c)
decTerm (cnode (catom (suc (suc zero))) c) = maybeMap tsucc (decTerm c)
decTerm _ = nothing

decFormula : Code -> Maybe Formula
decFormula (catom (suc (suc (suc zero)))) = just fbot
decFormula (cnode (catom (suc (suc (suc (suc zero))))) (cnode s t)) =
  maybeBind (decTerm s) (\ ds ->
  maybeBind (decTerm t) (\ dt ->
  just (feq ds dt)))
decFormula (cnode (catom (suc (suc (suc (suc (suc zero)))))) (cnode a b)) =
  maybeBind (decFormula a) (\ da ->
  maybeBind (decFormula b) (\ db ->
  just (fimp da db)))
decFormula (cnode (catom (suc (suc (suc (suc (suc (suc zero))))))) a) =
  maybeMap fall (decFormula a)
decFormula (cnode (catom (suc (suc (suc (suc (suc (suc (suc zero)))))))) c) =
  just (fcode c)
decFormula (cnode (catom n) rest) = hCeq (eqNat n n8) n rest
  where
  hCeq : Bool -> Nat -> Code -> Maybe Formula
  hCeq true _ (cnode e1 e2) =
    maybeBind (decCExp e1) (\ de1 ->
    maybeBind (decCExp e2) (\ de2 ->
    just (fceq de1 de2)))
  hCeq true _ (catom _) = nothing
  hCeq false m r = hCAll (eqNat m n9) r
    where
    hCAll : Bool -> Code -> Maybe Formula
    hCAll true r2 = maybeMap fcAll (decFormula r2)
    hCAll false (catom _) = nothing
    hCAll false (cnode _ _) = nothing
decFormula _ = nothing

------------------------------------------------------------------------
-- Proof checker
------------------------------------------------------------------------

n30 : Nat
n30 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc
       zero)))))))))))))))))))))))))))))

n31 : Nat
n31 = suc n30

n32 : Nat
n32 = suc n31

n33 : Nat
n33 = suc n32

n34 : Nat
n34 = suc n33

n35 : Nat
n35 = suc n34

-- Top-level helpers for checkProof (exposed for proof-level reasoning)

matchMP : Formula -> Formula -> Maybe Formula
matchMP (fimp a b) qf = guardEq a qf (just b)
matchMP fbot            _ = nothing
matchMP (feq _ _)       _ = nothing
matchMP (fall _)        _ = nothing
matchMP (fcode _)       _ = nothing
matchMP (fceq _ _)      _ = nothing
matchMP (fcAll _)       _ = nothing

checkProof : Code -> Maybe Formula

checkTag : Nat -> Code -> Maybe Formula
checkTag n tc = checkT30 (eqNat n n30) n tc
  where
  checkT30 : Bool -> Nat -> Code -> Maybe Formula
  checkT30 true _ tc =
    maybeBind (decTerm tc) (\ t -> just (feq t t))
  checkT30 false n tc = checkT31 (eqNat n n31) n tc
    where
    checkT31 : Bool -> Nat -> Code -> Maybe Formula
    checkT31 true _ (cnode ac bc) =
      maybeBind (decFormula ac) (\ a ->
      maybeBind (decFormula bc) (\ b ->
      just (fimp a (fimp b a))))
    checkT31 true _ _ = nothing
    checkT31 false n tc = checkT32 (eqNat n n32) n tc
      where
      checkT32 : Bool -> Nat -> Code -> Maybe Formula
      checkT32 true _ (cnode ac (cnode bc cc)) =
        maybeBind (decFormula ac) (\ a ->
        maybeBind (decFormula bc) (\ b ->
        maybeBind (decFormula cc) (\ c ->
        just (fimp (fimp a (fimp b c))
                   (fimp (fimp a b)
                         (fimp a c))))))
      checkT32 true _ _ = nothing
      checkT32 false n tc = checkT33 (eqNat n n33) n tc
        where
        checkT33 : Bool -> Nat -> Code -> Maybe Formula
        checkT33 true _ (cnode p q) =
          maybeBind (checkProof p) (\ pf ->
          maybeBind (checkProof q) (\ qf ->
          matchMP pf qf))
        checkT33 true _ _ = nothing
        checkT33 false n tc = checkT34 (eqNat n n34) n tc
          where
          checkT34 : Bool -> Nat -> Code -> Maybe Formula
          checkT34 true _ p = maybeMap fall (checkProof p)
          checkT34 false n tc = checkT35 (eqNat n n35) tc
            where
            checkT35 : Bool -> Code -> Maybe Formula
            checkT35 true p = maybeMap fcAll (checkProof p)
            checkT35 false _ = nothing

checkProof (cnode (catom n) tc) = checkTag n tc
checkProof (catom _) = nothing
checkProof (cnode (cnode _ _) _) = nothing

------------------------------------------------------------------------
-- Provability
------------------------------------------------------------------------

data Sigma (A : Set) (B : A -> Set) : Set where
  mkSigma : (x : A) -> B x -> Sigma A B

ProvableFormula : Formula -> Set
ProvableFormula A =
  Sigma Code (\ p -> Eq (checkProof p) (just A))

------------------------------------------------------------------------
-- Witness lemmas
------------------------------------------------------------------------

decVar-encVar : (v : Var) -> Eq (decVar (encVar v)) (just v)
decVar-encVar vz     = refl
decVar-encVar (vs v) = lemma (decVar (encVar v)) (decVar-encVar v)
  where
  lemma : (r : Maybe Var) -> Eq r (just v) -> Eq (maybeMap vs r) (just (vs v))
  lemma (just _)  refl = refl
  lemma nothing   ()

decTerm-encTerm : (t : Term) -> Eq (decTerm (encTerm t)) (just t)
decTerm-encTerm tzero     = refl
decTerm-encTerm (tvar v)  = lemma (decVar (encVar v)) (decVar-encVar v)
  where
  lemma : (r : Maybe Var) -> Eq r (just v) -> Eq (maybeMap tvar r) (just (tvar v))
  lemma (just _)  refl = refl
  lemma nothing   ()
decTerm-encTerm (tsucc t) = lemma (decTerm (encTerm t)) (decTerm-encTerm t)
  where
  lemma : (r : Maybe Term) -> Eq r (just t) -> Eq (maybeMap tsucc r) (just (tsucc t))
  lemma (just _)  refl = refl
  lemma nothing   ()

eqNat-refl : (n : Nat) -> Eq (eqNat n n) true
eqNat-refl zero    = refl
eqNat-refl (suc n) = eqNat-refl n

refl-provable-lemma :
  (t : Term) ->
  Eq (maybeBind (decTerm (encTerm t)) (\ s -> just (feq s s)))
     (just (feq t t))
refl-provable-lemma t = lemma (decTerm (encTerm t)) (decTerm-encTerm t)
  where
  lemma : (r : Maybe Term) -> Eq r (just t) ->
          Eq (maybeBind r (\ s -> just (feq s s))) (just (feq t t))
  lemma (just _)  refl = refl
  lemma nothing   ()

refl-provable : (t : Term) -> ProvableFormula (feq t t)
refl-provable t = mkSigma (cnode (catom n30) (encTerm t)) (refl-provable-lemma t)
