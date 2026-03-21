{-# OPTIONS --without-K --exact-split #-}

module ChwistekSyntax where

------------------------------------------------------------------------
-- A. Basic definitions
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

eqCong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
eqCong f refl = refl

------------------------------------------------------------------------
-- Binary-tree code type

data Code : Set where
  catom : Nat -> Code
  cnode : Code -> Code -> Code

------------------------------------------------------------------------
-- Variables (de Bruijn indices for term quantification)

data Var : Set where
  vz : Var
  vs : Var -> Var

------------------------------------------------------------------------
-- Code variables (de Bruijn indices for code quantification)

data CVar : Set where
  cvz : CVar
  cvs : CVar -> CVar

------------------------------------------------------------------------
-- Code expressions

data CExp : Set where
  cvar   : CVar -> CExp
  clit   : Code -> CExp
  ccheck : CExp -> CExp
  csub   : CExp -> CExp -> CExp    -- code-level substitution (quine trick)

------------------------------------------------------------------------
-- Terms

data Term : Set where
  tvar  : Var -> Term
  tzero : Term
  tsucc : Term -> Term

------------------------------------------------------------------------
-- Formulas

data Formula : Set where
  fbot  : Formula
  feq   : Term -> Term -> Formula
  fimp  : Formula -> Formula -> Formula
  fall  : Formula -> Formula             -- term quantification
  fcode : Code -> Formula                -- code leaf
  fceq  : CExp -> CExp -> Formula        -- code expression equality
  fcAll : Formula -> Formula             -- code quantification

------------------------------------------------------------------------
-- B. Encoding into Code
------------------------------------------------------------------------

-- Tag scheme:
--   0  = variable marker       14 = cvz marker
--   1  = zero / vs marker      15 = cvs marker
--   2  = succ marker           16 = cvar marker
--   3  = bot marker            17 = clit marker
--   4  = eq marker             18 = ccheck marker
--   5  = imp marker
--   6  = forall marker         10 = shole (schema)
--   7  = code-leaf marker      11 = sconst (schema)
--   8  = ceq marker            12 = simp (schema)
--   9  = cAll marker           13 = sall (schema)
--                              30-34 = proof tags

-- Tag constants for readability

n8 : Nat
n8 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

n9 : Nat
n9 = suc n8

n14 : Nat
n14 = suc (suc (suc (suc (suc n9))))

n15 : Nat
n15 = suc n14

n16 : Nat
n16 = suc n15

n17 : Nat
n17 = suc n16

n18 : Nat
n18 = suc n17

n19 : Nat
n19 = suc n18

encVar : Var -> Code
encVar vz     = catom zero
encVar (vs v) = cnode (catom (suc zero)) (encVar v)

encCVar : CVar -> Code
encCVar cvz     = catom n14
encCVar (cvs v) = cnode (catom n15) (encCVar v)

encCExp : CExp -> Code
encCExp (cvar v)   = cnode (catom n16) (encCVar v)
encCExp (clit c)   = cnode (catom n17) c
encCExp (ccheck e)   = cnode (catom n18) (encCExp e)
encCExp (csub e1 e2) = cnode (catom n19) (cnode (encCExp e1) (encCExp e2))

encTerm : Term -> Code
encTerm (tvar v)  = cnode (catom zero) (encVar v)
encTerm tzero     = catom (suc zero)
encTerm (tsucc t) = cnode (catom (suc (suc zero))) (encTerm t)

encFormula : Formula -> Code
encFormula fbot       = catom (suc (suc (suc zero)))
encFormula (feq s t)  =
  cnode (catom (suc (suc (suc (suc zero)))))
        (cnode (encTerm s) (encTerm t))
encFormula (fimp a b) =
  cnode (catom (suc (suc (suc (suc (suc zero))))))
        (cnode (encFormula a) (encFormula b))
encFormula (fall a)   =
  cnode (catom (suc (suc (suc (suc (suc (suc zero)))))))
        (encFormula a)
encFormula (fcode c)  =
  cnode (catom (suc (suc (suc (suc (suc (suc (suc zero))))))))
        c
encFormula (fceq e1 e2) =
  cnode (catom n8) (cnode (encCExp e1) (encCExp e2))
encFormula (fcAll a) =
  cnode (catom n9) (encFormula a)

------------------------------------------------------------------------
-- C. Structural substitution (de Bruijn, term variables)
------------------------------------------------------------------------

liftTerm : Term -> Term
liftTerm (tvar v)  = tvar (vs v)
liftTerm tzero     = tzero
liftTerm (tsucc t) = tsucc (liftTerm t)

substTerm0 : Term -> Term -> Term
substTerm0 s (tvar vz)     = s
substTerm0 s (tvar (vs v)) = tvar v
substTerm0 s tzero         = tzero
substTerm0 s (tsucc t)     = tsucc (substTerm0 s t)

substFormula0 : Term -> Formula -> Formula
substFormula0 s fbot         = fbot
substFormula0 s (feq t u)    = feq (substTerm0 s t) (substTerm0 s u)
substFormula0 s (fimp a b)   = fimp (substFormula0 s a) (substFormula0 s b)
substFormula0 s (fall a)     = fall (substFormula0 (liftTerm s) a)
substFormula0 s (fcode c)    = fcode c
substFormula0 s (fceq e1 e2) = fceq e1 e2   -- CExp has no term variables
substFormula0 s (fcAll a)    = fcAll (substFormula0 s a)

------------------------------------------------------------------------
-- D. Basic proof system (Hilbert-style)
------------------------------------------------------------------------

data Proof : Formula -> Set where
  ax-refl : (t : Term) -> Proof (feq t t)
  ax-k    : (A B : Formula) -> Proof (fimp A (fimp B A))
  ax-s    : (A B C : Formula) ->
            Proof (fimp (fimp A (fimp B C))
                  (fimp (fimp A B)
                        (fimp A C)))
  mp      : {A B : Formula} -> Proof (fimp A B) -> Proof A -> Proof B
  gen     : {A : Formula} -> Proof A -> Proof (fall A)
  cgen    : {A : Formula} -> Proof A -> Proof (fcAll A)

------------------------------------------------------------------------
-- E. Simple derived notions
------------------------------------------------------------------------

FNot : Formula -> Formula
FNot A = fimp A fbot

Contr : Formula
Contr = fbot

Provable : Formula -> Set
Provable A = Proof A

------------------------------------------------------------------------
-- F. Structural lemmas
------------------------------------------------------------------------

substTerm0-var-zero : (s : Term) -> Eq (substTerm0 s (tvar vz)) s
substTerm0-var-zero s = refl

substTerm0-zero : (s : Term) -> Eq (substTerm0 s tzero) tzero
substTerm0-zero s = refl

substFormula0-bot : (s : Term) -> Eq (substFormula0 s fbot) fbot
substFormula0-bot s = refl
