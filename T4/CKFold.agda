{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CKFold -- the PROGRAM-RANGE fold of the surprise-GII incompressibility
-- conjunction.  (Task (a), subtask 1 of T4/SURPRISE-GII-HANDOFF.md:
-- "fold define_p over enum".)
--
-- The shipped  T4.DefinePExp.Kfunctor  folds the negated  define_p  atoms over
-- the FULL index range  0..N :
--
--   KExp N = econjUpTo negDefineExp N = /\_{j=0}^{N} ¬ define_{p_j} .
--
-- The external induction of surprise-GII (clos-corrected.md, the step
-- S(r) -> S(r+1)) peels enumerated programs one at a time, and therefore needs
-- the conjunction over the SHRINKING program range  r..N , not the fixed  0..N .
-- This module builds that range fold and its shared object  Fun2  K-functor,
-- exactly mirroring DefinePExp's  KExp / KCode / Kfunctor / Kfunctor_code :
--
--   KExpFrom enum r k      = /\_{j=r}^{r+k} ¬ define_{p_j}        (k+1 conjuncts)
--   KCodeFrom enum r k a   = its meta code (right-nested cAnd)
--   KfunctorFrom enum r k : Fun2 ,
--       ap2 (KfunctorFrom r k) a b = KCodeFrom r k a              (PROVED).
--
-- It reuses every shipped piece (the  define_p  atoms of  T4.DefinePExp , the
-- ecAnd2  builder of  T4.ConjCodeExp ,  compile2 / compile2_eq  of  T4.AbsFun2 );
-- only the range index discipline is new.  The genuine characteristic "= O"
-- computation and the bare-argument restatement (task (a), subtasks 2-3) are
-- NOT done here -- this delivers the code-functor shape of the shipped
-- Kfunctor, range-restricted, as the first fold building block.

module T4.CKFold where

open import T4.Base
open import T4.AbsFun2  using ( Exp2 ; denote2 ; compile2 ; compile2_eq )
open import T4.ConjCodeExp using ( ecAnd2 )
open import T4.DefWit    using ( cAnd )
open import T4.DefinePExp using ( negDefineExp ; negDefineCode )

------------------------------------------------------------------------
-- Meta index addition (local, 3 lines -- avoids a heavy import).
--   natAdd r k = r + k  by recursion on the first argument.

natAdd : Nat -> Nat -> Nat
natAdd zero    m = m
natAdd (suc n) m = suc (natAdd n m)

-- enum : the enumerator of Berry's finite program set  S  (the single
-- foundational input, exactly as in  T4.DefinePExp ).
module _ (enum : Fun1) where

  ----------------------------------------------------------------------
  -- SECTION 1.  The program-range conjunction as an  Exp2 .
  --   KExpFrom r k = ¬define_{p_{r+k}} /\ ... /\ ¬define_{p_r}
  --   (largest index outermost, mirroring  econjUpTo 's orientation; the
  --   range is  r .. r+k , i.e.  k+1  conjuncts).

  KExpFrom : (r k : Nat) -> Exp2
  KExpFrom r zero    = negDefineExp enum r
  KExpFrom r (suc k) =
    ecAnd2 (negDefineExp enum (natAdd r (suc k))) (KExpFrom r k)

  ----------------------------------------------------------------------
  -- SECTION 2.  Its meta code (right-nested  cAnd , same orientation).

  KCodeFrom : (r k : Nat) -> Term -> Term
  KCodeFrom r zero    a = negDefineCode enum r a
  KCodeFrom r (suc k) a =
    cAnd (negDefineCode enum (natAdd r (suc k)) a) (KCodeFrom r k a)

  -- Denotation contract:  denote2 (KExpFrom r k) a b = KCodeFrom r k a .
  -- (zero case definitional via  negDefineExp_pin ; suc case via  cAnd_pin  +
  -- the recursive call, exactly as DefinePExp's  KExp_pin .)
  KExpFrom_pin :
    (r k : Nat) (a b : Term) ->
    Eq (denote2 (KExpFrom r k) a b) (KCodeFrom r k a)
  KExpFrom_pin r zero    a b = refl
  KExpFrom_pin r (suc k) a b =
    eqCong (\ z -> cAnd (negDefineCode enum (natAdd r (suc k)) a) z)
           (KExpFrom_pin r k a b)

  ----------------------------------------------------------------------
  -- SECTION 3.  The range K-functor (Fun2) and its proved code equation.

  KfunctorFrom : (r k : Nat) -> Fun2
  KfunctorFrom r k = compile2 (KExpFrom r k)

  -- ap2 (KfunctorFrom r k) a b = denote2 (KExpFrom r k) a b   (PROVED).
  KfunctorFrom_eq :
    (r k : Nat) (a b : Term) ->
    Deriv (eqF (ap2 (KfunctorFrom r k) a b) (denote2 (KExpFrom r k) a b))
  KfunctorFrom_eq r k a b = compile2_eq (KExpFrom r k) a b

  -- ap2 (KfunctorFrom r k) a b = KCodeFrom r k a   (PROVED) -- the explicit
  -- code-term shape the downstream recogniser / thm12 sides will consume,
  -- with  x0 := a  in the  num -data slot (as in the shipped  Kfunctor_code ).
  KfunctorFrom_code :
    (r k : Nat) (a b : Term) ->
    Deriv (eqF (ap2 (KfunctorFrom r k) a b) (KCodeFrom r k a))
  KfunctorFrom_code r k a b =
    eqSubst (\ z -> Deriv (eqF (ap2 (KfunctorFrom r k) a b) z))
            (KExpFrom_pin r k a b)
            (KfunctorFrom_eq r k a b)
