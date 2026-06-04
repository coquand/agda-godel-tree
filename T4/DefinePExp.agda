{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.DefinePExp -- the  define_p  object  Fun2  family + the shared object
-- Fun2  K-functor of surprise-GII (blocks 1+2 of NEXT-SESSION-SURPRISE-GII-PLAN).
--
-- For each enumerated program  p_j = ap1 enum (natCode j)  (Berry's finite
-- set  S  of programs of size  <= L* , ranged over by  enum : Fun1 ), the
-- definability atom is
--
--   define_{p_j}(x0, j)  :=  eqF (ap2 runProg p_j (ap1 num x0)) (ap1 s (natCode j))
--                              ("running  p_j  on length  x0  yields  j+1").
--
-- Its CODE is assembled as an  Exp2  (T4.AbsFun2) via the code-builder smart
-- constructors of  T4.ConjCodeExp , with the subject  x0  sitting in the
--  ap1 num -data slot ( eap1 num evar0 ), NEVER as a frozen  num (var l)  code.
--
-- The big conjunction  K(x0, p_0,...,p_N) = /\_{j<=N} ¬ define_{p_j}(x0, j)
-- is  econjUpTo (\ j -> ecNeg2 (definePExp j)) N , an  Exp2  in the two object
-- data slots  evar0 = x0  (subject / run length) and  evar1 = r  (kept free for
-- the run/index discipline; unused in this base shape).  compile2  turns it
-- into the genuine  Kfunctor : Fun2  with
--
--   ap2 (Kfunctor N) a b = denote2 (KExp N) a b = code K(num a, p_0..p_N)
--
-- as a PROVED  Deriv  (Kfunctor_eq) -- the literally-identical object term that
-- must appear across surprise-GII Steps 2 / 4 / 6 (W's recognition, Chaitin's
-- antecedent, thm12's output) so the three steps compose by  refl .

module T4.DefinePExp where

open import T4.Base
open import T4.Num using ( num )
open import T4.Kdef using ( runProg )
open import T4.AbsFun2
  using ( Exp2 ; evar0 ; evar1 ; econst ; eap1 ; eap2 ; denote2
        ; compile2 ; compile2_eq )
open import T4.ConjCodeExp
  using ( enat2 ; ecNeg2 ; ecEqTm2 ; ecAp1f2 ; ecAp2f2 ; econjUpTo )
open import T4.DefWit using ( cEqTm ; cNeg ; cAnd )
open import T4.CgiClash using ( cAp1f ; cAp2f )
open import T4.Thm12.ConstTermFun1 using ( NoVar ; NoVar_natCode )

-- enum : the enumerator of Berry's finite program set  S  (the single
-- foundational input of this block, alongside  enum_correct  downstream).
module _ (enum : Fun1) where

  ----------------------------------------------------------------------
  -- SECTION 1.  The enumerated program names (Berry's set  S ).
  --   pcodeOf j = ap1 enum (natCode j) ; var-free because  natCode j  is.

  pcodeOf : Nat -> Term
  pcodeOf j = ap1 enum (natCode j)

  NoVar_pcodeOf : (j : Nat) -> NoVar (pcodeOf j)
  NoVar_pcodeOf j = NoVar_natCode j

  ----------------------------------------------------------------------
  -- SECTION 2.  The  define_p  atom as an  Exp2  (subject  x0  in the  num -slot).

  definePExp : Nat -> Exp2
  definePExp j =
    ecEqTm2 (ecAp2f2 runProg (econst (pcodeOf j) (NoVar_pcodeOf j)) (eap1 num evar0))
            (ecAp1f2 s (enat2 j))

  -- Meta code of the atom : exactly  denote2 (definePExp j) a b  (by  refl ).
  definePCode : Nat -> Term -> Term
  definePCode j a =
    cEqTm (cAp2f runProg (pcodeOf j) (ap1 num a)) (cAp1f s (natCode j))

  definePExp_pin :
    (j : Nat) (a b : Term) ->
    Eq (denote2 (definePExp j) a b) (definePCode j a)
  definePExp_pin j a b = refl

  ----------------------------------------------------------------------
  -- SECTION 3.  Negated conjunct and the big conjunction  K .

  negDefineExp : Nat -> Exp2
  negDefineExp j = ecNeg2 (definePExp j)

  negDefineCode : Nat -> Term -> Term
  negDefineCode j a = cNeg (definePCode j a)

  negDefineExp_pin :
    (j : Nat) (a b : Term) ->
    Eq (denote2 (negDefineExp j) a b) (negDefineCode j a)
  negDefineExp_pin j a b = refl

  -- K(x0, p_0..p_N) = /\_{j<=N} ¬ define_{p_j}(x0, j)  as an  Exp2 .
  KExp : Nat -> Exp2
  KExp N = econjUpTo negDefineExp N

  -- Its meta code (right-nested  cAnd , mirroring  econjUpTo ).
  KCode : Nat -> Term -> Term
  KCode zero    a = negDefineCode zero a
  KCode (suc n) a = cAnd (negDefineCode (suc n) a) (KCode n a)

  KExp_pin :
    (N : Nat) (a b : Term) ->
    Eq (denote2 (KExp N) a b) (KCode N a)
  KExp_pin zero    a b = refl
  KExp_pin (suc n) a b =
    eqCong (\ z -> cAnd (negDefineCode (suc n) a) z) (KExp_pin n a b)

  ----------------------------------------------------------------------
  -- SECTION 4.  The shared object  Fun2  K-functor.

  Kfunctor : Nat -> Fun2
  Kfunctor N = compile2 (KExp N)

  -- ap2 (Kfunctor N) a b = denote2 (KExp N) a b   (PROVED).
  Kfunctor_eq :
    (N : Nat) (a b : Term) ->
    Deriv (eqF (ap2 (Kfunctor N) a b) (denote2 (KExp N) a b))
  Kfunctor_eq N a b = compile2_eq (KExp N) a b

  -- ap2 (Kfunctor N) a b = KCode N a   (PROVED) -- the explicit code-term shape
  -- that surprise-GII Steps 2 / 4 / 6 consume, with  x0 := a  in the  num -slot.
  Kfunctor_code :
    (N : Nat) (a b : Term) ->
    Deriv (eqF (ap2 (Kfunctor N) a b) (KCode N a))
  Kfunctor_code N a b =
    eqSubst (\ z -> Deriv (eqF (ap2 (Kfunctor N) a b) z))
            (KExp_pin N a b)
            (Kfunctor_eq N a b)
