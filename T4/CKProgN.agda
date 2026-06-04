{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CKProgN -- the number-code single counting atom  g N = 0  of surprise-GII
-- and its bare-argument characteristic atom  ( SURPRISE-GII-NUMBERCODE-HANDOFF
-- S3.2 ).  Number-code mirror of  T4.CKProg :  the enumeration is the IDENTITY
-- ( idx = I , folded in by  T4.DefIndN.defCountN ), so there is NO  enum  table;
-- the finite candidate set is the initial segment  { p < N }  and "no short
-- program describes  z " is the single atom  g N = 0 , where
--
--   g n  =  sum_{x<n} defIndN(x, z)   ( defCountN  over the identity ).
--
--   CKN : Fun2 ,   ap2 CKN u x = O   iff   some  p < N  defines  u  in  x  steps
--   ( the  isZero  flip, native  O = false / s O = true , as in  CKProg ).
--
--   CKN = Post isZero (Fan pi (Lift1 (constN N)) defCountN)
--   ap2 CKN u x = isZero ( ap2 defCountN (pi u x) (natCode N) )                  (PROVED)
--             = isZero ( sum_{j=0}^{N} defIndN(j, pi u x) ) .
--
-- N : Nat  is the (margin) count bound, kept SYMBOLIC ( = Bnat / NthrN-as-Nat
-- downstream; NEVER materialised).  CKN is a closed combinator given it.

module T4.CKProgN where

open import T4.Base
open import BRA3.Church   using ( isZero ; pi )
open import BRA3.Dispatch using ( constN ; constN_eq )
open import T4.Num        using ( num )
open import T4.Code       using ( codeFormula ; codeTerm )
open import T4.DefWit     using ( cEqTm ; cNeg )
open import T4.CgiClash   using ( cAp2f ; cVarc )
open import T4.DefIndN    using ( defCountN )

-- N : the meta count margin ( N := Bnat  downstream ).
module _ (N : Nat) where

  ----------------------------------------------------------------------
  -- SECTION 1.  The concrete counting program  CKN : Fun2 .

  CKN : Fun2
  CKN = Post isZero (Fan pi (Lift1 (constN N)) defCountN)

  -- ap2 CKN u x = isZero ( ap2 defCountN (pi u x) (natCode N) )   (PROVED).
  CKN_eq :
    (uT xT : Term) ->
    Deriv (eqF (ap2 CKN uT xT)
               (ap1 isZero (ap2 defCountN (ap2 pi uT xT) (natCode N))))
  CKN_eq uT xT =
    let ePost : Deriv (eqF (ap2 CKN uT xT)
                           (ap1 isZero (ap2 (Fan pi (Lift1 (constN N)) defCountN) uT xT)))
        ePost = axPost isZero (Fan pi (Lift1 (constN N)) defCountN) uT xT

        eFan : Deriv (eqF (ap2 (Fan pi (Lift1 (constN N)) defCountN) uT xT)
                          (ap2 defCountN (ap2 pi uT xT)
                                         (ap2 (Lift1 (constN N)) uT xT)))
        eFan = axFan pi (Lift1 (constN N)) defCountN uT xT

        eIdx : Deriv (eqF (ap2 (Lift1 (constN N)) uT xT) (natCode N))
        eIdx = ruleTrans (axLift (constN N) uT xT) (constN_eq N uT)

        eRange : Deriv (eqF (ap2 defCountN (ap2 pi uT xT) (ap2 (Lift1 (constN N)) uT xT))
                            (ap2 defCountN (ap2 pi uT xT) (natCode N)))
        eRange = congR defCountN (ap2 pi uT xT) eIdx
    in ruleTrans ePost
         (cong1 isZero (ruleTrans eFan eRange))

  ----------------------------------------------------------------------
  -- SECTION 2.  The bare-argument characteristic atom (cAp2f, two bare vars).
  --   All code identities by  refl  ( codeFormula / codeTerm  match
  --   cEqTm / cAp2f / cVarc / cNeg ; cO = codeTerm O = O ).

  charAtomN : Nat -> Nat -> Formula
  charAtomN i0 i1 = eqF (ap2 CKN (var i0) (var i1)) O

  charAtomCodeN : Term -> Term -> Term
  charAtomCodeN s0 s1 = cEqTm (cAp2f CKN s0 s1) O

  charAtomN_at_vars :
    (i0 i1 : Nat) ->
    Eq (codeFormula (charAtomN i0 i1)) (charAtomCodeN (cVarc i0) (cVarc i1))
  charAtomN_at_vars i0 i1 = refl

  -- Step-2 target: subject installed num-raw  ap1 num x0 , run-length still
  -- coded  cVarc x1 .
  charAtomCodeN_num_subj :
    (x0 : Term) (i1 : Nat) ->
    Eq (charAtomCodeN (ap1 num x0) (cVarc i1))
       (cEqTm (cAp2f CKN (ap1 num x0) (cVarc i1)) O)
  charAtomCodeN_num_subj x0 i1 = refl

  ----------------------------------------------------------------------
  -- SECTION 3.  The negated atom -- the stage predicate body
  --   S(r) := Deriv (neg (eqF (ap2 CKN (var x0) (var x1)) O)) .

  charNegN : Nat -> Nat -> Formula
  charNegN i0 i1 = neg (charAtomN i0 i1)

  charNegCodeN : Term -> Term -> Term
  charNegCodeN s0 s1 = cNeg (charAtomCodeN s0 s1)

  charNegN_at_vars :
    (i0 i1 : Nat) ->
    Eq (codeFormula (charNegN i0 i1)) (cNeg (cEqTm (cAp2f CKN (cVarc i0) (cVarc i1)) O))
  charNegN_at_vars i0 i1 = refl
