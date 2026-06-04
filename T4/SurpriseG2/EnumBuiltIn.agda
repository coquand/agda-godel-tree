{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.EnumBuiltIn --
--
-- Per T4/NEXT-SESSION-SURPRISEG2-BIGCONJ.md  Piece C : the
-- enum-by-construction that places the diagonal program code  gL
-- ( = enc (gLcodeDef Lstar) , identical to  T4.ChaitinG1CoreNumRaw 's
-- gLnameDef ) at every enumeration slot .   With  M-built := zero  the
-- big-conj K-formula degenerates to a SINGLE per-program neg at  gL ,
-- and the enumeration pin  enum (natCode 0) = gL  is  refl  by
-- construction .   N-built := suc zero  gives  Lt M N  for the
-- pigeonhole margin .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * `gL : Term`    -- the diagonal program code  enc (gLcodeDef Lstar) ,
--                     verbatim  T4.ChaitinG1CoreNumRaw.gLnameDef .
-- * `enumBuiltIn : Fun1`
--                  -- constTermFun1 gL :  applied to anything yields  gL .
-- * `enumPinAt : (k : Nat) -> Deriv (eqF (ap1 enumBuiltIn (natCode k)) gL)`
--                  -- the enumeration pin :  every slot is  gL .
-- * `M-built : Nat`  -- zero ( single enumerated program ) .
-- * `N-built : Nat`  -- suc zero ( two days  [0, 1] ) .
-- * `ltMN-built : Lt M-built N-built`
--                    -- ltZ zero :  pigeonhole margin .
-- * `constsBuiltIn : SurpriseConstsConj`
--                    -- the assembled  SurpriseConstsConj  record .

module T4.SurpriseG2.EnumBuiltIn where

open import T4.Base
open import T4.ProgEnc               using ( enc ; encApp
                                              ; tagLeaf ; tagUnary ; tagBinary )
open import T4.KdefDiag              using ( gLcodeDef )
open import T4.KGodel1BridgeDef      using ( Lstar )
open import T4.Thm12.ConstTermFun1   using ( constTermFun1 ; constTermFun1_eq
                                             ; NoVar ; NoVar_natCode
                                             ; NoVarAnd ; mkAnd )

open import T4.SurpriseG2.ConstantsConj  using ( SurpriseConstsConj )
open import T4.SurpriseG2.MetaPigeonhole as MP using ( Lt )

------------------------------------------------------------------------
-- The diagonal program code .   Same Term as  T4.ChaitinG1CoreNumRaw 's
-- gLnameDef : enc (gLcodeDef Lstar) .

gL : Term
gL = enc (gLcodeDef Lstar)

------------------------------------------------------------------------
-- The single-slot enumeration :  constant Fun1 returning  gL .

enumBuiltIn : Fun1
enumBuiltIn = constTermFun1 gL

------------------------------------------------------------------------
-- NoVar_encApp / NoVar_enc :  the  encApp / enc  outputs are CLOSED
-- regardless of the term  t  being encoded ( enc rewraps every
-- ap1/ap2/var/O as a Pair-with-natCode tag , dropping  t 's structure
-- entirely ;  see  T4.ProgEnc 's encApp definition ) .   We give
-- direct structural recursion .

NoVar_encApp : (t rest : Term) -> NoVar rest -> NoVar (encApp t rest)
NoVar_encApp O          rest nvr = mkAnd (NoVar_natCode tagLeaf) nvr
NoVar_encApp (var k)    rest nvr = mkAnd (NoVar_natCode tagLeaf) nvr
NoVar_encApp (ap1 f t)  rest nvr =
  mkAnd (NoVar_natCode tagUnary) (NoVar_encApp t rest nvr)
NoVar_encApp (ap2 g a b) rest nvr =
  mkAnd (NoVar_natCode tagBinary)
        (NoVar_encApp a (encApp b rest) (NoVar_encApp b rest nvr))

NoVar_enc : (t : Term) -> NoVar (enc t)
NoVar_enc t = NoVar_encApp t O tt

NoVar_gL : NoVar gL
NoVar_gL = NoVar_enc (gLcodeDef Lstar)

enumPinAt : (k : Nat) -> Deriv (eqF (ap1 enumBuiltIn (natCode k)) gL)
enumPinAt k = constTermFun1_eq gL NoVar_gL (natCode k)

------------------------------------------------------------------------
-- Pigeonhole margin :  M-built := zero ,  N-built := suc zero .

M-built : Nat
M-built = zero

N-built : Nat
N-built = suc zero

ltMN-built : Lt M-built N-built
ltMN-built = MP.ltZ zero

------------------------------------------------------------------------
-- The assembled  SurpriseConstsConj  record .

constsBuiltIn : SurpriseConstsConj
constsBuiltIn = record
  { N    = N-built
  ; M    = M-built
  ; enum = enumBuiltIn
  }
