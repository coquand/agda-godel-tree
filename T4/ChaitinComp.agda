{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinComp -- the standalone Goedel-Chaitin FIRST incompleteness
-- theorem, Con-FREE and at a NUMERAL subject (the faithful representation:
-- the proved formula is  K(natCode n) > L  with the subject a numeral
-- Snn...0 -- surprise.pdf p.2 "the integer x"; elements.pdf SS18 "the numeral
-- xi-bar = S...S0").  Because the subject IS a numeral, num and codeTerm
-- coincide on it (num_eq_code), so the recogniser soundness  bridgeCompCore
-- (numeral-indexed) is the FAITHFUL drop-in -- NO codeTermF, NO num-vs-codeTerm
-- wall, and  decode  is needed only to read the integer value off the slot
-- (decode (num (natCode n)) = natCode n), not to coerce coders.
--
-- This BYPASSES the symbolic  SpikeChaitin.Search  interface (whose  out : Fun1
-- / codeFormula -form  bridge  forced the spurious "symbolic subject" question)
-- and assembles directly from the shipped numeral pieces:
--
--   * bridgeCompCore  (BridgeComp)  -- the recogniser SOUNDNESS: a firing
--     numeric match  hmatch  at the found proof  pNeg  (eqInd against the
--     rebuilt code  negAtomCompOf ell srch (natCode n))  gives  dNeg : thmT
--     pNeg = codeFormula (neg (atomComp ell srch (natCode n))) ;
--   * dPos = CompressComp.dPosComp  (Thm12/13 Sigma_1-completeness)  -- T
--     proves  Comp_L(natCode n) , the short program  g  computes its output;
--   * dExF = DefWit.dExFGen  (D1 necessitated  axExFalso ).
--
-- Then two  encoded_mp  give the constructed inconsistency proof  mp2 :
--   thmT (f) = code(0=1) ,   f := cmp (cmp cExF cPos) pNeg ,
-- with NO Con (= CompressComp.chaitinBarrierFinishComp MINUS its con_inst +
-- final mp).  FIT is upstream (it produces  hmatch  via the bounded search at
-- the found numeral); here  hmatch  + the self-naming  h : srch ell = natCode n
-- ( g(L) = x0 ) + the length premise  dLen  are the inputs.

module T4.ChaitinComp where

open import T4.Base
open import T4.ThmT          using ( thmT )
open import T4.Num           using ( num )
open import T4.Code          using ( codeFormula ; codeTerm ; codeFalse ; falseF )
open import T4.Encode        using ( encode )
open import T4.LenR          using ( lenR )
open import T4.IsNat         using ( isNat )
open import T4.ParseRoundtrip using ( linTop )
open import T4.DefWit        using ( cImp ; dExFGen )
open import T4.CompressComp  using ( atomComp ; cPosComp ; dPosComp )
open import T4.NegAtomComp   using ( negAtomCompOf )
open import T4.BridgeComp    using ( bridgeCompCore )
open import T4.BridgeSkel    using ( bridgeToCodeFormula )
open import T4.Counting      using ( eqInd )
open import T4.ConInj        using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp )

open import BRA3.ChurchLeq      using ( leq )
open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- chaitin_inconsistency_comp -- the Con-FREE Chaitin-Goedel I at a numeral
-- subject  natCode n , recogniser soundness + both Stage-2 legs CONCRETE.

chaitin_inconsistency_comp :
  (ell : Term) (srch : Fun1) (n : Nat) ->
  (eN : isNat ell) ->                                            -- ell (= L) is a numeral
  (dLen : Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell)) -> -- the name of g fits L
  (h : Deriv (eqF (ap1 srch ell) (natCode n))) ->               -- self-naming: g(L) = n
  (pNeg : Term) ->                                              -- the found proof code  w0
  (hmatch :                                                     -- the search's numeric match
     Deriv (eqF (eqInd (ap1 thmT pNeg)
                       (ap1 (negAtomCompOf ell srch) (natCode n)))
                (ap1 s O))) ->
  Deriv (eqF (ap1 thmT
               (cmp (cmp (encode (axExFalso (atomComp ell srch (natCode n)) falseF))
                         (cPosComp ell srch (natCode n) eN dLen h))
                    pNeg))
             codeFalse)
chaitin_inconsistency_comp ell srch n eN dLen h pNeg hmatch =
  let y : Term
      y = natCode n
      A : Formula
      A = atomComp ell srch y
      cPos : Term
      cPos = cPosComp ell srch y eN dLen h
      cExF : Term
      cExF = encode (axExFalso A falseF)

      -- recogniser soundness:  dNeg = thmT pNeg = codeFormula (neg A) .
      dNeg : Deriv (eqF (ap1 thmT pNeg) (codeFormula (neg A)))
      dNeg = bridgeCompCore ell srch n pNeg hmatch

      -- Stage 3:  two encoded_mp give  thmT proves codeFalse .
      mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos))
                       (cImp (codeFormula (neg A)) codeFalse))
      mp1 = encoded_mp cExF cPos (codeFormula A) (cImp (codeFormula (neg A)) codeFalse)
              (dExFGen A) (dPosComp ell srch y eN dLen h)
      mp2 : Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) pNeg)) codeFalse)
      mp2 = encoded_mp (cmp cExF cPos) pNeg (codeFormula (neg A)) codeFalse mp1 dNeg
  in mp2

------------------------------------------------------------------------
-- chaitin_inconsistency_symbolic -- the Nelson-faithful (B) route: the
-- SAME Con-free inconsistency, now for a SYMBOLIC subject  subj  (the search
-- output  g(L) , not a meta-literal  natCode n ), with the ENTIRE residual
-- isolated to ONE Deriv  numEqCode : num subj = codeTerm subj  -- which is
-- num_eq_code EXACTLY when  subj  is a numeral (chaitin-G1-statement.tex
-- rem:subjcode / rem:valuecoded; Nelson Elements SS19 #4: the subject is
-- carried value-coded, as  Name x = num x ).
--
-- This GENERALISES chaitin_inconsistency_comp from  natCode n  to symbolic
-- subj :  the num-headed recogniser soundness  bridgeToCodeFormula  (=
-- bridgeSkel + skelOf_cong on numEqCode) lands  dNeg  in the codeFormula form
-- the ex-falso consumes, and  num/decode  carry the subject value-coded.  The
-- only place the value-coder  num  meets the syntax-coder  codeTerm  is the
-- single hypothesis  numEqCode  -- the term-vs-numeral boundary, made literal.

chaitin_inconsistency_symbolic :
  (ell : Term) (srch : Fun1) (subj : Term) ->
  (eN : isNat ell) ->                                            -- ell (= L) is a numeral
  (dLen : Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell)) -> -- the name of g fits L
  (h : Deriv (eqF (ap1 srch ell) subj)) ->                      -- self-naming: g(L) = subj
  (pNeg : Term) ->                                              -- the found proof code  w0
  (numEqCode : Deriv (eqF (ap1 num subj) (codeTerm subj))) ->   -- THE residual (num_eq_code on a numeral)
  (hmatch :                                                     -- the search's numeric match
     Deriv (eqF (eqInd (ap1 thmT pNeg)
                       (ap1 (negAtomCompOf ell srch) subj))
                (ap1 s O))) ->
  Deriv (eqF (ap1 thmT
               (cmp (cmp (encode (axExFalso (atomComp ell srch subj) falseF))
                         (cPosComp ell srch subj eN dLen h))
                    pNeg))
             codeFalse)
chaitin_inconsistency_symbolic ell srch subj eN dLen h pNeg numEqCode hmatch =
  let A : Formula
      A = atomComp ell srch subj
      cPos : Term
      cPos = cPosComp ell srch subj eN dLen h
      cExF : Term
      cExF = encode (axExFalso A falseF)

      -- recogniser soundness (num-headed) + the single numEqCode bridge:
      --   dNeg = thmT pNeg = codeFormula (neg A) .
      dNeg : Deriv (eqF (ap1 thmT pNeg) (codeFormula (neg A)))
      dNeg = bridgeToCodeFormula ell srch subj pNeg numEqCode hmatch

      mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos))
                       (cImp (codeFormula (neg A)) codeFalse))
      mp1 = encoded_mp cExF cPos (codeFormula A) (cImp (codeFormula (neg A)) codeFalse)
              (dExFGen A) (dPosComp ell srch subj eN dLen h)
      mp2 : Deriv (eqF (ap1 thmT (cmp (cmp cExF cPos) pNeg)) codeFalse)
      mp2 = encoded_mp (cmp cExF cPos) pNeg (codeFormula (neg A)) codeFalse mp1 dNeg
  in mp2
