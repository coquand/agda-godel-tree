{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CGINumRaw -- Chaitin-Goedel I, num-raw, completed to falseF.
--
-- The Con-free clash core is T4.ChaitinG1Hit.chaitin_G1_hit (num-raw: dPos via
-- thm13_singulary, dExF via the code-agnostic encoded_exfalso, dNeg via the
-- recogniser, all meeting at  P = codeFXeqY1 compHit z0 (s O)  by refl -- no
-- codeFormula, no codeTerm, no isNat; the subject z0 is a Term).  It returns
--   thmT (cgiProof ...) = codeFalse                       (T proves 0=1 is provable).
-- Here we add the single external step:  Con  (= T does not prove 0=1, the
-- ConSchema  neg (thmT (var 0) = codeFalse))  refutes the built proof, giving
--   falseF .
--
-- This is surprise.pdf statement (1) p.4 read as: from a proof that  K(x_) > L0
-- (the recogniser firing -> dNeg) and the fact that  x_  has a short description
-- (the bounded-search hit  h), we BUILD a proof of  0=1 , whose existence is
-- absurd under Con.
--
-- STILL TO SUPPLY (the search/run layer -- the honest surprise.pdf inputs, none
-- needing codeFormula/isNat):
--   * compHit : the concrete bounded-search indicator for "exists p of length
--     <= L0 and n with definable(p, z, n)"  (T4.Definable + bounded search);
--   * h  : compHit z0 = 1   -- "z0 has a short description" (the looping program
--     g_L witnesses it; surprise.pdf "it is easy to give a program ... describing
--     the running");
--   * dNeg : thmT w0 = cNeg (codeFXeqY1 compHit z0 1)  -- the recogniser firing
--     ("w0 proves K(z0) > L0");
--   * z0 := out_L w0  -- the read-off subject, a Term, via decode_num_id (no isNat).

module T4.CGINumRaw where

open import T4.Base
open import T4.ThmT          using ( thmT )
open import T4.Code          using ( codeFalse ; falseF )
open import T4.DefWit        using ( cNeg )
open import T4.ConInj        using ( ConSchema ; cmp )
open import T4.Thm12.All     using ( thm12 ; fst )
open import T4.Thm12.Thm13   using ( codeFXeqY1 )
open import T4.EncodedProp   using ( exfProof )
open import T4.ChaitinG1Hit  using ( chaitin_G1_hit )

open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- The constructed proof  z  (= f), exactly as in chaitin_G1_hit's conclusion.

cgiProof : (compHit : Fun1) (z0 w0 : Term) -> Term
cgiProof compHit z0 w0 =
  cmp (cmp (exfProof (codeFXeqY1 compHit z0 (ap1 s O)) codeFalse)
           (ap1 (fst (thm12 compHit)) z0))
      w0

------------------------------------------------------------------------
-- CGI completed:  Con + (search hit h) + (recogniser dNeg)  ==>  falseF .
-- The clash builds  thmT (cgiProof ...) = codeFalse  (Con-free, num-raw); Con
-- refutes it.

cgi_inconsistent :
  Deriv ConSchema ->
  (compHit : Fun1) (z0 w0 : Term) ->
  Deriv (eqF (ap1 compHit z0) (ap1 s O)) ->                                  -- h:  z0 has a short description
  Deriv (eqF (ap1 thmT w0) (cNeg (codeFXeqY1 compHit z0 (ap1 s O)))) ->      -- dNeg:  w0 proves K(z0) > L0
  Deriv falseF
cgi_inconsistent con compHit z0 w0 h dNeg =
  let X : Formula
      X = eqF (ap1 thmT (cgiProof compHit z0 w0)) codeFalse
      dFalse : Deriv X
      dFalse = chaitin_G1_hit compHit z0 w0 h dNeg
      con_inst : Deriv (neg X)
      con_inst = ruleInst zero (cgiProof compHit z0 w0) con
  in mp (mp (axExFalso X falseF) dFalse) con_inst
