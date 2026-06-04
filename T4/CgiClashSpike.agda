{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiClashSpike -- Chaitin-Goedel I, num-raw open form: the CLASH SPIKE.
--
-- Build order step 1 (CGI-NUMRAW-HANDOFF.md SS6, riskiest-first): validate the
-- num-raw instantiation of the OPEN K-formula and that the legs meet by refl.
--
-- The open K-formula is  Kdef L x = imp (szLeq(p)=1) (neg (definable p x n))
-- with  p = var 0  (program),  n = var 1  (fuel),  subject  x  num-raw (the
-- hole  ap1 num x ).  Its code  KcodeOpen  is a hand-written concrete num-raw
-- code (independent of the wrapAll machinery -- that is step (a)).  The spike:
--
--   (1) compute  sbf spec0 (sbf spec1 KcodeOpen) = KcodeClosed  -- the GENUINELY
--       NEW substitution: var 0 := num P , var 1 := num N dropped RAW, subject
--       num X inert.  This is the analog of  sbfEq_codeFormula  for num-raw
--       codes, assembled from the shipped  sbf_step_* / sbt_step_*  one-node
--       combinators (T4.SbStep) + the num-leaf inertness  sbt_num_inert /
--       sbt_inert_NumCode  (T4.NumInert / T4.SbStep) .
--   (2) Wrap with  thmT_at_sb  twice (the two encoded substitutions) to land
--        thmT (sb-wrap) = KcodeClosed .
--   (3) Strip the implication with the size fact  (encoded_mp)  -> cNeg D .
--   (4) Assemble the inconsistency via  chaitin_G1_assembly  (= encoded_exfalso
--       + two encoded_mp) -> thmT z = codeFalse .
--
-- The positive leg (dPos), the open negative leg (dNeg) and the size fact
-- (dSize) are HYPOTHESES here (the run/size/firing facts that steps (c)-(e)
-- discharge).  Because  D := defc (num P) (num N)  is a CONCRETE function of
-- the substituents, the closed K-code's  cNeg D  matches dPos's  D  by refl;
-- that is the coherence the spike confirms.
--
-- Abstract functor parameters (their codes appear opaquely under sbt):
--   szF  = the size indicator szLeqFun L  (step (a) pins it)
--   pF   = parse        predF = predecessor        eF = evalU
-- These never reduce; only their structural positions matter for substitution.

module T4.CgiClashSpike where

open import T4.Base
open import T4.Tags using
  ( tag_sb ; tag_var ; tag_ap1 ; tag_ap2 ; tag_eq ; tag_neg ; tag_imp ; tag_mp ; tag_s )
open import T4.Code using ( codeFun1 ; codeFun2 ; codeFalse )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt ; sbt_at_O )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.SbStep using
  ( sbf_step_imp ; sbf_step_atomic ; sbf_step_neg ; sbt_step_ap1 ; sbt_step_ap2
  ; NumCode ; ncO ; ncNum ; ncAp1 ; sbt_inert_NumCode )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp ; cAnd )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.ChaitinG1 using ( chaitin_G1_assembly )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  Pure code constructors (codeTerm shapes; functor codes opaque).

cAp1f : Fun1 -> Term -> Term
cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

cAp2f : Fun2 -> Term -> Term -> Term
cAp2f g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

-- codeTerm (var k) = Pair (natCode tag_var) (natCode k).
cVarc : Nat -> Term
cVarc k = ap2 Pair (natCode tag_var) (natCode k)

------------------------------------------------------------------------
-- SECTION 2.  The clash spike.

spikeClash :
  (szF pF predF : Fun1) (eF : Fun2) ->
  (P N X w0 cPos cSize : Term) ->
  -- dNeg (open):  thmT w0 = KcodeOpen  (the recogniser firing -- step (d))
  Deriv (eqF (ap1 thmT w0)
             (cImp (cEqTm (cAp1f szF (cVarc zero)) (cAp1f s O))
                   (cNeg (cAnd
                     (cEqTm (cAp2f eF (cAp1f pF (cVarc zero)) (cVarc (suc zero)))
                            (cAp1f s (ap1 num X)))
                     (cEqTm (cAp2f eF (cAp1f pF (cVarc zero))
                                      (cAp1f predF (cVarc (suc zero))))
                            O))))) ->
  -- dSize:  thmT cSize = code(szLeq(num P) = 1)  (the size fact -- step (c)/dLenStar)
  Deriv (eqF (ap1 thmT cSize)
             (cEqTm (cAp1f szF (ap1 num P)) (cAp1f s O))) ->
  -- dPos:  thmT cPos = D  (the run, internalised num-raw via Thm13 -- step (c))
  Deriv (eqF (ap1 thmT cPos)
             (cAnd
               (cEqTm (cAp2f eF (cAp1f pF (ap1 num P)) (ap1 num N))
                      (cAp1f s (ap1 num X)))
               (cEqTm (cAp2f eF (cAp1f pF (ap1 num P))
                                (cAp1f predF (ap1 num N)))
                      O))) ->
  -- conclusion: a constructed proof code  z  with  thmT z = code(0=1) .
  Deriv (eqF (ap1 thmT
               (cmp (cmp (exfProof
                           (cAnd
                             (cEqTm (cAp2f eF (cAp1f pF (ap1 num P)) (ap1 num N))
                                    (cAp1f s (ap1 num X)))
                             (cEqTm (cAp2f eF (cAp1f pF (ap1 num P))
                                              (cAp1f predF (ap1 num N)))
                                    O))
                           codeFalse)
                         cPos)
                    (cmp (ap2 pi (natCode tag_sb)
                           (ap2 pi (ap2 Pair (natCode zero) (ap1 num P))
                             (ap2 pi (natCode tag_sb)
                               (ap2 pi (ap2 Pair (natCode (suc zero)) (ap1 num N)) w0))))
                         cSize)))
             codeFalse)
spikeClash szF pF predF eF P N X w0 cPos cSize dNeg dSize dPos = result
  where
    ----------------------------------------------------------------
    -- Code pieces, parameterised by the program-slot  prog  and the
    -- fuel-slot  fuel  (the subject hole  ap1 num X  is constant).

    szAtom : Term -> Term
    szAtom prog = cEqTm (cAp1f szF prog) (cAp1f s O)

    conj1c : Term -> Term -> Term
    conj1c prog fuel =
      cEqTm (cAp2f eF (cAp1f pF prog) fuel) (cAp1f s (ap1 num X))

    conj2c : Term -> Term -> Term
    conj2c prog fuel =
      cEqTm (cAp2f eF (cAp1f pF prog) (cAp1f predF fuel)) O

    defc : Term -> Term -> Term
    defc prog fuel = cAnd (conj1c prog fuel) (conj2c prog fuel)

    KcodeT : Term -> Term -> Term
    KcodeT prog fuel = cImp (szAtom prog) (cNeg (defc prog fuel))

    ----------------------------------------------------------------
    -- The generic single substitution pass over  KcodeT , given how the
    -- program slot  (prog -> prog')  and fuel slot  (fuel -> fuel')  move
    -- under  sbt (Pair (natCode k) S) .  Constant num-leaves are inert.

    passEq :
      (k : Nat) (S prog prog' fuel fuel' : Term) ->
      Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) prog) prog') ->
      Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) fuel) fuel') ->
      Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (KcodeT prog fuel))
                  (KcodeT prog' fuel'))
    passEq k S prog prog' fuel fuel' eProg eFuel =
      let spec : Term
          spec = ap2 Pair (natCode k) S

          -- inert constant leaves.
          e_sO : Deriv (eqF (ap2 sbt spec (cAp1f s O)) (cAp1f s O))
          e_sO = sbt_inert_NumCode (cAp1f s O) (ncAp1 s O ncO) k S

          e_sHole : Deriv (eqF (ap2 sbt spec (cAp1f s (ap1 num X)))
                                (cAp1f s (ap1 num X)))
          e_sHole = sbt_inert_NumCode (cAp1f s (ap1 num X))
                      (ncAp1 s (ap1 num X) (ncNum X)) k S

          e_O : Deriv (eqF (ap2 sbt spec O) O)
          e_O = sbt_at_O spec

          -- moving leaves wrapped in functor nodes.
          e_pProg : Deriv (eqF (ap2 sbt spec (cAp1f pF prog)) (cAp1f pF prog'))
          e_pProg = sbt_step_ap1 k S pF prog prog' eProg

          e_predFuel : Deriv (eqF (ap2 sbt spec (cAp1f predF fuel))
                                   (cAp1f predF fuel'))
          e_predFuel = sbt_step_ap1 k S predF fuel fuel' eFuel

          -- szLeq atomic.
          e_szLHS : Deriv (eqF (ap2 sbt spec (cAp1f szF prog)) (cAp1f szF prog'))
          e_szLHS = sbt_step_ap1 k S szF prog prog' eProg

          e_szAtom : Deriv (eqF (ap2 sbf spec (szAtom prog)) (szAtom prog'))
          e_szAtom =
            sbf_step_atomic k S (cAp1f szF prog) (cAp1f s O)
              (cAp1f szF prog') (cAp1f s O) e_szLHS e_sO

          -- conjunct 1.
          e_c1LHS :
            Deriv (eqF (ap2 sbt spec (cAp2f eF (cAp1f pF prog) fuel))
                        (cAp2f eF (cAp1f pF prog') fuel'))
          e_c1LHS =
            sbt_step_ap2 k S eF (cAp1f pF prog) fuel (cAp1f pF prog') fuel'
              e_pProg eFuel

          e_conj1 : Deriv (eqF (ap2 sbf spec (conj1c prog fuel))
                                (conj1c prog' fuel'))
          e_conj1 =
            sbf_step_atomic k S
              (cAp2f eF (cAp1f pF prog) fuel) (cAp1f s (ap1 num X))
              (cAp2f eF (cAp1f pF prog') fuel') (cAp1f s (ap1 num X))
              e_c1LHS e_sHole

          -- conjunct 2.
          e_c2LHS :
            Deriv (eqF (ap2 sbt spec (cAp2f eF (cAp1f pF prog) (cAp1f predF fuel)))
                        (cAp2f eF (cAp1f pF prog') (cAp1f predF fuel')))
          e_c2LHS =
            sbt_step_ap2 k S eF (cAp1f pF prog) (cAp1f predF fuel)
              (cAp1f pF prog') (cAp1f predF fuel') e_pProg e_predFuel

          e_conj2 : Deriv (eqF (ap2 sbf spec (conj2c prog fuel))
                                (conj2c prog' fuel'))
          e_conj2 =
            sbf_step_atomic k S
              (cAp2f eF (cAp1f pF prog) (cAp1f predF fuel)) O
              (cAp2f eF (cAp1f pF prog') (cAp1f predF fuel')) O
              e_c2LHS e_O

          -- definable = cAnd conj1 conj2 = cNeg (cImp conj1 (cNeg conj2)).
          e_negc2 : Deriv (eqF (ap2 sbf spec (cNeg (conj2c prog fuel)))
                                (cNeg (conj2c prog' fuel')))
          e_negc2 = sbf_step_neg k S (conj2c prog fuel) (conj2c prog' fuel') e_conj2

          e_impD :
            Deriv (eqF (ap2 sbf spec (cImp (conj1c prog fuel) (cNeg (conj2c prog fuel))))
                        (cImp (conj1c prog' fuel') (cNeg (conj2c prog' fuel'))))
          e_impD =
            sbf_step_imp k S (conj1c prog fuel) (cNeg (conj2c prog fuel))
              (conj1c prog' fuel') (cNeg (conj2c prog' fuel')) e_conj1 e_negc2

          e_D : Deriv (eqF (ap2 sbf spec (defc prog fuel)) (defc prog' fuel'))
          e_D =
            sbf_step_neg k S
              (cImp (conj1c prog fuel) (cNeg (conj2c prog fuel)))
              (cImp (conj1c prog' fuel') (cNeg (conj2c prog' fuel'))) e_impD

          e_negD : Deriv (eqF (ap2 sbf spec (cNeg (defc prog fuel)))
                                (cNeg (defc prog' fuel')))
          e_negD = sbf_step_neg k S (defc prog fuel) (defc prog' fuel') e_D
      in sbf_step_imp k S (szAtom prog) (cNeg (defc prog fuel))
           (szAtom prog') (cNeg (defc prog' fuel')) e_szAtom e_negD

    ----------------------------------------------------------------
    -- The two substituents and specs.

    S0 : Term
    S0 = ap1 num P
    S1 : Term
    S1 = ap1 num N
    spec0 : Term
    spec0 = ap2 Pair (natCode zero) S0
    spec1 : Term
    spec1 = ap2 Pair (natCode (suc zero)) S1

    KcodeOpen : Term
    KcodeOpen = KcodeT (cVarc zero) (cVarc (suc zero))
    KcodeMid : Term
    KcodeMid = KcodeT (cVarc zero) (ap1 num N)
    KcodeClosed : Term
    KcodeClosed = KcodeT (ap1 num P) (ap1 num N)

    ----------------------------------------------------------------
    -- Inner pass (spec1, var 1 := num N): var 0 stays (nomatch), var 1 -> num N.

    innerEq : Deriv (eqF (ap2 sbf spec1 KcodeOpen) KcodeMid)
    innerEq =
      passEq (suc zero) S1 (cVarc zero) (cVarc zero) (cVarc (suc zero)) (ap1 num N)
        (sbt_at_var_nomatch (suc zero) zero S1 refl)
        (sbt_at_var_match (suc zero) S1)

    -- Outer pass (spec0, var 0 := num P): var 0 -> num P, num N inert.
    outerEq : Deriv (eqF (ap2 sbf spec0 KcodeMid) KcodeClosed)
    outerEq =
      passEq zero S0 (cVarc zero) (ap1 num P) (ap1 num N) (ap1 num N)
        (sbt_at_var_match zero S0)
        (sbt_num_inert zero S0 N)

    substBoth : Deriv (eqF (ap2 sbf spec0 (ap2 sbf spec1 KcodeOpen)) KcodeClosed)
    substBoth = ruleTrans (congR sbf spec0 innerEq) outerEq

    ----------------------------------------------------------------
    -- The two encoded substitutions (thmT_at_sb twice).

    innerWrap : Term
    innerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec1 w0)
    outerWrap : Term
    outerWrap = ap2 pi (natCode tag_sb) (ap2 pi spec0 innerWrap)

    dInner : Deriv (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 (ap1 thmT w0)))
    dInner = thmT_at_sb spec1 w0

    dInner2 : Deriv (eqF (ap1 thmT innerWrap) (ap2 sbf spec1 KcodeOpen))
    dInner2 = ruleTrans dInner (congR sbf spec1 dNeg)

    dOuter : Deriv (eqF (ap1 thmT outerWrap) (ap2 sbf spec0 (ap1 thmT innerWrap)))
    dOuter = thmT_at_sb spec0 innerWrap

    dOuter2 : Deriv (eqF (ap1 thmT outerWrap)
                          (ap2 sbf spec0 (ap2 sbf spec1 KcodeOpen)))
    dOuter2 = ruleTrans dOuter (congR sbf spec0 dInner2)

    dInst : Deriv (eqF (ap1 thmT outerWrap) KcodeClosed)
    dInst = ruleTrans dOuter2 substBoth

    ----------------------------------------------------------------
    -- The clash.

    Dclosed : Term
    Dclosed = defc (ap1 num P) (ap1 num N)

    -- KcodeClosed = cImp (szAtom (num P)) (cNeg Dclosed); strip with the size fact.
    dNegFinal : Deriv (eqF (ap1 thmT (cmp outerWrap cSize)) (cNeg Dclosed))
    dNegFinal =
      encoded_mp outerWrap cSize (szAtom (ap1 num P)) (cNeg Dclosed) dInst dSize

    dExF : Deriv (eqF (ap1 thmT (exfProof Dclosed codeFalse))
                       (cImp Dclosed (cImp (cNeg Dclosed) codeFalse)))
    dExF = encoded_exfalso Dclosed codeFalse

    result :
      Deriv (eqF (ap1 thmT
                   (cmp (cmp (exfProof Dclosed codeFalse) cPos) (cmp outerWrap cSize)))
                  codeFalse)
    result =
      chaitin_G1_assembly Dclosed cPos (exfProof Dclosed codeFalse)
        (cmp outerWrap cSize) dPos dNegFinal dExF
