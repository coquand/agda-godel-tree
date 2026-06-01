{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CgFunFun1 -- the genuine  Fun1 G  diagonal of Chaitin-Goedel-I.
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- BRA4.CgFun.cgFun : Term -> Term  is a META term-transformer.  This
-- file replaces it by a SINGLE genuine  Fun1 G  (a BRA program) with
--
--   gFact :  (w : Term) -> Deriv (eqF (ap1 G (closeW w)) (cgFun w))
--
-- i.e.  cgFun = ap1 G . closeW  as a PROVED object equality.  (Note:
-- it is NOT a meta  Eq  --  ap1 G (closeW w)  has head  ap1  while
-- cgFun w  has head  ap2 Pair , so the factorization is genuinely a
-- Deriv, witnessed by the combinatory-completeness evaluation, not a
-- definitional collapse.)  The clean CGI then reads
--
--   chaitinG1_Fun1_closed :  (closeW w = w) ->
--     Deriv (imp Rf (eqF (ap1 thmT w) (Kcode Lstar (outKdef Lstar w)))) ->
--     Deriv (imp Rf (eqF (ap1 thmT (ap1 G w)) codeFalse)) ,
--
-- a genuine  Fun1  diagonal, imp-arrow, no closedness bookkeeping.
--
-- =====================================================================
-- HOW  G  IS BUILT.
-- =====================================================================
--
--  cgFun w  is a fixed object-level combinator context  E[cw]  with
--  cw = closeW w  the only  w -dependence (BRA4.CgFun, lines 117-183).
--  Every node is an  ap1 / ap2  of an object  Fun1 / Fun2  ( gRec ,
--  sigma , pi , num , Pair , fuelMu_c , fuelG_c , outL_c , Df_runProg ,
--  runProg , s )  or a var-free constant ; the META term-builders
--  ( cmp , cImp , cNeg , cEqTm , cAp1f , cAp2f , exfProof  and its
--  axK / axNeg / axS / liftP / bComb chains)  are themselves pure
--  ap2 Pair -skeletons of their arguments.
--
--  So  E[-]  is a one-variable  Exp  (BRA4.AbsFun1) and
--    G = compile bodyExp ,    gFact w = compile_eq bodyExp (closeW w) ,
--  the generic combinatory-completeness evaluation.  We mirror  cgFun 's
--  let-chain node-for-node as  bodyExp  ;  denote bodyExp (closeW w)  is
--  DEFINITIONALLY  cgFun w  (same private constants, replicated below).

module BRA4.CgFunFun1 where

open import BRA4.Base
open import BRA4.AbsFun1
  using ( Exp ; evar ; econst ; eap1 ; eap2 ; denote ; compile ; compile_eq )
open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; NoVarAnd ; mkAnd ; NoVar_natCode )
open import BRA4.DoubleCodeNum
  using ( NoVar_codeFun1L ; NoVar_codeFun2L )
open import BRA4.NegAtomCode using ( NoVar_codeFormula )
open import BRA4.Code  using ( codeFalse ; codeFun1 ; codeFun2 ; codeFormula )
open import BRA4.Tags  using
  ( tag_sb ; tag_mp ; tag_imp ; tag_neg ; tag_eq ; tag_ap1 ; tag_ap2 ; tag_ax )
open import BRA4.ThmT  using ( thmT )
open import BRA4.Num   using ( num )
open import BRA4.Kdef  using ( runProg ; Kcode )
open import BRA4.KdefRecog using ( hitKdef ; hitKdef_le_one ; outKdef )
open import BRA4.KdefDiag   using ( predFlipDef ; gLcodeDef )
open import BRA4.KGodel1BridgeDef using ( Lstar )
open import BRA4.CloseW using ( closeW )
open import BRA4.StepU2Correct1New using ( correct1 ; correct2 )
open import BRA4.StepU2CorrectAPI using ( Correct1 ; Correct2 ; fuelF ; fuelG )
open import BRA4.ChaitinG1CoreNumRaw using ( gLnameDef ; cSizeProofDef )
open import BRA4.CgFun      using ( cgFun )
open import BRA4.CgFalseImp using ( cgFalseImp ; cgFalseImpAtVar2 )
open import BRA4.ProgEnc using ( enc ; encApp ; tagLeaf ; tagUnary ; tagBinary )

import BRA4.Thm12.All as ThmAll
import BRA4.FirstHit

open BRA4.FirstHit.Search
       (hitKdef Lstar (outKdef Lstar))
       (hitKdef_le_one Lstar (outKdef Lstar))
  using ( gRec )

open import BRA3.Church      using ( pi ; sigma ; sub )
open import BRA3.Fan         using ( Lift1 ; Lift2 ; Fan )
open import BRA3.PairAlgebra using ( Post )
open import BRA3.Contrapositive using ( compI )
open import BRA3.RuleInst2 using ( simSubstF )

------------------------------------------------------------------------
-- Local constants -- VERBATIM copy of BRA4.CgFun's private block, so the
-- composite Term  denote bodyExp (closeW w)  matches  cgFun w  by  refl .

private
  Df_runProg : Fun2
  Df_runProg = ThmAll.fst (ThmAll.thm12_Fun2 runProg)

  outL_c : Fun1
  outL_c = outKdef Lstar

  gFun_c : Fun1
  gFun_c = predFlipDef Lstar

  bF_c : Correct1 gFun_c
  bF_c = correct1 gFun_c

  fG_c : Fun1
  fG_c = fuelF bF_c

  fuelBase_c : Fun1
  fuelBase_c = C sigma fG_c (constN 1)

  sub_at_s_c : Fun2
  sub_at_s_c = Fan (Lift1 u) (Lift2 s) sub

  fuelStepH2_c : Fun2
  fuelStepH2_c = Fan (Post fG_c sub_at_s_c) (Lift1 (constN 1)) sigma

  fuelMu_c : Fun2
  fuelMu_c = R fuelBase_c sigma fuelStepH2_c

  bG_c : Correct2 (Lift1 outL_c)
  bG_c = correct2 (Lift1 outL_c)

  fuelG_c : Fun2
  fuelG_c = fuelG bG_c

------------------------------------------------------------------------
-- NoVar (enc t) :  the encoder produces a var-free right-spine of
--  ap2 pi (natCode tag) (...)  cells (BRA4.ProgEnc.encApp).

NoVar_encApp : (t rest : Term) -> NoVar rest -> NoVar (encApp t rest)
NoVar_encApp O          rest nr = mkAnd (NoVar_natCode tagLeaf) nr
NoVar_encApp (var k)    rest nr = mkAnd (NoVar_natCode tagLeaf) nr
NoVar_encApp (ap1 f t)  rest nr =
  mkAnd (NoVar_natCode tagUnary) (NoVar_encApp t rest nr)
NoVar_encApp (ap2 g a b) rest nr =
  mkAnd (NoVar_natCode tagBinary)
        (NoVar_encApp a (encApp b rest) (NoVar_encApp b rest nr))

NoVar_enc : (t : Term) -> NoVar (enc t)
NoVar_enc t = NoVar_encApp t O tt

------------------------------------------------------------------------
-- NoVar of the three named constants of  cgFun .

nvGL : NoVar gLnameDef
nvGL = NoVar_enc (gLcodeDef Lstar)

nvCF : NoVar codeFalse
nvCF = NoVar_codeFormula (atomic (eqn O (ap1 s O)))

nvCSP : NoVar cSizeProofDef
nvCSP = nvGL

------------------------------------------------------------------------
-- Exp smart constructors mirroring the meta term-builders.  Each
-- satisfies  denote (smart-cons ...) x = meta-builder ... (denote ... x)
-- DEFINITIONALLY (the meta-builders are pure  ap2 Pair / natCode
-- skeletons -- BRA4.ConInj , BRA4.DefWit , BRA4.CgiClash , BRA4.EncodedProp).

enat : Nat -> Exp
enat n = econst (natCode n) (NoVar_natCode n)

epair : Exp -> Exp -> Exp
epair a b = eap2 Pair a b

ecNeg : Exp -> Exp
ecNeg c = epair (enat tag_neg) c

ecImp : Exp -> Exp -> Exp
ecImp a b = epair (enat tag_imp) (epair a b)

ecmpE : Exp -> Exp -> Exp
ecmpE a b = epair (enat tag_mp) (epair a b)

ecEqTmE : Exp -> Exp -> Exp
ecEqTmE a b = epair (enat tag_eq) (epair a b)

ecAp1fE : Fun1 -> Exp -> Exp
ecAp1fE f t =
  epair (enat tag_ap1) (epair (econst (codeFun1 f) (NoVar_codeFun1L f)) t)

ecAp2fE : Fun2 -> Exp -> Exp -> Exp
ecAp2fE g a b =
  epair (enat tag_ap2)
        (epair (econst (codeFun2 g) (NoVar_codeFun2L g)) (epair a b))

eaxKProofE : Exp -> Exp -> Exp
eaxKProofE cA cB = epair (enat tag_ax) (epair (enat 11) (epair cA cB))

eaxNegProofE : Exp -> Exp -> Exp
eaxNegProofE cA cB = epair (enat tag_ax) (epair (enat 13) (epair cA cB))

eaxSProofE : Exp -> Exp -> Exp -> Exp
eaxSProofE cA cB cC =
  epair (enat tag_ax) (epair (enat 12) (epair cA (epair cB cC)))

eliftPProofE : Exp -> Exp -> Exp -> Exp                 -- cQ cRf pq
eliftPProofE cQ cRf pq = ecmpE (eaxKProofE cQ cRf) pq

ebCombProofE : Exp -> Exp -> Exp -> Exp -> Exp -> Exp   -- cP cQ cRf pd1 pd2
ebCombProofE cP cQ cRf pd1 pd2 =
  ecmpE (ecmpE (eaxSProofE cP cQ cRf) pd1) pd2

ebCombTwoProofE :                                       -- cP1 cP2 cQ cRf pd1 pd2
  Exp -> Exp -> Exp -> Exp -> Exp -> Exp -> Exp
ebCombTwoProofE cP1 cP2 cQ cRf pd1 pd2 =
  let cS2 = ecImp (ecImp cP2 (ecImp cQ cRf))
                  (ecImp (ecImp cP2 cQ) (ecImp cP2 cRf))
      tL  = eliftPProofE cS2 cP1 (eaxSProofE cP2 cQ cRf)
      tIn = ebCombProofE cP1 (ecImp cP2 (ecImp cQ cRf))
                             (ecImp (ecImp cP2 cQ) (ecImp cP2 cRf)) tL pd1
  in ebCombProofE cP1 (ecImp cP2 cQ) (ecImp cP2 cRf) tIn pd2

eexfProofE : Exp -> Exp -> Exp
eexfProofE cP cQ =
  let cQ_nqnp = ecImp (ecNeg cP) (ecImp (ecNeg cQ) (ecNeg cP))
      tNQNP   = eliftPProofE cQ_nqnp cP (eaxKProofE (ecNeg cP) (ecNeg cQ))
      cAN     = ecImp (ecImp (ecNeg cQ) (ecNeg cP)) (ecImp cP cQ)
      tL1     = eliftPProofE cAN (ecNeg cP) (eaxNegProofE cQ cP)
      tANL    = eliftPProofE (ecImp (ecNeg cP) cAN) cP tL1
      cQ'1    = ecImp (ecNeg cQ) (ecNeg cP)
      cRf'1   = ecImp cP cQ
      tPQ     = ebCombTwoProofE cP (ecNeg cP) cQ'1 cRf'1 tANL tNQNP
      tHP     = eaxKProofE cP (ecNeg cP)
  in ebCombTwoProofE cP (ecNeg cP) cP cQ tPQ tHP

------------------------------------------------------------------------
-- bodyExp -- a node-for-node transcription of  BRA4.CgFun.cgFun 's
-- let-chain.   evar  marks the single  w -dependence  cw = closeW w .

private
  esO : Exp                              -- the constant  ap1 s O
  esO = econst (ap1 s O) tt

  ekmax : Exp                            -- k_max = ap2 gRec O (ap1 s cw)
  ekmax = eap2 gRec (econst O tt) (eap1 s evar)

  ex' : Exp                              -- x' = ap1 outL_c k_max
  ex' = eap1 outL_c ekmax

  eseg2 : Exp                            -- ap2 sigma (s O) (ap2 fuelMu_c k_max k_max)
  eseg2 = eap2 sigma esO (eap2 fuelMu_c ekmax ekmax)

  efuelAB : Exp
  efuelAB = eap2 sigma esO eseg2

  efuelABC : Exp
  efuelABC = eap2 sigma efuelAB esO

  efuelD : Exp
  efuelD = eap2 sigma efuelABC esO

  efuelE : Exp
  efuelE = eap2 sigma efuelD esO

  efGouter : Exp                         -- ap2 fuelG_c k_max O
  efGouter = eap2 fuelG_c ekmax (econst O tt)

  efuelM : Exp
  efuelM = eap2 sigma efuelE efGouter

  enTerm : Exp                           -- fuelN
  enTerm = eap2 sigma efuelM esO

  eS0 : Exp                              -- ap1 num gLnameDef
  eS0 = eap1 num (econst gLnameDef nvGL)

  eS1 : Exp                              -- ap1 num nTerm
  eS1 = eap1 num enTerm

  espec0 : Exp                           -- ap2 Pair (natCode 0) S0
  espec0 = eap2 Pair (enat zero) eS0

  espec1 : Exp                           -- ap2 Pair (natCode 1) S1
  espec1 = eap2 Pair (enat (suc zero)) eS1

  einnerWrap : Exp                       -- ap2 pi tag_sb (ap2 pi spec1 k_max)
  einnerWrap = eap2 pi (enat tag_sb) (eap2 pi espec1 ekmax)

  eouterWrap : Exp                       -- ap2 pi tag_sb (ap2 pi spec0 innerWrap)
  eouterWrap = eap2 pi (enat tag_sb) (eap2 pi espec0 einnerWrap)

  ecPos : Exp                            -- ap2 Df_runProg gLnameDef nTerm
  ecPos = eap2 Df_runProg (econst gLnameDef nvGL) enTerm

  eD_eq : Exp                            -- cEqTm (cAp2f runProg S0 S1) (cAp1f s (num x'))
  eD_eq = ecEqTmE (ecAp2fE runProg eS0 eS1)
                  (ecAp1fE s (eap1 num ex'))

  bodyExp : Exp
  bodyExp =
    ecmpE (ecmpE (eexfProofE eD_eq (econst codeFalse nvCF)) ecPos)
          (ecmpE eouterWrap (econst cSizeProofDef nvCSP))

------------------------------------------------------------------------
-- The genuine  Fun1  diagonal  G  and its factorization fact.

G : Fun1
G = compile bodyExp

gFact : (w : Term) -> Deriv (eqF (ap1 G (closeW w)) (cgFun w))
gFact w = compile_eq bodyExp (closeW w)

------------------------------------------------------------------------
-- The imp + Fun1 restatement, general  w .

chaitinG1_Fun1 :
  (Rf : Formula) (w : Term) ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (eqF (ap1 thmT (closeW w))
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w))))) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap1 G (closeW w))) codeFalse))
chaitinG1_Fun1 Rf w sub0_Rf sub1_Rf sim_Rf hyp =
  let base : Deriv (imp Rf (eqF (ap1 thmT (cgFun w)) codeFalse))
      base = cgFalseImp Rf w sub0_Rf sub1_Rf sim_Rf hyp

      A : Term
      A = ap1 thmT (ap1 G (closeW w))

      B : Term
      B = ap1 thmT (cgFun w)

      -- thmT respects  ap1 G (closeW w) = cgFun w , so  thmT B = thmT A
      -- ( B = thmT (cgFun w) , A = thmT (ap1 G (closeW w)) ) :
      congThmBA : Deriv (eqF B A)
      congThmBA = cong1 thmT (ruleSym (gFact w))

      -- re-index the conclusion's subject from  cgFun w  to  ap1 G (closeW w) :
      --   ax_eqTrans B A codeFalse : (B = A) -> (B = codeFalse) -> (A = codeFalse) .
      reIdx : Deriv (imp (eqF B codeFalse) (eqF A codeFalse))
      reIdx = mp (ax_eqTrans B A codeFalse) congThmBA
  in compI base reIdx

------------------------------------------------------------------------
-- The clean corollary on witnesses closed at vars 0/1  ( closeW w = w ) .
-- EXACTLY the user's target -- a genuine  Fun1 G , imp-arrow, no closeW.

chaitinG1_Fun1_closed :
  (Rf : Formula) (w : Term) ->
  Eq (closeW w) w ->
  ((a : Term) -> Eq (substF zero a Rf) Rf) ->
  ((a : Term) -> Eq (substF (suc zero) a Rf) Rf) ->
  ((a b : Term) -> Eq (simSubstF zero a (suc zero) b Rf) Rf) ->
  Deriv (imp Rf (eqF (ap1 thmT w)
                      (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))) ->
  Deriv (imp Rf (eqF (ap1 thmT (ap1 G w)) codeFalse))
chaitinG1_Fun1_closed Rf w cwEq sub0_Rf sub1_Rf sim_Rf hyp =
  let hyp' : Deriv (imp Rf (eqF (ap1 thmT (closeW w))
                                 (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) (closeW w)))))
      hyp' = eqSubst (\ t -> Deriv (imp Rf (eqF (ap1 thmT t)
                                                 (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) t)))))
                     (eqSym cwEq) hyp

      core : Deriv (imp Rf (eqF (ap1 thmT (ap1 G (closeW w))) codeFalse))
      core = chaitinG1_Fun1 Rf w sub0_Rf sub1_Rf sim_Rf hyp'
  in eqSubst (\ t -> Deriv (imp Rf (eqF (ap1 thmT (ap1 G t)) codeFalse)))
             cwEq core

------------------------------------------------------------------------
-- THE HEADLINE :  the internal Chaitin-Goedel-I implication, for ANY  w ,
-- with the genuine  Fun1 G  and NO closedness hypothesis whatsoever.
--
--   chaitinG1_Fun1_all :
--     (w : Term) ->
--     Deriv (imp (eqF (ap1 thmT w) (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))
--                 (eqF (ap1 thmT (ap1 G w)) codeFalse))
--
-- WHY no closedness is needed (the point of replacing the meta  cgFun  by
-- the genuine  Fun1 G ):   prove the implication ONCE at the FRESH witness
--  var 2  ( BRA4.CgFalseImp.cgFalseImpAtVar2 ).   There  closeW (var 2) =
--  var 2  definitionally, so  cgFun (var 2) = ap1 G (var 2)  ( = gFact at
--  var 2 ), and the subject is literally the program  G  applied to  var 2 .
-- Then  ruleInst (var 2 := w)  substitutes throughout :   because  var 2  is
-- the SOLE occurrence and  ap1 G  is mere data,
--    substT 2 w (ap1 G (var 2)) = ap1 G (substT 2 w (var 2)) = ap1 G w ,
-- cleanly -- giving  imp X(w) (eqF (thmT (ap1 G w)) codeFalse)  for ANY  w .
-- This commuting is EXACTLY what failed for the meta  cgFun  ( substituting
--  var 2 -> w  into  cgFun (var 2)  does NOT yield  cgFun w , since  cgFun w
-- embeds  closeW w  in its  k_max  slot) -- which is why  closeW / closedness
-- was unavoidable before.   With a real  Fun1 , it is unavoidable no longer.

chaitinG1_Fun1_all :
  (w : Term) ->
  Deriv (imp (eqF (ap1 thmT w)
                   (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) w)))
              (eqF (ap1 thmT (ap1 G w)) codeFalse))
chaitinG1_Fun1_all w =
  let v2 : Term
      v2 = var (suc (suc zero))

      -- closeW (var 2) = var 2 (defeq), so  gFact (var 2)  is exactly
      --   Deriv (eqF (ap1 G (var 2)) (cgFun (var 2))) .
      gFactV2 : Deriv (eqF (ap1 G v2) (cgFun v2))
      gFactV2 = gFact v2

      B2 : Term
      B2 = ap1 thmT (cgFun v2)

      A2 : Term
      A2 = ap1 thmT (ap1 G v2)

      congB2A2 : Deriv (eqF B2 A2)
      congB2A2 = cong1 thmT (ruleSym gFactV2)

      reIdx2 : Deriv (imp (eqF B2 codeFalse) (eqF A2 codeFalse))
      reIdx2 = mp (ax_eqTrans B2 A2 codeFalse) congB2A2

      -- the implication at the fresh witness  var 2 , subject  ap1 G (var 2) :
      impV2 : Deriv (imp (eqF (ap1 thmT v2)
                              (ap1 (Kcode Lstar) (ap1 (outKdef Lstar) v2)))
                          (eqF (ap1 thmT (ap1 G v2)) codeFalse))
      impV2 = compI cgFalseImpAtVar2 reIdx2

  in ruleInst (suc (suc zero)) w impV2
