{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.EncodedProp -- the code-agnostic ax-branch necessitations of the THREE
-- primitive propositional axioms  axK (idx 11) / axS (idx 12) / axNeg (idx 13) ,
-- the propositional analogues of the shipped equational  encodedAxEqCong* .
-- This is the ONE shared deliverable of CHAITIN-G1-PLAN.md Phase 1: from these,
--  encoded_mp  composition yields BOTH  encoded_and  and  encoded_exfalso  (an
--  mp -tree over these three; see chaitin-G1-blueprint.tex Sec 9).
--
-- Each is built by consuming the SHIPPED verifier closure  thmT_at_axN<k>
-- (BRA4.ThmTAtAx11/12/13) -- which gives  thmT (packAx k extra) = outputRHS extra
-- with the formula-code slots read as  Fst/Snd extra  -- and then reducing those
-- projections to the supplied codes via  axFst / axSnd  ( Pair = pi ).  No
-- codeFormula:  the codes  cA , cB , cC  are arbitrary  Term s.

module BRA4.EncodedProp where

open import BRA4.Base
open import BRA4.Tags  using ( tag_ax ; tag_imp ; tag_neg )
open import BRA4.ThmT  using ( thmT )
open import BRA4.DefWit using ( cImp ; cNeg ; cAnd )
open import BRA4.ThmTAtAx11 using ( thmT_at_axN11 )
open import BRA4.ThmTAtAx12 using ( thmT_at_axN12 )
open import BRA4.ThmTAtAx13 using ( thmT_at_axN13 )
open import BRA4.ConInj using ( cmp )
open import BRA4.Thm12.EncodedMp using ( encoded_mp )

------------------------------------------------------------------------
-- axK  (index 11) :  imp A (imp B A) .
--
-- proof code:  packAx 11 (Pair cA cB) = Pair tag_ax (Pair (natCode 11) (Pair cA cB)) .
-- (pack/packAx are private in BRA4.Encode; we spell the form thmT_at_axN11 reads.)

axKProof : Term -> Term -> Term
axKProof cA cB =
  ap2 Pair (natCode tag_ax) (ap2 Pair (natCode 11) (ap2 Pair cA cB))

encoded_axK :
  (cA cB : Term) ->
  Deriv (eqF (ap1 thmT (axKProof cA cB)) (cImp cA (cImp cB cA)))
encoded_axK cA cB =
  let P : Term
      P = ap2 Pair cA cB

      axF : Deriv (eqF (ap1 Fst P) cA)
      axF = axFst cA cB
      axS : Deriv (eqF (ap1 Snd P) cB)
      axS = axSnd cA cB

      -- rewrite  Pair (Snd P) (Fst P)  ->  Pair cB cA :
      inner_pair :
        Deriv (eqF (ap2 Pair (ap1 Snd P) (ap1 Fst P)) (ap2 Pair cB cA))
      inner_pair = ruleTrans (congL Pair (ap1 Fst P) axS) (congR Pair cB axF)

      -- ->  cImp cB cA :
      inner_cimp :
        Deriv (eqF (cImp (ap1 Snd P) (ap1 Fst P)) (cImp cB cA))
      inner_cimp = congR Pair (natCode tag_imp) inner_pair

      -- rewrite  Pair (Fst P) (cImp (Snd P) (Fst P))  ->  Pair cA (cImp cB cA) :
      outer_pair :
        Deriv (eqF (ap2 Pair (ap1 Fst P) (cImp (ap1 Snd P) (ap1 Fst P)))
                   (ap2 Pair cA (cImp cB cA)))
      outer_pair = ruleTrans (congL Pair (cImp (ap1 Snd P) (ap1 Fst P)) axF)
                             (congR Pair cA inner_cimp)

      -- ->  cImp cA (cImp cB cA) :
      cleanup :
        Deriv (eqF (cImp (ap1 Fst P) (cImp (ap1 Snd P) (ap1 Fst P)))
                   (cImp cA (cImp cB cA)))
      cleanup = congR Pair (natCode tag_imp) outer_pair
  in ruleTrans (thmT_at_axN11 P) cleanup

------------------------------------------------------------------------
-- axNeg  (index 13) :  imp (imp (neg A) (neg B)) (imp B A) .
--
-- outputRHS (Pair cA cB) = cImp (cImp (cNeg A) (cNeg B)) (cImp B A) ,
--   A = Fst (Pair cA cB) , B = Snd (Pair cA cB) .

axNegProof : Term -> Term -> Term
axNegProof cA cB =
  ap2 Pair (natCode tag_ax) (ap2 Pair (natCode 13) (ap2 Pair cA cB))

encoded_axNeg :
  (cA cB : Term) ->
  Deriv (eqF (ap1 thmT (axNegProof cA cB))
             (cImp (cImp (cNeg cA) (cNeg cB)) (cImp cB cA)))
encoded_axNeg cA cB =
  let P : Term
      P = ap2 Pair cA cB
      A' : Term
      A' = ap1 Fst P
      B' : Term
      B' = ap1 Snd P

      axF : Deriv (eqF A' cA)
      axF = axFst cA cB
      axS : Deriv (eqF B' cB)
      axS = axSnd cA cB

      -- antecedent  cImp (cNeg A') (cNeg B')  ->  cImp (cNeg cA) (cNeg cB) :
      negA : Deriv (eqF (cNeg A') (cNeg cA))
      negA = congR Pair (natCode tag_neg) axF
      negB : Deriv (eqF (cNeg B') (cNeg cB))
      negB = congR Pair (natCode tag_neg) axS
      pair_negs : Deriv (eqF (ap2 Pair (cNeg A') (cNeg B')) (ap2 Pair (cNeg cA) (cNeg cB)))
      pair_negs = ruleTrans (congL Pair (cNeg B') negA) (congR Pair (cNeg cA) negB)
      ant : Deriv (eqF (cImp (cNeg A') (cNeg B')) (cImp (cNeg cA) (cNeg cB)))
      ant = congR Pair (natCode tag_imp) pair_negs

      -- consequent  cImp B' A'  ->  cImp cB cA :
      pair_BA : Deriv (eqF (ap2 Pair B' A') (ap2 Pair cB cA))
      pair_BA = ruleTrans (congL Pair A' axS) (congR Pair cB axF)
      cons : Deriv (eqF (cImp B' A') (cImp cB cA))
      cons = congR Pair (natCode tag_imp) pair_BA

      -- outer  cImp ant cons :
      pair_outer :
        Deriv (eqF (ap2 Pair (cImp (cNeg A') (cNeg B')) (cImp B' A'))
                   (ap2 Pair (cImp (cNeg cA) (cNeg cB)) (cImp cB cA)))
      pair_outer = ruleTrans (congL Pair (cImp B' A') ant)
                             (congR Pair (cImp (cNeg cA) (cNeg cB)) cons)
      cleanup :
        Deriv (eqF (cImp (cImp (cNeg A') (cNeg B')) (cImp B' A'))
                   (cImp (cImp (cNeg cA) (cNeg cB)) (cImp cB cA)))
      cleanup = congR Pair (natCode tag_imp) pair_outer
  in ruleTrans (thmT_at_axN13 P) cleanup

------------------------------------------------------------------------
-- axS  (index 12) :  imp (imp A (imp B C)) (imp (imp A B) (imp A C)) .
--
-- outputRHS (Pair cA (Pair cB cC)) = the above coded, with
--   A = Fst P , B = Fst (Snd P) , C = Snd (Snd P) ,  P = Pair cA (Pair cB cC) .

axSProof : Term -> Term -> Term -> Term
axSProof cA cB cC =
  ap2 Pair (natCode tag_ax)
    (ap2 Pair (natCode 12) (ap2 Pair cA (ap2 Pair cB cC)))

encoded_axS :
  (cA cB cC : Term) ->
  Deriv (eqF (ap1 thmT (axSProof cA cB cC))
             (cImp (cImp cA (cImp cB cC)) (cImp (cImp cA cB) (cImp cA cC))))
encoded_axS cA cB cC =
  let P : Term
      P = ap2 Pair cA (ap2 Pair cB cC)
      A' : Term
      A' = ap1 Fst P
      B' : Term
      B' = ap1 Fst (ap1 Snd P)
      C' : Term
      C' = ap1 Snd (ap1 Snd P)

      axF : Deriv (eqF A' cA)
      axF = axFst cA (ap2 Pair cB cC)
      sndP : Deriv (eqF (ap1 Snd P) (ap2 Pair cB cC))
      sndP = axSnd cA (ap2 Pair cB cC)
      axB : Deriv (eqF B' cB)
      axB = ruleTrans (cong1 Fst sndP) (axFst cB cC)
      axC : Deriv (eqF C' cC)
      axC = ruleTrans (cong1 Snd sndP) (axSnd cB cC)

      -- cImp B' C' -> cImp cB cC
      cimp_BC : Deriv (eqF (cImp B' C') (cImp cB cC))
      cimp_BC = congR Pair (natCode tag_imp)
                  (ruleTrans (congL Pair C' axB) (congR Pair cB axC))
      -- ANTECEDENT  cImp A' (cImp B' C') -> cImp cA (cImp cB cC)
      cimp_Ant : Deriv (eqF (cImp A' (cImp B' C')) (cImp cA (cImp cB cC)))
      cimp_Ant = congR Pair (natCode tag_imp)
                   (ruleTrans (congL Pair (cImp B' C') axF) (congR Pair cA cimp_BC))

      -- cImp A' B' -> cImp cA cB ;  cImp A' C' -> cImp cA cC
      cimp_AB : Deriv (eqF (cImp A' B') (cImp cA cB))
      cimp_AB = congR Pair (natCode tag_imp)
                  (ruleTrans (congL Pair B' axF) (congR Pair cA axB))
      cimp_AC : Deriv (eqF (cImp A' C') (cImp cA cC))
      cimp_AC = congR Pair (natCode tag_imp)
                  (ruleTrans (congL Pair C' axF) (congR Pair cA axC))
      -- CONSEQUENT  cImp (cImp A' B') (cImp A' C') -> cImp (cImp cA cB) (cImp cA cC)
      cimp_Cons :
        Deriv (eqF (cImp (cImp A' B') (cImp A' C'))
                   (cImp (cImp cA cB) (cImp cA cC)))
      cimp_Cons = congR Pair (natCode tag_imp)
                    (ruleTrans (congL Pair (cImp A' C') cimp_AB)
                               (congR Pair (cImp cA cB) cimp_AC))

      -- outer
      cleanup :
        Deriv (eqF (cImp (cImp A' (cImp B' C')) (cImp (cImp A' B') (cImp A' C')))
                   (cImp (cImp cA (cImp cB cC)) (cImp (cImp cA cB) (cImp cA cC))))
      cleanup = congR Pair (natCode tag_imp)
                  (ruleTrans (congL Pair (cImp (cImp A' B') (cImp A' C')) cimp_Ant)
                             (congR Pair (cImp cA (cImp cB cC)) cimp_Cons))
  in ruleTrans (thmT_at_axN12 P) cleanup

------------------------------------------------------------------------
-- ENCODED COMBINATORS (the necessitations of liftP / bComb / bCombTwo,
-- which are themselves mp-trees over axK / axS).  These let us mirror the
-- derived  axExFalso  (and  andIntro )  line-by-line at the encoded level.

-- liftP Rf D = mp (axK Q Rf) D.
liftPProof : Term -> Term -> Term -> Term       -- cQ cRf pq
liftPProof cQ cRf pq = cmp (axKProof cQ cRf) pq

encoded_liftP :
  (cRf cQ pq : Term) ->
  Deriv (eqF (ap1 thmT pq) cQ) ->
  Deriv (eqF (ap1 thmT (liftPProof cQ cRf pq)) (cImp cRf cQ))
encoded_liftP cRf cQ pq d =
  encoded_mp (axKProof cQ cRf) pq cQ (cImp cRf cQ) (encoded_axK cQ cRf) d

-- bComb D1 D2 = mp (mp (axS P Q Rf) D1) D2 .
bCombProof : Term -> Term -> Term -> Term -> Term -> Term   -- cP cQ cRf pd1 pd2
bCombProof cP cQ cRf pd1 pd2 = cmp (cmp (axSProof cP cQ cRf) pd1) pd2

encoded_bComb :
  (cP cQ cRf pd1 pd2 : Term) ->
  Deriv (eqF (ap1 thmT pd1) (cImp cP (cImp cQ cRf))) ->
  Deriv (eqF (ap1 thmT pd2) (cImp cP cQ)) ->
  Deriv (eqF (ap1 thmT (bCombProof cP cQ cRf pd1 pd2)) (cImp cP cRf))
encoded_bComb cP cQ cRf pd1 pd2 e1 e2 =
  let inner : Deriv (eqF (ap1 thmT (cmp (axSProof cP cQ cRf) pd1))
                         (cImp (cImp cP cQ) (cImp cP cRf)))
      inner = encoded_mp (axSProof cP cQ cRf) pd1
                (cImp cP (cImp cQ cRf)) (cImp (cImp cP cQ) (cImp cP cRf))
                (encoded_axS cP cQ cRf) e1
  in encoded_mp (cmp (axSProof cP cQ cRf) pd1) pd2
       (cImp cP cQ) (cImp cP cRf) inner e2

-- bCombTwo D1 D2 = bComb (bComb (liftP P1 (axS P2 Q Rf)) D1) D2 .
bCombTwoProof : Term -> Term -> Term -> Term -> Term -> Term -> Term  -- cP1 cP2 cQ cRf pd1 pd2
bCombTwoProof cP1 cP2 cQ cRf pd1 pd2 =
  let cS2  = cImp (cImp cP2 (cImp cQ cRf)) (cImp (cImp cP2 cQ) (cImp cP2 cRf))
      tL   = liftPProof cS2 cP1 (axSProof cP2 cQ cRf)
      tIn  = bCombProof cP1 (cImp cP2 (cImp cQ cRf))
                            (cImp (cImp cP2 cQ) (cImp cP2 cRf)) tL pd1
  in bCombProof cP1 (cImp cP2 cQ) (cImp cP2 cRf) tIn pd2

encoded_bCombTwo :
  (cP1 cP2 cQ cRf pd1 pd2 : Term) ->
  Deriv (eqF (ap1 thmT pd1) (cImp cP1 (cImp cP2 (cImp cQ cRf)))) ->
  Deriv (eqF (ap1 thmT pd2) (cImp cP1 (cImp cP2 cQ))) ->
  Deriv (eqF (ap1 thmT (bCombTwoProof cP1 cP2 cQ cRf pd1 pd2))
             (cImp cP1 (cImp cP2 cRf)))
encoded_bCombTwo cP1 cP2 cQ cRf pd1 pd2 e1 e2 =
  let cS2 : Term
      cS2 = cImp (cImp cP2 (cImp cQ cRf)) (cImp (cImp cP2 cQ) (cImp cP2 cRf))
      tL : Term
      tL = liftPProof cS2 cP1 (axSProof cP2 cQ cRf)
      e_liftS : Deriv (eqF (ap1 thmT tL) (cImp cP1 cS2))
      e_liftS = encoded_liftP cP1 cS2 (axSProof cP2 cQ cRf) (encoded_axS cP2 cQ cRf)
      e_inner :
        Deriv (eqF (ap1 thmT (bCombProof cP1 (cImp cP2 (cImp cQ cRf))
                                             (cImp (cImp cP2 cQ) (cImp cP2 cRf)) tL pd1))
                   (cImp cP1 (cImp (cImp cP2 cQ) (cImp cP2 cRf))))
      e_inner = encoded_bComb cP1 (cImp cP2 (cImp cQ cRf))
                  (cImp (cImp cP2 cQ) (cImp cP2 cRf)) tL pd1 e_liftS e1
  in encoded_bComb cP1 (cImp cP2 cQ) (cImp cP2 cRf)
       (bCombProof cP1 (cImp cP2 (cImp cQ cRf))
                       (cImp (cImp cP2 cQ) (cImp cP2 cRf)) tL pd1)
       pd2 e_inner e2

------------------------------------------------------------------------
-- encoded_exfalso :  thmT (exfProof cP cQ) = cImp cP (cImp (cNeg cP) cQ) ,
-- the code-agnostic necessitation of  axExFalso P Q : imp P (imp (neg P) Q) .
-- Mirrors BRA3.Contrapositive.axExFalso line-by-line (liftP / bCombTwo over
-- axK / axNeg).  Feeding  cP = atomCompOf z0 , cQ = codeFalse  lands exactly
-- the  dExF  leg of BRA4.ChaitinG1.

exfProof : Term -> Term -> Term
exfProof cP cQ =
  let cQ_nqnp = cImp (cNeg cP) (cImp (cNeg cQ) (cNeg cP))
      tNQNP   = liftPProof cQ_nqnp cP (axKProof (cNeg cP) (cNeg cQ))
      cAN     = cImp (cImp (cNeg cQ) (cNeg cP)) (cImp cP cQ)
      tL1     = liftPProof cAN (cNeg cP) (axNegProof cQ cP)
      tANL    = liftPProof (cImp (cNeg cP) cAN) cP tL1
      cQ'1    = cImp (cNeg cQ) (cNeg cP)
      cRf'1   = cImp cP cQ
      tPQ     = bCombTwoProof cP (cNeg cP) cQ'1 cRf'1 tANL tNQNP
      tHP     = axKProof cP (cNeg cP)
  in bCombTwoProof cP (cNeg cP) cP cQ tPQ tHP

encoded_exfalso :
  (cP cQ : Term) ->
  Deriv (eqF (ap1 thmT (exfProof cP cQ)) (cImp cP (cImp (cNeg cP) cQ)))
encoded_exfalso cP cQ =
  let cQ_nqnp : Term
      cQ_nqnp = cImp (cNeg cP) (cImp (cNeg cQ) (cNeg cP))
      tNQNP : Term
      tNQNP = liftPProof cQ_nqnp cP (axKProof (cNeg cP) (cNeg cQ))
      e_nqnp : Deriv (eqF (ap1 thmT tNQNP) (cImp cP cQ_nqnp))
      e_nqnp = encoded_liftP cP cQ_nqnp (axKProof (cNeg cP) (cNeg cQ))
                 (encoded_axK (cNeg cP) (cNeg cQ))

      cAN : Term
      cAN = cImp (cImp (cNeg cQ) (cNeg cP)) (cImp cP cQ)
      tL1 : Term
      tL1 = liftPProof cAN (cNeg cP) (axNegProof cQ cP)
      e_L1 : Deriv (eqF (ap1 thmT tL1) (cImp (cNeg cP) cAN))
      e_L1 = encoded_liftP (cNeg cP) cAN (axNegProof cQ cP) (encoded_axNeg cQ cP)
      tANL : Term
      tANL = liftPProof (cImp (cNeg cP) cAN) cP tL1
      e_anl : Deriv (eqF (ap1 thmT tANL) (cImp cP (cImp (cNeg cP) cAN)))
      e_anl = encoded_liftP cP (cImp (cNeg cP) cAN) tL1 e_L1

      cQ'1 : Term
      cQ'1 = cImp (cNeg cQ) (cNeg cP)
      cRf'1 : Term
      cRf'1 = cImp cP cQ
      tPQ : Term
      tPQ = bCombTwoProof cP (cNeg cP) cQ'1 cRf'1 tANL tNQNP
      e_pq : Deriv (eqF (ap1 thmT tPQ) (cImp cP (cImp (cNeg cP) (cImp cP cQ))))
      e_pq = encoded_bCombTwo cP (cNeg cP) cQ'1 cRf'1 tANL tNQNP e_anl e_nqnp

      tHP : Term
      tHP = axKProof cP (cNeg cP)
      e_hp : Deriv (eqF (ap1 thmT tHP) (cImp cP (cImp (cNeg cP) cP)))
      e_hp = encoded_axK cP (cNeg cP)
  in encoded_bCombTwo cP (cNeg cP) cP cQ tPQ tHP e_pq e_hp

------------------------------------------------------------------------
-- TOWARDS encoded_and (the dPos leg).  We mirror CompressCanonical.andIntro,
-- which is an mp-tree over axK/axS/axNeg via identP / Q_to_dNeg(DNI) /
-- axContrapos (themselves over DNE).  Same encoded* pattern as encoded_exfalso,
-- just a longer chain.  Start: encoded_identP.

-- identP P = mp (mp (axS P (imp P P) P) (axK P (imp P P))) (axK P P) : imp P P.
identPProof : Term -> Term
identPProof cP =
  cmp (cmp (axSProof cP (cImp cP cP) cP) (axKProof cP (cImp cP cP))) (axKProof cP cP)

encoded_identP :
  (cP : Term) ->
  Deriv (eqF (ap1 thmT (identPProof cP)) (cImp cP cP))
encoded_identP cP =
  let e1 : Deriv (eqF (ap1 thmT (axSProof cP (cImp cP cP) cP))
                      (cImp (cImp cP (cImp (cImp cP cP) cP))
                            (cImp (cImp cP (cImp cP cP)) (cImp cP cP))))
      e1 = encoded_axS cP (cImp cP cP) cP
      e2 : Deriv (eqF (ap1 thmT (axKProof cP (cImp cP cP)))
                      (cImp cP (cImp (cImp cP cP) cP)))
      e2 = encoded_axK cP (cImp cP cP)
      m1 : Deriv (eqF (ap1 thmT (cmp (axSProof cP (cImp cP cP) cP)
                                     (axKProof cP (cImp cP cP))))
                      (cImp (cImp cP (cImp cP cP)) (cImp cP cP)))
      m1 = encoded_mp (axSProof cP (cImp cP cP) cP) (axKProof cP (cImp cP cP))
             (cImp cP (cImp (cImp cP cP) cP))
             (cImp (cImp cP (cImp cP cP)) (cImp cP cP)) e1 e2
      e3 : Deriv (eqF (ap1 thmT (axKProof cP cP)) (cImp cP (cImp cP cP)))
      e3 = encoded_axK cP cP
  in encoded_mp (cmp (axSProof cP (cImp cP cP) cP) (axKProof cP (cImp cP cP)))
       (axKProof cP cP) (cImp cP (cImp cP cP)) (cImp cP cP) m1 e3

------------------------------------------------------------------------
-- encoded_DNE :  thmT (dneProof cA) = cImp cH cA  (cH = cNeg (cNeg cA)),
-- the necessitation of  DNE A : imp (neg (neg A)) A .  Mirrors the 20-step
-- mp-tree of BRA3.Contrapositive.DNE over axK/axS/axNeg.

dneProof : Term -> Term
dneProof cA =
  let cU = cNeg cA
      cH = cNeg cU
      cV = cNeg cH
      cW = cNeg cV
      cS1 = cImp (cImp cW cH) (cImp cU cV)
      cS8 = cImp (cImp cU cV) (cImp cH cA)
      p1  = axNegProof cV cU
      p2  = axKProof cS1 cH
      p3  = cmp p2 p1
      p4  = axSProof cH (cImp cW cH) (cImp cU cV)
      p5  = cmp p4 p3
      p6  = axKProof cH cW
      p7  = cmp p5 p6
      p8  = axNegProof cA cH
      p9  = axKProof cS8 cH
      p10 = cmp p9 p8
      p11 = axSProof cH (cImp cU cV) (cImp cH cA)
      p12 = cmp p11 p10
      p13 = cmp p12 p7
      p14 = axKProof cH (cImp cH cH)
      p15 = axKProof cH cH
      p16 = axSProof cH (cImp cH cH) cH
      p17 = cmp p16 p14
      p18 = cmp p17 p15
      p19 = axSProof cH cH cA
      p20 = cmp p19 p13
  in cmp p20 p18

encoded_DNE :
  (cA : Term) ->
  Deriv (eqF (ap1 thmT (dneProof cA)) (cImp (cNeg (cNeg cA)) cA))
encoded_DNE cA =
  let cU = cNeg cA
      cH = cNeg cU
      cV = cNeg cH
      cW = cNeg cV
      cS1 = cImp (cImp cW cH) (cImp cU cV)
      cS8 = cImp (cImp cU cV) (cImp cH cA)
      p1  = axNegProof cV cU
      p2  = axKProof cS1 cH
      p3  = cmp p2 p1
      p4  = axSProof cH (cImp cW cH) (cImp cU cV)
      p5  = cmp p4 p3
      p6  = axKProof cH cW
      p7  = cmp p5 p6
      p8  = axNegProof cA cH
      p9  = axKProof cS8 cH
      p10 = cmp p9 p8
      p11 = axSProof cH (cImp cU cV) (cImp cH cA)
      p12 = cmp p11 p10
      p13 = cmp p12 p7
      p14 = axKProof cH (cImp cH cH)
      p15 = axKProof cH cH
      p16 = axSProof cH (cImp cH cH) cH
      p17 = cmp p16 p14
      p18 = cmp p17 p15
      p19 = axSProof cH cH cA
      p20 = cmp p19 p13

      e1  = encoded_axNeg cV cU
      e2  = encoded_axK cS1 cH
      e3  = encoded_mp p2 p1 cS1 (cImp cH cS1) e2 e1
      e4  = encoded_axS cH (cImp cW cH) (cImp cU cV)
      e5  = encoded_mp p4 p3 (cImp cH cS1)
              (cImp (cImp cH (cImp cW cH)) (cImp cH (cImp cU cV))) e4 e3
      e6  = encoded_axK cH cW
      e7  = encoded_mp p5 p6 (cImp cH (cImp cW cH)) (cImp cH (cImp cU cV)) e5 e6
      e8  = encoded_axNeg cA cH
      e9  = encoded_axK cS8 cH
      e10 = encoded_mp p9 p8 cS8 (cImp cH cS8) e9 e8
      e11 = encoded_axS cH (cImp cU cV) (cImp cH cA)
      e12 = encoded_mp p11 p10 (cImp cH cS8)
              (cImp (cImp cH (cImp cU cV)) (cImp cH (cImp cH cA))) e11 e10
      e13 = encoded_mp p12 p7 (cImp cH (cImp cU cV)) (cImp cH (cImp cH cA)) e12 e7
      e14 = encoded_axK cH (cImp cH cH)
      e15 = encoded_axK cH cH
      e16 = encoded_axS cH (cImp cH cH) cH
      e17 = encoded_mp p16 p14 (cImp cH (cImp (cImp cH cH) cH))
              (cImp (cImp cH (cImp cH cH)) (cImp cH cH)) e16 e14
      e18 = encoded_mp p17 p15 (cImp cH (cImp cH cH)) (cImp cH cH) e17 e15
      e19 = encoded_axS cH cH cA
      e20 = encoded_mp p19 p13 (cImp cH (cImp cH cA))
              (cImp (cImp cH cH) (cImp cH cA)) e19 e13
  in encoded_mp p20 p18 (cImp cH cH) (cImp cH cA) e20 e18

------------------------------------------------------------------------
-- encoded_Q_to_dNeg :  thmT (qToDNegProof cQ) = cImp cQ (cNeg (cNeg cQ)) .
-- Q_to_dNeg Q = mp (axNeg (neg (neg Q)) Q) (DNE (neg Q)) .

qToDNegProof : Term -> Term
qToDNegProof cQ = cmp (axNegProof (cNeg (cNeg cQ)) cQ) (dneProof (cNeg cQ))

encoded_Q_to_dNeg :
  (cQ : Term) ->
  Deriv (eqF (ap1 thmT (qToDNegProof cQ)) (cImp cQ (cNeg (cNeg cQ))))
encoded_Q_to_dNeg cQ =
  encoded_mp (axNegProof (cNeg (cNeg cQ)) cQ) (dneProof (cNeg cQ))
    (cImp (cNeg (cNeg (cNeg cQ))) (cNeg cQ)) (cImp cQ (cNeg (cNeg cQ)))
    (encoded_axNeg (cNeg (cNeg cQ)) cQ) (encoded_DNE (cNeg cQ))

------------------------------------------------------------------------
-- encoded_dNeg_lift :  thmT (dNegLiftProof cP cQ)
--   = cImp (cImp cP cQ) (cImp (cNeg (cNeg cP)) (cNeg (cNeg cQ))) .
-- Mirrors dNeg_lift P Q (liftP/bCombTwo/axK over DNE/identP/Q_to_dNeg).

dNegLiftProof : Term -> Term -> Term
dNegLiftProof cP cQ =
  let cH = cImp cP cQ
      cNNP = cNeg (cNeg cP)
      cNNQ = cNeg (cNeg cQ)
      t_in1 = liftPProof (cImp cNNP cP) cNNP (dneProof cP)
      t_D1  = liftPProof (cImp cNNP (cImp cNNP cP)) cH t_in1
      t_D2  = liftPProof (cImp cNNP cNNP) cH (identPProof cNNP)
      t_Pav = bCombTwoProof cH cNNP cNNP cP t_D1 t_D2
      t_Hav = axKProof cH cNNP
      t_Qav = bCombTwoProof cH cNNP cP cQ t_Hav t_Pav
      t_in2 = liftPProof (cImp cQ cNNQ) cNNP (qToDNegProof cQ)
      t_Qto = liftPProof (cImp cNNP (cImp cQ cNNQ)) cH t_in2
  in bCombTwoProof cH cNNP cQ cNNQ t_Qto t_Qav

encoded_dNeg_lift :
  (cP cQ : Term) ->
  Deriv (eqF (ap1 thmT (dNegLiftProof cP cQ))
             (cImp (cImp cP cQ) (cImp (cNeg (cNeg cP)) (cNeg (cNeg cQ)))))
encoded_dNeg_lift cP cQ =
  let cH = cImp cP cQ
      cNNP = cNeg (cNeg cP)
      cNNQ = cNeg (cNeg cQ)
      t_in1 = liftPProof (cImp cNNP cP) cNNP (dneProof cP)
      e_in1 = encoded_liftP cNNP (cImp cNNP cP) (dneProof cP) (encoded_DNE cP)
      t_D1  = liftPProof (cImp cNNP (cImp cNNP cP)) cH t_in1
      e_D1  = encoded_liftP cH (cImp cNNP (cImp cNNP cP)) t_in1 e_in1
      t_D2  = liftPProof (cImp cNNP cNNP) cH (identPProof cNNP)
      e_D2  = encoded_liftP cH (cImp cNNP cNNP) (identPProof cNNP) (encoded_identP cNNP)
      t_Pav = bCombTwoProof cH cNNP cNNP cP t_D1 t_D2
      e_Pav = encoded_bCombTwo cH cNNP cNNP cP t_D1 t_D2 e_D1 e_D2
      t_Hav = axKProof cH cNNP
      e_Hav = encoded_axK cH cNNP
      t_Qav = bCombTwoProof cH cNNP cP cQ t_Hav t_Pav
      e_Qav = encoded_bCombTwo cH cNNP cP cQ t_Hav t_Pav e_Hav e_Pav
      t_in2 = liftPProof (cImp cQ cNNQ) cNNP (qToDNegProof cQ)
      e_in2 = encoded_liftP cNNP (cImp cQ cNNQ) (qToDNegProof cQ) (encoded_Q_to_dNeg cQ)
      t_Qto = liftPProof (cImp cNNP (cImp cQ cNNQ)) cH t_in2
      e_Qto = encoded_liftP cH (cImp cNNP (cImp cQ cNNQ)) t_in2 e_in2
  in encoded_bCombTwo cH cNNP cQ cNNQ t_Qto t_Qav e_Qto e_Qav

------------------------------------------------------------------------
-- encoded_axContrapos :  thmT (axContraposProof cP cQ)
--   = cImp (cImp cP cQ) (cImp (cNeg cQ) (cNeg cP)) .
-- axContrapos P Q = compI (dNeg_lift P Q) (axNeg (neg P) (neg Q))
--                 = bComb (liftP X (axNeg ..)) (dNeg_lift ..) ,  X = imp P Q.

axContraposProof : Term -> Term -> Term
axContraposProof cP cQ =
  let cX = cImp cP cQ
      cY = cImp (cNeg (cNeg cP)) (cNeg (cNeg cQ))
      cW = cImp (cNeg cQ) (cNeg cP)
      t_lift = liftPProof (cImp cY cW) cX (axNegProof (cNeg cP) (cNeg cQ))
  in bCombProof cX cY cW t_lift (dNegLiftProof cP cQ)

encoded_axContrapos :
  (cP cQ : Term) ->
  Deriv (eqF (ap1 thmT (axContraposProof cP cQ))
             (cImp (cImp cP cQ) (cImp (cNeg cQ) (cNeg cP))))
encoded_axContrapos cP cQ =
  let cX = cImp cP cQ
      cY = cImp (cNeg (cNeg cP)) (cNeg (cNeg cQ))
      cW = cImp (cNeg cQ) (cNeg cP)
      t_lift = liftPProof (cImp cY cW) cX (axNegProof (cNeg cP) (cNeg cQ))
      e_lift = encoded_liftP cX (cImp cY cW) (axNegProof (cNeg cP) (cNeg cQ))
                 (encoded_axNeg (cNeg cP) (cNeg cQ))
  in encoded_bComb cX cY cW t_lift (dNegLiftProof cP cQ) e_lift (encoded_dNeg_lift cP cQ)

------------------------------------------------------------------------
-- encoded_and :  thmT (andProof cA cB pa pb) = cAnd cA cB ,  the dPos leg.
-- Mirrors CompressCanonical.andIntro : Deriv A -> Deriv B -> Deriv (fAnd A B)
-- = mp (mp (axContrapos X (neg B)) dX_nB) dNNB ,  X = imp A (neg B) .

andProof : Term -> Term -> Term -> Term -> Term
andProof cA cB pa pb =
  let cX = cImp cA (cNeg cB)
      t_dXA  = liftPProof cA cX pa
      t_dXnB = bCombProof cX cA (cNeg cB) (identPProof cX) t_dXA
      t_dNNB = cmp (qToDNegProof cB) pb
      p_cp   = axContraposProof cX (cNeg cB)
      t_m1   = cmp p_cp t_dXnB
  in cmp t_m1 t_dNNB

encoded_and :
  (cA cB pa pb : Term) ->
  Deriv (eqF (ap1 thmT pa) cA) ->
  Deriv (eqF (ap1 thmT pb) cB) ->
  Deriv (eqF (ap1 thmT (andProof cA cB pa pb)) (cAnd cA cB))
encoded_and cA cB pa pb e_da e_db =
  let cX = cImp cA (cNeg cB)
      t_dXA  = liftPProof cA cX pa
      e_dXA  = encoded_liftP cX cA pa e_da
      t_dXnB = bCombProof cX cA (cNeg cB) (identPProof cX) t_dXA
      e_dXnB = encoded_bComb cX cA (cNeg cB) (identPProof cX) t_dXA
                 (encoded_identP cX) e_dXA
      t_dNNB = cmp (qToDNegProof cB) pb
      e_dNNB = encoded_mp (qToDNegProof cB) pb cB (cNeg (cNeg cB))
                 (encoded_Q_to_dNeg cB) e_db
      p_cp   = axContraposProof cX (cNeg cB)
      e_cp   = encoded_axContrapos cX (cNeg cB)
      t_m1   = cmp p_cp t_dXnB
      e_m1   = encoded_mp p_cp t_dXnB (cImp cX (cNeg cB))
                 (cImp (cNeg (cNeg cB)) (cNeg cX)) e_cp e_dXnB
  in encoded_mp t_m1 t_dNNB (cNeg (cNeg cB)) (cNeg cX) e_m1 e_dNNB
