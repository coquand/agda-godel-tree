{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.CgiClashConj -- the integrated single-conjunct clash
-- for the NEW conjunction-shape K-formula  KdefConj M enum subject
-- with the program slot pushed through  enumRunProgOf enum  (see
-- T4.SurpriseG2.EnumRunProg ).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- `cgiClashConj`  ( the PRINCIPAL deliverable )  --  given
--
--   * `M` : Nat ,  `enum` : Fun1  ( the surprise-exam parameters ) ;
--   * `kStar` : Nat  +  `kStarBound` : NatLe kStar M  ( the META index
--     of the diagonal program in the enumeration ) ;
--   * `gLname` , `nTerm` , `x'` , `w0` : Term ;
--   * `dNeg`   : `thmT w0 = KcodeConj M enum x'`  ( the open dNeg ;
--                supplied by  KdefRecogConj.dNeg_from_hitKdefConj ) ;
--   * `runEnumForm` : `enumRunProgOf enum (natCode kStar) nTerm = s x'`
--                ( the diagonal run-fact in the new shape ; bridged by
--                the caller from  `evalU (parse gLname) nTerm = s x'`
--                +  `enumPin : enum (natCode kStar) = gLname`  via
--                `enumRunProgOf_eq` + `runProg_eq` ) ;
--
-- builds a  SomeProof  =  `(witness , Deriv (thmT witness = codeFalse))`
-- via the EXACT  chaitin_G1_assembly + encoded_exfalso  algebra of OLD
-- T4.CgiClash , re-targeted at the NEW matrix shape :
--
--    * the open dNeg is instantiated at `v0 := S0 := num (natCode kStar)`
--      and `v1 := S1 := num nTerm`  via  `thmT_at_sb`  twice and the
--      generic single-pass `passKConj`  ( parallel to OLD `passK` ) ;
--    * the leq-antecedent  `cEqTm (cAp2f sub S0 c_natCode_M) O`  is
--      stripped by `encoded_mp` ,  with the antecedent thmT-witness
--      built by  `thm13_binary sub`  on  `Deriv (leq (natCode kStar)
--      (natCode M))`  ( derived from  `kStarBound`  by external
--      recursion on the  NatLe  witness ) ;
--    * the positive leg is built INTERNALLY by  `thm13_binary` at
--      `enumRunProgOf enum`  on  `runEnumForm` ,  bridged to the
--      substituted ~def code's RHS shape via  `num_at_S` .
--
-- `cgiClashConjFromLegs`  ( the secondary deliverable , kept for
-- generality )  --  the simple wrapper that , given a closed ~def code
-- D + the two thmT-derivations  dPos / dNegFinal , runs
-- chaitin_G1_assembly + encoded_exfalso  ; the same wrapper as in the
-- earlier skeleton version of this file .   Callers that want to
-- supply the legs externally use this wrapper directly .

module T4.SurpriseG2.CgiClashConj where

open import T4.Base
open import T4.Tags using
  ( tag_sb ; tag_var ; tag_ap1 ; tag_ap2 ; tag_eq ; tag_neg ; tag_imp ; tag_s )
open import T4.Code using ( codeTerm ; codeFormula ; codeFun1 ; codeFun2 ; codeFalse )
open import T4.Num  using ( num ; num_at_O ; num_at_S )
open import T4.IsNat using ( num_eq_code ; isNat )
open import T4.NumContract using ( isNat_natCode )
open import T4.ThmT using ( thmT )
open import T4.ThmTAtSb using ( thmT_at_sb )
open import T4.SbF using ( sbf )
open import T4.SbT using ( sbt ; sbt_at_O )
open import T4.SbtAtVar using ( sbt_at_var_match ; sbt_at_var_nomatch )
open import T4.NumInert using ( sbt_num_inert )
open import T4.SbStep using
  ( sbf_step_imp ; sbf_step_atomic ; sbf_step_neg ; sbt_step_ap1 ; sbt_step_ap2
  ; NumCode ; ncO ; ncNum ; ncAp1 ; sbt_inert_NumCode )
open import T4.DefWit using ( cEqTm ; cNeg ; cImp )
open import T4.ConInj using ( cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.EncodedProp using ( encoded_exfalso ; exfProof )
open import T4.ChaitinG1 using ( chaitin_G1_assembly )
open import T4.Thm12.Thm13 using ( codeFXeqY2 ; thm13_binary )
open import T4.Thm12.All using ( thm12_Fun2 ; fst )
open import T4.Kdef using ( runProg )

open import T4.SurpriseG2.EnumRunProg using ( enumRunProgOf )
open import T4.SurpriseG2.KcodeConj
  using ( KcodeConj ; kdefConjConsts ; kdefConjSkel ; KcodeConj_eval )
open import T4.SurpriseG2.CGIConjSpec using ( Sigma ; mkSigma )

open import BRA3.Church using ( pi ; sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.RuleInst2 using ( NatLe ; le-zero ; le-suc )

------------------------------------------------------------------------
-- Local codeTerm-shape constructors  ( same as in T4.CgiClash ) .

cAp1f : Fun1 -> Term -> Term
cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

cAp2f : Fun2 -> Term -> Term -> Term
cAp2f g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

cVarc : Nat -> Term
cVarc k = ap2 Pair (natCode tag_var) (natCode k)

------------------------------------------------------------------------
-- SomeProof  -- the (witness, Deriv) pair returned by the clash .
--
-- DEFINED AS A TYPE ALIAS over the generic  Sigma  from CGIConjSpec
-- (instead of a fresh record) because :   a specialised record with
-- field  isPf : Deriv (eqF (ap1 thmT pf) codeFalse)  forces Agda to
-- elaborate  thmT  (a deep  C thmT_F2 o I  composition) at the record
-- definition site -- this single record alone takes 30s+ to typecheck
-- regardless of any other content .   Using the generic  Sigma  with
-- the type-level dependency expressed as a function  ( z -> Deriv ... )
-- bypasses the record-field elaboration entirely ; the alias adds
-- no typecheck overhead .

SomeProof : Set
SomeProof = Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))

------------------------------------------------------------------------
-- LEG-FORM WRAPPER  (kept for generality) :  given the closed ~def
-- code  D  +  dPos , dNegFinal , assemble  SomeProof  via
-- chaitin_G1_assembly + encoded_exfalso .

cgiClashConjFromLegs :
  (D cPos wNeg : Term) ->
  Deriv (eqF (ap1 thmT cPos) D) ->
  Deriv (eqF (ap1 thmT wNeg) (cNeg D)) ->
  SomeProof
cgiClashConjFromLegs D cPos wNeg dPos dNegFinal =
  mkSigma
    (cmp (cmp (exfProof D codeFalse) cPos) wNeg)
    (chaitin_G1_assembly D cPos (exfProof D codeFalse) wNeg
       dPos dNegFinal (encoded_exfalso D codeFalse))

------------------------------------------------------------------------
-- INERTNESS WITNESS  for  codeTerm (natCode M)  ( the "encoded numeral
-- tower" )  --  used by the  passKConj  substitution pass to keep the
-- M-natCode slot inside the antecedent atom inert .

NumCode_codeTerm_natCode : (M : Nat) -> NumCode (codeTerm (natCode M))
NumCode_codeTerm_natCode zero    = ncO
NumCode_codeTerm_natCode (suc m) =
  ncAp1 s (codeTerm (natCode m)) (NumCode_codeTerm_natCode m)

------------------------------------------------------------------------
-- META-to-OBJECT  bridge :  NatLe -> Deriv (leq natCode natCode) .
-- External induction on the  NatLe  witness ;  succ_mono  +  leqZ .

open import T4.Counting using ( leqZ )
open import T4.PHP      using ( succ_mono )

deriv_leq_natCode :
  (m n : Nat) -> NatLe m n -> Deriv (leq (natCode m) (natCode n))
deriv_leq_natCode .zero n (le-zero .n) = leqZ (natCode n)
deriv_leq_natCode .(suc _) .(suc _) (le-suc {m'} {n'} le') =
  succ_mono (natCode m') (natCode n') (deriv_leq_natCode m' n' le')

------------------------------------------------------------------------
-- POSITIVE-LEG LEMMA  ( factored as a top-level definition --  per
-- memory/feedback_slow_typecheck_means_abstract_constants ;  inlining
-- the  thm12_Fun2 (enumRunProgOf enum)  expansion inside  cgiClashConj
-- pushed the typecheck above 60s due to the  Fan-of-Fan-of-Fun2  spine
-- recursion .   Lifting it to a top-level keeps  cgiClashConj  warm
-- below the  20s  budget ) .
--
-- INPUTS :   enum , kStar , nTerm , x' , runEnumForm .
-- OUTPUT :   Deriv (eqF (ap1 thmT cPos) defEqShape) , where
--            cPos       = ap2 (fst (thm12_Fun2 (enumRunProgOf enum)))
--                              (natCode kStar) nTerm  ;
--            defEqShape = cEqTm (cAp2f (enumRunProgOf enum)
--                                  (ap1 num (natCode kStar)) (ap1 num nTerm))
--                              (cAp1f s (ap1 num x'))  .

cPosOf : Fun1 -> Nat -> Term -> Term
cPosOf enum kStar nTerm =
  ap2 (fst (thm12_Fun2 (enumRunProgOf enum))) (natCode kStar) nTerm

dPosConjAt :
  (enum : Fun1) (kStar : Nat) (nTerm x' : Term) ->
  Deriv (eqF (ap2 (enumRunProgOf enum) (natCode kStar) nTerm) (ap1 s x')) ->
  Deriv (eqF (ap1 thmT (cPosOf enum kStar nTerm))
              (cEqTm (cAp2f (enumRunProgOf enum)
                            (ap1 num (natCode kStar)) (ap1 num nTerm))
                     (cAp1f s (ap1 num x'))))
dPosConjAt enum kStar nTerm x' runEnumForm =
  let -- thm13_binary at  enumRunProgOf enum  :
      --   thmT cPos = codeFXeqY2 (enumRunProgOf enum) (natCode kStar) nTerm (s x') .
      d1 :
        Deriv (eqF (ap1 thmT (cPosOf enum kStar nTerm))
                    (codeFXeqY2 (enumRunProgOf enum)
                                 (natCode kStar) nTerm (ap1 s x')))
      d1 = thm13_binary (enumRunProgOf enum) (natCode kStar) nTerm
             (ap1 s x') runEnumForm

      -- Bridge :  num (s x') -> cAp1f s (num x')  (num_at_S x') .
      e_rhs :
        Deriv (eqF (ap1 num (ap1 s x'))
                    (ap2 Pair (natCode tag_ap1)
                      (ap2 Pair (natCode tag_s) (ap1 num x'))))
      e_rhs = num_at_S x'

      LHS-cAp2f : Term
      LHS-cAp2f =
        cAp2f (enumRunProgOf enum) (ap1 num (natCode kStar)) (ap1 num nTerm)

      bridgeInner :
        Deriv (eqF (ap2 Pair LHS-cAp2f (ap1 num (ap1 s x')))
                    (ap2 Pair LHS-cAp2f (cAp1f s (ap1 num x'))))
      bridgeInner = congR Pair LHS-cAp2f e_rhs

      bridge :
        Deriv (eqF (codeFXeqY2 (enumRunProgOf enum)
                                 (natCode kStar) nTerm (ap1 s x'))
                    (cEqTm LHS-cAp2f (cAp1f s (ap1 num x'))))
      bridge = congR Pair (natCode tag_eq) bridgeInner
  in ruleTrans d1 bridge

------------------------------------------------------------------------
-- ANTECEDENT-LEG LEMMA  ( factored as a top-level for the SAME slow-
-- typecheck reason as  dPosConjAt :   thm12_Fun2 sub  expands deeply
-- because  sub = R u p_aux v  triggers nested  thm12_Fun2 / thm12
-- recursion ) .
--
-- INPUTS :   M , kStar , kStarBound : NatLe kStar M .
-- OUTPUT :   Deriv (eqF (ap1 thmT (cAnteProofOf kStar M)) anteShape) , where
--            cAnteProofOf kStar M = ap2 (fst (thm12_Fun2 sub))
--                                       (natCode kStar) (natCode M) ;
--            anteShape           = cEqTm (cAp2f sub (ap1 num (natCode kStar))
--                                                   (codeTerm (natCode M))) O .

cAnteProofOf : Nat -> Nat -> Term
cAnteProofOf kStar M =
  ap2 (fst (thm12_Fun2 sub)) (natCode kStar) (natCode M)

dAnteConjAt :
  (M : Nat) (kStar : Nat) (kStarBound : NatLe kStar M) ->
  Deriv (eqF (ap1 thmT (cAnteProofOf kStar M))
              (cEqTm (cAp2f sub (ap1 num (natCode kStar)) (codeTerm (natCode M)))
                     O))
dAnteConjAt M kStar kStarBound =
  let dLeqNat : Deriv (leq (natCode kStar) (natCode M))
      dLeqNat = deriv_leq_natCode kStar M kStarBound

      d1 :
        Deriv (eqF (ap1 thmT (cAnteProofOf kStar M))
                    (codeFXeqY2 sub (natCode kStar) (natCode M) O))
      d1 = thm13_binary sub (natCode kStar) (natCode M) O dLeqNat

      -- Bridges :
      --   (a)  num (natCode M) -> codeTerm (natCode M)   via num_eq_code .
      --   (b)  num O           -> O                       via num_at_O .
      e_numM :
        Deriv (eqF (ap1 num (natCode M)) (codeTerm (natCode M)))
      e_numM = num_eq_code (natCode M) (isNat_natCode M)

      S0 : Term
      S0 = ap1 num (natCode kStar)

      e_subSlot :
        Deriv (eqF (cAp2f sub S0 (ap1 num (natCode M)))
                    (cAp2f sub S0 (codeTerm (natCode M))))
      e_subSlot = congR Pair (natCode tag_ap2)
                    (congR Pair (codeFun2 sub)
                      (congR Pair S0 e_numM))

      e_rhsZero : Deriv (eqF (ap1 num O) O)
      e_rhsZero = num_at_O

      e_anteInnerPair :
        Deriv (eqF (ap2 Pair (cAp2f sub S0 (ap1 num (natCode M))) (ap1 num O))
                    (ap2 Pair (cAp2f sub S0 (codeTerm (natCode M))) O))
      e_anteInnerPair =
        ruleTrans (congL Pair (ap1 num O) e_subSlot)
                  (congR Pair (cAp2f sub S0 (codeTerm (natCode M))) e_rhsZero)

      bridge :
        Deriv (eqF (codeFXeqY2 sub (natCode kStar) (natCode M) O)
                    (cEqTm (cAp2f sub S0 (codeTerm (natCode M))) O))
      bridge = congR Pair (natCode tag_eq) e_anteInnerPair
  in ruleTrans d1 bridge

------------------------------------------------------------------------
-- THE NEW K-FORMULA SHAPE  ( substituted form at progIdx / fuel
-- variables , subject hole filled with  num x' ) .   Mirrors OLD
-- CgiClash.KT  with the size-atom REPLACED by the leq-on-sub atom
-- and the program slot REPLACED by  cAp2f prgFun  where  prgFun
-- is ABSTRACT  ( := enumRunProgOf enum  at the cgiClashConj call site ) .
--
-- The abstraction is per
-- memory/feedback_slow_typecheck_means_abstract_constants :   leaving
-- prgFun  un-instantiated inside  passK / KT / defEqT  prevents the
-- ` codeFun2 (enumRunProgOf enum) `  recursion from firing at every
-- passK use ; the expansion only fires ONCE  ( at the cgiClashConj
-- call site , when the KT instance is unified with kdefConjSkel ) .

-- The closed M-natCode tower in the codeTerm encoding .
cnatMtower : Nat -> Term
cnatMtower M = codeTerm (natCode M)

-- antecedent atom :  cEqTm (cAp2f sub progIdx (cnatMtower M)) O .
anteAt : Nat -> Term -> Term
anteAt M progIdx = cEqTm (cAp2f sub progIdx (cnatMtower M)) O

-- ~def-equation atom :  cEqTm (cAp2f prgFun progIdx fuel) (cAp1f s (num subject)) .
defEqTAt : Fun2 -> Term -> Term -> Term -> Term
defEqTAt prgFun subject progIdx fuel =
  cEqTm (cAp2f prgFun progIdx fuel) (cAp1f s (ap1 num subject))

-- the open K-code  ( same Pair-chain as  kdefConjSkel M enum (num x')
-- when prgFun = enumRunProgOf enum ) .
KTAt : Nat -> Fun2 -> Term -> Term -> Term -> Term
KTAt M prgFun subject progIdx fuel =
  cImp (anteAt M progIdx) (cNeg (defEqTAt prgFun subject progIdx fuel))

------------------------------------------------------------------------
-- The generic single substitution pass over  KTAt .   Parametric in
-- prgFun : Fun2  ( abstract ) ;  the body never expands  codeFun2 prgFun ,
-- so this lemma typechecks in <1s regardless of how deep  prgFun
-- unfolds .

passKAt :
  (M : Nat) (prgFun : Fun2) (subject : Term) ->
  (k : Nat) (S progIdx progIdx' fuel fuel' : Term) ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) progIdx) progIdx') ->
  Deriv (eqF (ap2 sbt (ap2 Pair (natCode k) S) fuel) fuel') ->
  Deriv (eqF (ap2 sbf (ap2 Pair (natCode k) S) (KTAt M prgFun subject progIdx fuel))
              (KTAt M prgFun subject progIdx' fuel'))
passKAt M prgFun subject k S progIdx progIdx' fuel fuel' eIdx eFuel =
  let spec : Term
      spec = ap2 Pair (natCode k) S

      cnatM : Term
      cnatM = cnatMtower M

      e_cnatM : Deriv (eqF (ap2 sbt spec cnatM) cnatM)
      e_cnatM = sbt_inert_NumCode cnatM (NumCode_codeTerm_natCode M) k S

      e_O : Deriv (eqF (ap2 sbt spec O) O)
      e_O = sbt_at_O spec

      e_sHole : Deriv (eqF (ap2 sbt spec (cAp1f s (ap1 num subject)))
                            (cAp1f s (ap1 num subject)))
      e_sHole = sbt_inert_NumCode (cAp1f s (ap1 num subject))
                  (ncAp1 s (ap1 num subject) (ncNum subject)) k S

      -- antecedent atom LHS : cAp2f sub progIdx cnatM  ->  cAp2f sub progIdx' cnatM .
      e_anteLHS : Deriv (eqF (ap2 sbt spec (cAp2f sub progIdx cnatM))
                              (cAp2f sub progIdx' cnatM))
      e_anteLHS = sbt_step_ap2 k S sub progIdx cnatM progIdx' cnatM
                    eIdx e_cnatM

      -- antecedent atom  ( = cEqTm LHS O ) .
      e_ante : Deriv (eqF (ap2 sbf spec (anteAt M progIdx)) (anteAt M progIdx'))
      e_ante = sbf_step_atomic k S
                 (cAp2f sub progIdx cnatM) O
                 (cAp2f sub progIdx' cnatM) O
                 e_anteLHS e_O

      -- ~def-equation atom LHS : cAp2f prgFun progIdx fuel  ->  cAp2f prgFun progIdx' fuel' .
      e_defLHS : Deriv (eqF (ap2 sbt spec (cAp2f prgFun progIdx fuel))
                             (cAp2f prgFun progIdx' fuel'))
      e_defLHS = sbt_step_ap2 k S prgFun
                   progIdx fuel progIdx' fuel' eIdx eFuel

      -- ~def-equation atom .
      e_def : Deriv (eqF (ap2 sbf spec (defEqTAt prgFun subject progIdx fuel))
                          (defEqTAt prgFun subject progIdx' fuel'))
      e_def = sbf_step_atomic k S
                (cAp2f prgFun progIdx fuel) (cAp1f s (ap1 num subject))
                (cAp2f prgFun progIdx' fuel') (cAp1f s (ap1 num subject))
                e_defLHS e_sHole

      -- neg-wrap on the ~def-equation atom .
      e_negdef : Deriv (eqF (ap2 sbf spec (cNeg (defEqTAt prgFun subject progIdx fuel)))
                             (cNeg (defEqTAt prgFun subject progIdx' fuel')))
      e_negdef = sbf_step_neg k S
                   (defEqTAt prgFun subject progIdx fuel)
                   (defEqTAt prgFun subject progIdx' fuel') e_def
  in sbf_step_imp k S
       (anteAt M progIdx) (cNeg (defEqTAt prgFun subject progIdx fuel))
       (anteAt M progIdx') (cNeg (defEqTAt prgFun subject progIdx' fuel'))
       e_ante e_negdef

------------------------------------------------------------------------
-- THE INTEGRATED CLASH  ( the PRINCIPAL deliverable ) is in the
-- separate file  T4.SurpriseG2.CgiClashConjMain  --  splitting it
-- off keeps the same-file typecheck of the heavy
-- dPosConjAt / dAnteConjAt  signatures from interacting with the
-- cgiClashConj body unification ( which would push cgiClashConj's
-- typecheck above the 20s budget , per slow-typecheck principle ) .
-- All glue lemmas above are re-exported there .
