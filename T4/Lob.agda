{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Lob -- Loeb's theorem in the T4 verifier framework, UNCONDITIONAL
-- (general target formula A), as the generalisation of Guard's clean
-- diagonal Goedel II (T4.Thm.Thm14GodelII = A := falseF).
--
-- Statement:
--
--   lob : (A : Formula) (nf0 : notFreeF 0 A) (nf1 : notFreeF 1 A) ->
--         Deriv (imp (atomic (eqn (ap1 thmT (var 1)) (codeFormula A))) A) ->
--         Deriv A
--
-- i.e. from a proof of the Loeb hypothesis  (thmT(var 1) = code A) -> A
-- (with var 1 the free proof-code variable) produce a proof of A.  The
-- ONLY side condition is the minimal freshness: the diagonal slot (var 0)
-- and the proof variable (var 1) are not free in A (T4.NotFree.notFreeF).
--
-- CONSTRUCTION (mirrors Guard Theorem 14, but G is an IMPLICATION so the
-- climb is SIMPLER -- ONE encoded mp, no HPart/TPrime schema):
--
--   Seed   F   = imp (thmT(var 1) = var 0) A          -- var 0 = diagonal slot
--   sub-form diagonal (Thm14F-style):  G = imp (thmT(var 1) = sub(i,i)) A
--   so  G  <->  ( box_1 G -> A )  with the diagonal identity
--   sub(i,i) =Deriv= codeFormula G.
--
--   step1/2/3 (= Thm14Step1-3, with Loeb's i,j) :
--       under  P_x x = (thmT x = j) ,  thmT(g x) = "th(x_) = sub(i,i)"  (= A_ x).
--   step4 (= Thm14Step4, but G = imp .. A) :
--       under  P_x x ,  thmT(K_part x) = encImp (A_ x) (codeFormula A)
--       (the box of  G[var 1 := x_] = (atom[x_] -> A) ;  A-part inert as
--        var 1 is not free in A).
--   step5 (ONE encoded mp) :  thmT(big_term x) = codeFormula A .
--   endgame :  big_term(var 1) + Loeb hypothesis -> Deriv (imp (thmT(var 1)=j) A) ;
--       Leibniz  j -> sub(i,i)  (reusing var 0 as the Leibniz slot)  ->  Deriv G ;
--       necessitate + instantiate -> Deriv A.
--
-- The two freshness hypotheses each yield, via T4.NotFree:
--   nf0 -> meta substF no-op at var 0 (diagonal/Leibniz slot) ;
--   nf1 -> meta substF no-op at var 1  AND  object-level sbf inertness on
--          codeFormula A at index 1 (FreshNF.sbfInert_codeFormula).

module T4.Lob where

open import T4.Base
open import T4.Tags
open import T4.Code              using ( codeFun1 ; codeFun2 ; codeFormula ; codeTerm )
open import T4.Num               using ( num )
open import T4.NumContract       using ( numContract ; module NumContract )
open import T4.SbT               using ( sbt )
open import T4.SbF               using ( sbf )
open import T4.SbfAtClosures     using ( sbContract )
open import T4.SbDerived         using ( module Derive )
open import T4.NotFree
  using ( notFreeF ; substF_notFree ; module FreshNF
        ; notFree_above_F ; substF_back ; notFree0_after_F ; notFree_preserve_F
        ; substF_back_at ; notFree_self_after_F ; notFree_preserve_at_F )
open import T4.ThmT              using ( thmT )
open import T4.Encode            using ( encode )
open import T4.NatBridge         using ( codeFormulaNat ; codeFormula_eq )
open import T4.Sub               using ( sub ; sub_eq )
open import T4.ThmTCompleteRec   using ( thmT_complete_rec )
open import T4.ThmTAtSb          using ( thmT_at_sb )
open import T4.SbContract        using ( SbContract ; module SbContract )
open import T4.Thm.Thm14Step4    using ( sbt_codeTerm_natCode_eq )

open import BRA3.Substitutivity  using ( substF_cong )
open import BRA3.Logic           using ( impTrans )
open import BRA3.Dispatch        using ( closed_ap2 ; closedAt )
open import BRA3.RuleInst2
  using ( maxVarF ; NatLe ; le-zero ; le-suc ; le-trans ; le-refl ; le-suc-right
        ; maxN-le-left ; maxN-le-right ; natEq-lt-false ; natEq_sym
        ; natEq-refl )
open import BRA3.RuleInst2       using ( maxN )

open import T4.SbStep
  using ( InertU ; NumCode ; ncNum ; ncAp1 ; ncAp2 ; sbt_inert_NumCode )
open import T4.Thm12.All         using ( thm12 ; thm12_Fun2 ; fst ; snd )
open import T4.Thm12.Thm13       using ( codeFXeqY1 ; codeFXeqY2 ; thm13_binary )
open import T4.Thm12.EncodedEqChain     using ( Df_eqTrans )
open import T4.Thm12.EncodedAxEqTrans   using ( Df_axEqTrans )
open import T4.Thm12.EncodedRefl        using ( Df_refl_meta )
open import T4.Thm12.ImpHelpers
  using ( impRefl ; impLift ; impMp ; impCong1 ; impCongR ; impEqTrans )
open import T4.Thm12.ImpEncodedEqChain
  using ( imp_encoded_eqSym ; imp_encoded_eqTrans )
open import T4.Thm12.EncodedMp   using ( imp_encoded_mp )
open import T4.Thm.Thm14Step1    using ( thm13_singulary_imp )

open Derive sbt sbf sbContract using ( sbfEq_codeFormula )
open FreshNF sbt sbf sbContract using ( sbfInert_codeFormula )
open NumContract numContract using ( numEq )
open SbContract sbContract
  using ( sbf_at_atomic ; sbf_at_imp ; sbt_at_ap1 ; sbt_at_ap2
        ; sbt_at_var_match )

------------------------------------------------------------------------
-- Closedness of the code of any Formula / Term / Fun (everything is
-- built from natCode / O leaves under Pair -- NO  var  nodes).  Generic
-- in the (arbitrary) formula; used for the endgame substT no-ops on
--  codeFormula A  and  sub(i,i) .

closed_codeFun1 : (f : Fun1) -> Closed (codeFun1 f)
closed_codeFun2 : (g : Fun2) -> Closed (codeFun2 g)

closed_codeFun1 s           = closed_natCode _
closed_codeFun1 o           = closed_natCode _
closed_codeFun1 u           = closed_natCode _
closed_codeFun1 (C g h1 h2) =
  closed_ap2 Pair _ _ (closed_natCode _)
    (closed_ap2 Pair _ _ (closed_codeFun2 g)
      (closed_ap2 Pair _ _ (closed_codeFun1 h1) (closed_codeFun1 h2)))

closed_codeFun2 v           = closed_natCode _
closed_codeFun2 (R g h1 h2) =
  closed_ap2 Pair _ _ (closed_natCode _)
    (closed_ap2 Pair _ _ (closed_codeFun1 g)
      (closed_ap2 Pair _ _ (closed_codeFun2 h1) (closed_codeFun2 h2)))

closed_codeTerm : (t : Term) -> Closed (codeTerm t)
closed_codeTerm O           = closed_O
closed_codeTerm (var k)     =
  closed_ap2 Pair _ _ (closed_natCode _) (closed_natCode _)
closed_codeTerm (ap1 f t)   =
  closed_ap2 Pair _ _ (closed_natCode _)
    (closed_ap2 Pair _ _ (closed_codeFun1 f) (closed_codeTerm t))
closed_codeTerm (ap2 g a b) =
  closed_ap2 Pair _ _ (closed_natCode _)
    (closed_ap2 Pair _ _ (closed_codeFun2 g)
      (closed_ap2 Pair _ _ (closed_codeTerm a) (closed_codeTerm b)))

closed_codeFormula : (P : Formula) -> Closed (codeFormula P)
closed_codeFormula (atomic (eqn a b)) =
  closed_ap2 Pair _ _ (closed_natCode _)
    (closed_ap2 Pair _ _ (closed_codeTerm a) (closed_codeTerm b))
closed_codeFormula (neg p)   =
  closed_ap2 Pair _ _ (closed_natCode _) (closed_codeFormula p)
closed_codeFormula (imp p q) =
  closed_ap2 Pair _ _ (closed_natCode _)
    (closed_ap2 Pair _ _ (closed_codeFormula p) (closed_codeFormula q))
closed_codeFormula (E f) =
  closed_ap2 Pair _ _ (closed_natCode _) (closed_codeFun1 f)

------------------------------------------------------------------------
-- Guard-style encoded Term abbreviations (IDENTICAL to T4.Thm.Thm14F,
-- so that thm13_singulary_imp / thm13_binary land on these by refl).

code : Term -> Term
code t = ap1 num t

encEqF : Term -> Term -> Term
encEqF a b = ap2 Pair (natCode tag_eq) (ap2 Pair a b)

encThm : Term -> Term
encThm t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 thmT) t)

encSub : Term -> Term -> Term
encSub a b =
  ap2 Pair (natCode tag_ap2)
    (ap2 Pair (codeFun2 sub) (ap2 Pair a b))

encImp : Term -> Term -> Term
encImp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

------------------------------------------------------------------------
-- Everything below is parametric in the (sentence) target formula A.

-- The only side condition is that the diagonal slot (var 0) and the
-- proof variable (var 1) are not free in A.
module _ (A : Formula) (nf0 : notFreeF zero A) (nf1 : notFreeF (suc zero) A) where

 ----------------------------------------------------------------------
 -- The no-op facts the two freshness hypotheses supply.

 -- Meta substF no-ops (var 0 / var 1 not free in A).
 aNoop0 : (X : Term) -> Eq (substF zero X A) A
 aNoop0 X = substF_notFree zero A X nf0

 aNoop1 : (X : Term) -> Eq (substF (suc zero) X A) A
 aNoop1 X = substF_notFree (suc zero) A X nf1

 -- Object-level sbf inertness on codeFormula A at index 1 (var 1 fresh).
 aSbfInert1 :
   (S : Term) ->
   Deriv (eqF (ap2 sbf (ap2 Pair (natCode (suc zero)) S) (codeFormula A))
              (codeFormula A))
 aSbfInert1 S = sbfInert_codeFormula (suc zero) S A nf1

 ----------------------------------------------------------------------
 -- The Loeb seed and its sub-form diagonal fixed point (mirror Thm14F).
 --
 --   F        = imp (thmT(var 1) = var 0) A
 --   diag_sub = sub(var 0, var 0)
 --   H        = substF 0 diag_sub F
 --   i        = natCode (codeFormulaNat H)
 --   G        = substF 0 i H
 --   j        = natCode (codeFormulaNat G)

 F : Formula
 F = imp (atomic (eqn (ap1 thmT (var (suc zero))) (var zero))) A

 diag_sub : Term
 diag_sub = ap2 sub (var zero) (var zero)

 H : Formula
 H = substF zero diag_sub F

 iNat : Nat
 iNat = codeFormulaNat H

 i : Term
 i = natCode iNat

 G : Formula
 G = substF zero i H

 jNat : Nat
 jNat = codeFormulaNat G

 j : Term
 j = natCode jNat

 ----------------------------------------------------------------------
 -- Guard's diagonal identity  sub(i,i) =Deriv= codeFormula G  (VERBATIM
 -- from T4.Thm.Thm14F; the proof is generic in H).

 diag_term_eq : Deriv (eqF (ap2 sub i i) (codeFormula G))
 diag_term_eq =
   let
     s1 : Deriv (eqF (ap2 sub i i)
                     (ap2 sbf (ap2 Pair (natCode zero) (ap1 num i)) i))
     s1 = sub_eq i i

     s2 : Deriv (eqF (ap1 num i) (codeTerm i))
     s2 = numEq iNat

     s3 : Deriv (eqF (ap2 Pair (natCode zero) (ap1 num i))
                     (ap2 Pair (natCode zero) (codeTerm i)))
     s3 = congR Pair (natCode zero) s2

     s4 : Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (ap1 num i)) i)
                     (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) i))
     s4 = congL sbf i s3

     s5 : Deriv (eqF i (codeFormula H))
     s5 = ruleSym (codeFormula_eq H)

     s6 : Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) i)
                     (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) (codeFormula H)))
     s6 = congR sbf (ap2 Pair (natCode zero) (codeTerm i)) s5

     s7 : Deriv (eqF (ap2 sbf (ap2 Pair (natCode zero) (codeTerm i)) (codeFormula H))
                     (codeFormula G))
     s7 = sbfEq_codeFormula zero i H

   in ruleTrans s1 (ruleTrans s4 (ruleTrans s6 s7))

 -- sub(i,i) =Deriv= j .
 sub_ii_eq_j : Deriv (eqF (ap2 sub i i) j)
 sub_ii_eq_j = ruleTrans diag_term_eq (codeFormula_eq G)

 -- codeFormula G =Deriv= j .
 codeFormulaG_eq_j : Deriv (eqF (codeFormula G) j)
 codeFormulaG_eq_j = codeFormula_eq G

 ----------------------------------------------------------------------
 -- The "clean" Goedel sentence  G_clean = imp atom' A , and the bridge
 -- codeFormula G =Eq= codeFormula G_clean (the A-part of G differs from A
 -- only by two substF no-ops, since A is closed).

 atom' : Formula
 atom' = atomic (eqn (ap1 thmT (var (suc zero))) (ap2 sub i i))

 G_clean : Formula
 G_clean = imp atom' A

 -- G = imp atom' (substF 0 i (substF 0 diag_sub A))  definitionally.
 bodyEq : Eq (substF zero i (substF zero diag_sub A)) A
 bodyEq = eqTrans (eqCong (substF zero i) (aNoop0 diag_sub)) (aNoop0 i)

 GG : Eq G G_clean
 GG = eqCong (\ X -> imp atom' X) bodyEq

 cG_eq : Eq (codeFormula G) (codeFormula G_clean)
 cG_eq = eqCong codeFormula GG

 ----------------------------------------------------------------------
 -- step1 / step2 / step3  (= T4.Thm.Thm14Step1-3 with Loeb's i, j).

 -- "th(x) = j" .
 P_x : Term -> Formula
 P_x x = eqF (ap1 thmT x) j

 -- "Dth(x)" .
 Df_thmT : Term -> Term
 Df_thmT x = ap1 (fst (thm12 thmT)) x

 -- Step 1 :  th(x) = j  ⊃  th(Dth(x)) = "th(x_) = j" .
 step1 :
   (x : Term) ->
   Deriv (imp (P_x x)
               (eqF (ap1 thmT (Df_thmT x))
                     (encEqF (encThm (code x)) (code j))))
 step1 x =
   thm13_singulary_imp (P_x x) thmT x j (impRefl (P_x x))

 -- "Dsub(i,i)" .
 Df_sub_ii : Term
 Df_sub_ii = ap2 (fst (thm12_Fun2 sub)) i i

 -- Step 2 :  th(Dsub(i,i)) = "sub(i,i) = j"  (unconditional) .
 step2 :
   Deriv (eqF (ap1 thmT Df_sub_ii)
               (encEqF (encSub (code i) (code i)) (code j)))
 step2 = thm13_binary sub i i j sub_ii_eq_j

 -- Df_flipped_step2  -- Step 2's equality flipped to "j = sub(i,i)" .
 Df_flipped_step2 : Term
 Df_flipped_step2 =
   ap2 Pair (natCode tag_mp)
     (ap2 Pair
       (ap2 Pair (natCode tag_mp)
         (ap2 Pair (Df_axEqTrans (encSub (code i) (code i))
                                  (code j)
                                  (encSub (code i) (code i)))
                    Df_sub_ii))
       (Df_refl_meta (encSub (code i) (code i))))

 -- g x  -- the combined derivation Term .
 g : Term -> Term
 g x = Df_eqTrans (Df_thmT x) Df_flipped_step2
                   (encThm (code x)) (code j) (encSub (code i) (code i))

 -- A_ x  =  "th(x_) = sub(i,i)" .
 A_ : Term -> Term
 A_ x = encEqF (encThm (code x)) (encSub (code i) (code i))

 -- Step 3 :  th(x) = j  ⊃  th(g x) = "th(x_) = sub(i,i)" .
 step3 :
   (x : Term) ->
   Deriv (imp (P_x x)
               (eqF (ap1 thmT (g x)) (A_ x)))
 step3 x =
   let
     P : Formula
     P = P_x x

     step1_imp :
       Deriv (imp P (eqF (ap1 thmT (Df_thmT x))
                          (encEqF (encThm (code x)) (code j))))
     step1_imp = step1 x

     step2_imp :
       Deriv (imp P (eqF (ap1 thmT Df_sub_ii)
                          (encEqF (encSub (code i) (code i)) (code j))))
     step2_imp = impLift {P} step2

     iEncThmX : InertU (encThm (code x))
     iEncThmX = sbt_inert_NumCode (encThm (code x))
                  (ncAp1 thmT (code x) (ncNum x))

     iCodeJ : InertU (code j)
     iCodeJ = sbt_inert_NumCode (code j) (ncNum j)

     iEncSub : InertU (encSub (code i) (code i))
     iEncSub = sbt_inert_NumCode (encSub (code i) (code i))
                 (ncAp2 sub (code i) (code i) (ncNum i) (ncNum i))

     step2_flipped :
       Deriv (imp P (eqF (ap1 thmT Df_flipped_step2)
                          (encEqF (code j) (encSub (code i) (code i)))))
     step2_flipped =
       imp_encoded_eqSym P Df_sub_ii
                           (encSub (code i) (code i)) (code j)
                           iEncSub iCodeJ
                           step2_imp

     step3_imp :
       Deriv (imp P (eqF (ap1 thmT (g x))
                          (encEqF (encThm (code x)) (encSub (code i) (code i)))))
     step3_imp =
       imp_encoded_eqTrans P
         (Df_thmT x) Df_flipped_step2
         (encThm (code x)) (code j) (encSub (code i) (code i))
         iEncThmX iCodeJ iEncSub
         step1_imp step2_flipped

   in step3_imp

 ----------------------------------------------------------------------
 -- step4  (= T4.Thm.Thm14Step4, but  G_clean = imp atom' A ).
 --
 -- Under  P_x x = (thmT x = j) ,  K_part x  proves the box of
 --   G[var 1 := x_]  =  (atom[x_] -> A)  :
 --     thmT(K_part x) = encImp (A_ x) (codeFormula A) .
 -- The atom-part of the unfold is verbatim Thm14Step4; the A-part is
 -- inert because A is closed (aSbfInert).

 cSpec_x : Term -> Term
 cSpec_x x = ap2 Pair (natCode (suc zero)) (code x)

 K_part : Term -> Term
 K_part x = ap2 Pair (natCode tag_sb) (ap2 Pair (cSpec_x x) x)

 step4 :
   (x : Term) ->
   Deriv (imp (P_x x)
               (eqF (ap1 thmT (K_part x))
                     (encImp (A_ x) (codeFormula A))))
 step4 x =
   let
     P : Formula
     P = P_x x

     cSpec : Term
     cSpec = cSpec_x x

     -- (A)  thmT(K_part x) = sbf cSpec (thmT x)   [thmT_at_sb] , lifted.
     step_A_imp :
       Deriv (imp P (eqF (ap1 thmT (K_part x))
                          (ap2 sbf cSpec (ap1 thmT x))))
     step_A_imp = impLift {P} (thmT_at_sb cSpec x)

     -- (B)  under P : sbf cSpec (thmT x) = sbf cSpec j .
     step_B_imp :
       Deriv (imp P (eqF (ap2 sbf cSpec (ap1 thmT x)) (ap2 sbf cSpec j)))
     step_B_imp = impCongR {P} sbf (ap1 thmT x) j cSpec (impRefl P)

     -- (C)  j = codeFormula G_clean   (j = codeFormula G , then cG_eq) ;
     --       sbf cSpec j = sbf cSpec (codeFormula G_clean) .
     j_eq_clean : Deriv (eqF j (codeFormula G_clean))
     j_eq_clean = eqSubst (\ z -> Deriv (eqF j z)) cG_eq
                          (ruleSym codeFormulaG_eq_j)

     step_C_imp :
       Deriv (imp P (eqF (ap2 sbf cSpec j)
                          (ap2 sbf cSpec (codeFormula G_clean))))
     step_C_imp = impLift {P} (congR sbf cSpec j_eq_clean)

     -- (D)  unfold  sbf cSpec (codeFormula G_clean) .
     eqInner : Term
     eqInner =
       ap2 Pair (natCode tag_eq)
         (ap2 Pair (codeTerm (ap1 thmT (var (suc zero))))
                   (codeTerm (ap2 sub i i)))

     -- imp-unfold :  sbf cSpec (codeFormula (imp atom' A))
     --   = Pair tag_imp (Pair (sbf cSpec eqInner) (sbf cSpec (codeFormula A))) .
     step_D1 :
       Deriv (eqF (ap2 sbf cSpec (codeFormula G_clean))
                   (ap2 Pair (natCode tag_imp)
                     (ap2 Pair (ap2 sbf cSpec eqInner)
                               (ap2 sbf cSpec (codeFormula A)))))
     step_D1 = sbf_at_imp (suc zero) (code x) (codeFormula atom') (codeFormula A)

     -- atom-part :  sbf cSpec eqInner = A_ x   (verbatim Thm14Step4).
     step_D2 :
       Deriv (eqF (ap2 sbf cSpec eqInner)
                   (ap2 Pair (natCode tag_eq)
                     (ap2 Pair
                       (ap2 sbt cSpec (codeTerm (ap1 thmT (var (suc zero)))))
                       (ap2 sbt cSpec (codeTerm (ap2 sub i i))))))
     step_D2 = sbf_at_atomic (suc zero) (code x)
                 (codeTerm (ap1 thmT (var (suc zero))))
                 (codeTerm (ap2 sub i i))

     -- LHS slot :  sbt cSpec (codeTerm (ap1 thmT (var 1))) = encThm (code x) .
     step_E1 :
       Deriv (eqF (ap2 sbt cSpec (codeTerm (ap1 thmT (var (suc zero)))))
                   (ap2 Pair (natCode tag_ap1)
                     (ap2 Pair (codeFun1 thmT)
                       (ap2 sbt cSpec (codeTerm (var (suc zero)))))))
     step_E1 = sbt_at_ap1 (suc zero) (code x) thmT (codeTerm (var (suc zero)))

     step_E2 :
       Deriv (eqF (ap2 sbt cSpec (codeTerm (var (suc zero)))) (code x))
     step_E2 = sbt_at_var_match (suc zero) (code x)

     step_E :
       Deriv (eqF (ap2 sbt cSpec (codeTerm (ap1 thmT (var (suc zero)))))
                   (encThm (code x)))
     step_E =
       ruleTrans step_E1
         (congR Pair (natCode tag_ap1)
           (congR Pair (codeFun1 thmT) step_E2))

     -- RHS slot :  sbt cSpec (codeTerm (ap2 sub i i)) = encSub (code i)(code i) .
     step_F1 :
       Deriv (eqF (ap2 sbt cSpec (codeTerm (ap2 sub i i)))
                   (ap2 Pair (natCode tag_ap2)
                     (ap2 Pair (codeFun2 sub)
                       (ap2 Pair
                         (ap2 sbt cSpec (codeTerm i))
                         (ap2 sbt cSpec (codeTerm i))))))
     step_F1 = sbt_at_ap2 (suc zero) (code x) sub (codeTerm i) (codeTerm i)

     sbt_i_to_code : Deriv (eqF (ap2 sbt cSpec (codeTerm i)) (code i))
     sbt_i_to_code =
       ruleTrans (sbt_codeTerm_natCode_eq (suc zero) (code x) iNat)
                 (ruleSym (numEq iNat))

     step_F2 :
       Deriv (eqF (ap2 Pair
                     (ap2 sbt cSpec (codeTerm i))
                     (ap2 sbt cSpec (codeTerm i)))
                   (ap2 Pair (code i) (code i)))
     step_F2 =
       ruleTrans (congL Pair (ap2 sbt cSpec (codeTerm i)) sbt_i_to_code)
                 (congR Pair (code i) sbt_i_to_code)

     step_F :
       Deriv (eqF (ap2 sbt cSpec (codeTerm (ap2 sub i i)))
                   (encSub (code i) (code i)))
     step_F =
       ruleTrans step_F1
         (congR Pair (natCode tag_ap2)
           (congR Pair (codeFun2 sub) step_F2))

     -- combine  step_D2 + step_E + step_F  ->  sbf cSpec eqInner = A_ x .
     atomPart :
       Deriv (eqF (ap2 sbf cSpec eqInner) (A_ x))
     atomPart =
       ruleTrans step_D2
         (congR Pair (natCode tag_eq)
           (ruleTrans
             (congL Pair (ap2 sbt cSpec (codeTerm (ap2 sub i i))) step_E)
             (congR Pair (encThm (code x)) step_F)))

     -- A-part :  sbf cSpec (codeFormula A) = codeFormula A   (A closed).
     aPart : Deriv (eqF (ap2 sbf cSpec (codeFormula A)) (codeFormula A))
     aPart = aSbfInert1 (code x)

     -- assemble (D) :  sbf cSpec (codeFormula G_clean) = encImp (A_ x)(codeFormula A) .
     step_D :
       Deriv (eqF (ap2 sbf cSpec (codeFormula G_clean))
                   (encImp (A_ x) (codeFormula A)))
     step_D =
       ruleTrans step_D1
         (congR Pair (natCode tag_imp)
           (ruleTrans
             (congL Pair (ap2 sbf cSpec (codeFormula A)) atomPart)
             (congR Pair (A_ x) aPart)))

     step_D_imp :
       Deriv (imp P (eqF (ap2 sbf cSpec (codeFormula G_clean))
                          (encImp (A_ x) (codeFormula A))))
     step_D_imp = impLift {P} step_D

     -- chain A,B,C,D via impEqTrans .
     step_AB :
       Deriv (imp P (eqF (ap1 thmT (K_part x)) (ap2 sbf cSpec j)))
     step_AB =
       impEqTrans {P}
         (ap1 thmT (K_part x)) (ap2 sbf cSpec (ap1 thmT x)) (ap2 sbf cSpec j)
         step_A_imp step_B_imp

     step_ABC :
       Deriv (imp P (eqF (ap1 thmT (K_part x))
                          (ap2 sbf cSpec (codeFormula G_clean))))
     step_ABC =
       impEqTrans {P}
         (ap1 thmT (K_part x)) (ap2 sbf cSpec j)
         (ap2 sbf cSpec (codeFormula G_clean))
         step_AB step_C_imp

   in impEqTrans {P}
        (ap1 thmT (K_part x)) (ap2 sbf cSpec (codeFormula G_clean))
        (encImp (A_ x) (codeFormula A))
        step_ABC step_D_imp

 ----------------------------------------------------------------------
 -- step5  (ONE encoded mp) :  thmT(big_term x) = codeFormula A .
 --
 --   K_part x  proves  (atom[x_] -> A)  [step4] ;
 --   g x       proves   atom[x_]        [step3] ;
 --   mp(K_part x, g x)  proves  A .

 big_term : Term -> Term
 big_term x = ap2 Pair (natCode tag_mp) (ap2 Pair (K_part x) (g x))

 step5 :
   (x : Term) ->
   Deriv (imp (P_x x)
               (eqF (ap1 thmT (big_term x)) (codeFormula A)))
 step5 x =
   imp_encoded_mp (P_x x) (K_part x) (g x) (A_ x) (codeFormula A)
     (step4 x) (step3 x)

 ----------------------------------------------------------------------
 -- The requested Loeb hypothesis :  (thmT(var 1) = code A) -> A .

 LobHyp : Set
 LobHyp =
   Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula A))) A)

 ----------------------------------------------------------------------
 -- The closed diagonal subject  sub(i,i)  is a closed Term.

 closed_sub_ii : Closed (ap2 sub i i)
 closed_sub_ii = closed_ap2 sub i i (closed_natCode iNat) (closed_natCode iNat)

 ----------------------------------------------------------------------
 -- LOEB'S THEOREM.

 lob : LobHyp -> Deriv A
 lob hLob =
   let
     v1 : Term
     v1 = var (suc zero)

     bt : Term
     bt = big_term v1

     -- step5 at the proof variable  var 1 .
     step5_v1 :
       Deriv (imp (eqF (ap1 thmT v1) j)
                   (eqF (ap1 thmT bt) (codeFormula A)))
     step5_v1 = step5 v1

     -- Loeb hyp instantiated at the proof code  bt = big_term(var 1) .
     hInst0 :
       Deriv (substF (suc zero) bt
               (imp (atomic (eqn (ap1 thmT v1) (codeFormula A))) A))
     hInst0 = ruleInst (suc zero) bt hLob

     -- substT 1 bt (codeFormula A) = codeFormula A  (codeFormula A closed) .
     hInst1 :
       Deriv (imp (eqF (ap1 thmT bt) (codeFormula A)) (substF (suc zero) bt A))
     hInst1 =
       eqSubst (\ z -> Deriv (imp (eqF (ap1 thmT bt) z) (substF (suc zero) bt A)))
               (closedAt (closed_codeFormula A) (suc zero) bt)
               hInst0

     -- substF 1 bt A = A  (A closed) .
     hInst :
       Deriv (imp (eqF (ap1 thmT bt) (codeFormula A)) A)
     hInst =
       eqSubst (\ X -> Deriv (imp (eqF (ap1 thmT bt) (codeFormula A)) X))
               (aNoop1 bt)
               hInst1

     -- compose  step5_v1 ;  hInst   ->  D : (thmT(var 1) = j) -> A .
     dD : Deriv (imp (eqF (ap1 thmT v1) j) A)
     dD = impTrans step5_v1 hInst

     ------------------------------------------------------------------
     -- Leibniz bridge  j -> sub(i,i)  ->  Deriv G_clean .  We reuse the
     -- diagonal slot (var 0) as the Leibniz variable, so only var 0
     -- freshness is needed (no extra fresh index).
     --
     --   Phi z = imp (thmT(var 1) = z) A    (var 0 = z = slot)
     --   substF 0 j Phi         = imp (thmT(var 1)=j)        (substF 0 j A)         = dD-type
     --   substF 0 (sub i i) Phi = imp (thmT(var 1)=sub(i,i)) (substF 0 (sub i i) A) = G_clean

     Phi : Formula
     Phi = imp (eqF (ap1 thmT v1) (var zero)) A

     rawBridge :
       Deriv (imp (substF zero j Phi)
                   (substF zero (ap2 sub i i) Phi))
     rawBridge =
       substF_cong zero j (ap2 sub i i) (ruleSym sub_ii_eq_j) Phi

     -- rewrite both A-parts to  A .
     bridge1 :
       Deriv (imp (imp (eqF (ap1 thmT v1) j) A)
                   (substF zero (ap2 sub i i) Phi))
     bridge1 =
       eqSubst (\ X -> Deriv (imp (imp (eqF (ap1 thmT v1) j) X)
                                   (substF zero (ap2 sub i i) Phi)))
               (aNoop0 j)
               rawBridge

     bridge :
       Deriv (imp (imp (eqF (ap1 thmT v1) j) A) G_clean)
     bridge =
       eqSubst (\ X -> Deriv (imp (imp (eqF (ap1 thmT v1) j) A)
                                   (imp (eqF (ap1 thmT v1) (ap2 sub i i)) X)))
               (aNoop0 (ap2 sub i i))
               bridge1

     dG : Deriv G_clean
     dG = mp bridge dD

     ------------------------------------------------------------------
     -- Endgame :  necessitate dG , instantiate at var 1 := y , mp .

     y : Term
     y = encode dG

     eq1 : Deriv (eqF (ap1 thmT y) (codeFormula G_clean))
     eq1 = thmT_complete_rec dG

     -- codeFormula G_clean = sub(i,i)   (diag_term_eq via cG_eq).
     diag_clean : Deriv (eqF (ap2 sub i i) (codeFormula G_clean))
     diag_clean =
       eqSubst (\ z -> Deriv (eqF (ap2 sub i i) z)) cG_eq diag_term_eq

     thmTy_eq : Deriv (eqF (ap1 thmT y) (ap2 sub i i))
     thmTy_eq = ruleTrans eq1 (ruleSym diag_clean)

     -- instantiate  dG  at  var 1 := y .
     dG_inst0 : Deriv (substF (suc zero) y G_clean)
     dG_inst0 = ruleInst (suc zero) y dG

     -- substT 1 y (sub i i) = sub i i  (closed) .
     dG_inst1 :
       Deriv (imp (eqF (ap1 thmT y) (ap2 sub i i)) (substF (suc zero) y A))
     dG_inst1 =
       eqSubst (\ z -> Deriv (imp (eqF (ap1 thmT y) z) (substF (suc zero) y A)))
               (closedAt closed_sub_ii (suc zero) y)
               dG_inst0

     -- substF 1 y A = A .
     dG_inst :
       Deriv (imp (eqF (ap1 thmT y) (ap2 sub i i)) A)
     dG_inst =
       eqSubst (\ X -> Deriv (imp (eqF (ap1 thmT y) (ap2 sub i i)) X))
               (aNoop1 y)
               dG_inst1

   in mp dG_inst thmTy_eq

------------------------------------------------------------------------
-- Top-level (non-parametrised) statement of Loeb's theorem, with the
-- formula A and its two freshness witnesses made explicit arguments.

lobThm :
  (A : Formula)
  (nf0 : notFreeF zero A)
  (nf1 : notFreeF (suc zero) A) ->
  Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula A))) A) ->
  Deriv A
lobThm A nf0 nf1 hLob = lob A nf0 nf1 hLob

------------------------------------------------------------------------
-- LOEB with the MINIMAL freshness hypothesis : only the proof variable
-- (var 1) need be fresh for A ; the diagonal-slot condition is removed by
-- alpha-renaming.  Pick a fresh index  k >= 2 , k > maxVarF A , set
--  B = A[var k / var 0]  (so var 0 and var 1 are both fresh for B), run
--  lobThm  on B , and rename back.
--
-- The renaming round-trip is handled by the internal substitution functor
--  gproof = sb (k := var 0) (var 1)  at the proof-code level (thmT_at_sb +
--  sbfEq_codeFormula) ; the conclusion is moved from A to B by a single
--  ruleInst (var 0 := var k).

lobThm1 :
  (A : Formula)
  (nf1 : notFreeF (suc zero) A) ->
  Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula A))) A) ->
  Deriv A
lobThm1 A nf1 hLob =
  let
    -- A fresh index  k >= 2 , above every variable of A .
    k : Nat
    k = maxN (suc (suc zero)) (maxVarF A)

    le2k : NatLe (suc (suc zero)) k
    le2k = maxN-le-left (suc (suc zero)) (maxVarF A)

    leMaxk : NatLe (maxVarF A) k
    leMaxk = maxN-le-right (suc (suc zero)) (maxVarF A)

    le1k : NatLe (suc zero) k
    le1k = le-trans (le-suc (le-zero (suc zero))) le2k

    eqK0 : Eq (natEq k zero) false
    eqK0 = natEq-lt-false k zero le1k

    eqK1 : Eq (natEq k (suc zero)) false
    eqK1 = natEq-lt-false k (suc zero) le2k

    eq0k : Eq (natEq zero k) false
    eq0k = eqTrans (natEq_sym zero k) eqK0

    eq1k : Eq (natEq (suc zero) k) false
    eq1k = eqTrans (natEq_sym (suc zero) k) eqK1

    nfkA : notFreeF k A
    nfkA = notFree_above_F k A leMaxk

    -- The renamed sentence  B = A[var k / var 0] .
    B : Formula
    B = substF zero (var k) A

    nfB0 : notFreeF zero B
    nfB0 = notFree0_after_F k A eq0k

    nfB1 : notFreeF (suc zero) B
    nfB1 = notFree_preserve_F (suc zero) k A nf1 eq1k

    boxB : Formula
    boxB = atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula B))

    --------------------------------------------------------------------
    -- The proof-code substitution functor  gproof  (sb-wrap installing
    --  var k := var 0  on the proof  var 1 ).

    spec : Term
    spec = ap2 Pair (natCode k) (codeTerm (var zero))

    gproof : Term
    gproof = ap2 Pair (natCode tag_sb) (ap2 Pair spec (var (suc zero)))

    -- sbf spec (codeFormula B) =Deriv= codeFormula A  (renaming back, since
    --  substF k (var 0) B = A ).
    sbfToA : Deriv (eqF (ap2 sbf spec (codeFormula B)) (codeFormula A))
    sbfToA =
      eqSubst (\ z -> Deriv (eqF (ap2 sbf spec (codeFormula B)) (codeFormula z)))
              (substF_back k A nfkA)
              (sbfEq_codeFormula k (var zero) B)

    -- e1 :  boxB  ->  thmT(gproof) = codeFormula A .
    c1 : Deriv (imp boxB (eqF (ap1 thmT gproof)
                               (ap2 sbf spec (ap1 thmT (var (suc zero))))))
    c1 = impLift {boxB} (thmT_at_sb spec (var (suc zero)))

    c2 : Deriv (imp boxB (eqF (ap2 sbf spec (ap1 thmT (var (suc zero))))
                               (ap2 sbf spec (codeFormula B))))
    c2 = impCongR {boxB} sbf (ap1 thmT (var (suc zero))) (codeFormula B) spec
                  (impRefl boxB)

    c3 : Deriv (imp boxB (eqF (ap2 sbf spec (codeFormula B)) (codeFormula A)))
    c3 = impLift {boxB} sbfToA

    e1 : Deriv (imp boxB (eqF (ap1 thmT gproof) (codeFormula A)))
    e1 =
      impEqTrans {boxB}
        (ap1 thmT gproof) (ap2 sbf spec (codeFormula B)) (codeFormula A)
        (impEqTrans {boxB}
          (ap1 thmT gproof)
          (ap2 sbf spec (ap1 thmT (var (suc zero))))
          (ap2 sbf spec (codeFormula B))
          c1 c2)
        c3

    -- e2 :  thmT(gproof) = codeFormula A  ->  A   (Loeb hyp at gproof).
    hInst :
      Deriv (substF (suc zero) gproof
              (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula A))) A))
    hInst = ruleInst (suc zero) gproof hLob

    e2a :
      Deriv (imp (eqF (ap1 thmT gproof) (codeFormula A)) (substF (suc zero) gproof A))
    e2a =
      eqSubst (\ z -> Deriv (imp (eqF (ap1 thmT gproof) z) (substF (suc zero) gproof A)))
              (closedAt (closed_codeFormula A) (suc zero) gproof)
              hInst

    e2 : Deriv (imp (eqF (ap1 thmT gproof) (codeFormula A)) A)
    e2 =
      eqSubst (\ X -> Deriv (imp (eqF (ap1 thmT gproof) (codeFormula A)) X))
              (substF_notFree (suc zero) A gproof nf1)
              e2a

    -- e3 :  boxB -> A .
    e3 : Deriv (imp boxB A)
    e3 = impTrans e1 e2

    -- hLobB :  boxB -> B   (move conclusion A to B by  var 0 := var k ).
    hLobB : Deriv (imp boxB B)
    hLobB =
      eqSubst (\ z -> Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) z)) B))
              (closedAt (closed_codeFormula B) zero (var k))
              (ruleInst zero (var k) e3)

    -- Loeb for B (var 0, var 1 fresh) ; then rename back to A .
    dB : Deriv B
    dB = lobThm B nfB0 nfB1 hLobB
  in eqSubst (\ F -> Deriv F)
             (substF_back k A nfkA)
             (ruleInst k (var zero) dB)

------------------------------------------------------------------------
-- LOEB at an ARBITRARY proof-variable index  k , needing ONLY that  var k
-- is not free in A (no condition on var 1).
--
-- METHOD (with two scratch indices  m , l  fresh for A , distinct from
--  k , 1  and each other) :
--   B  = A[var m / var 1]      -- so  var 1  is not free in B
--   g  = sb((m, codeTerm(var 1)), var l)   -- proof-code functor with
--        thmT(g) =Deriv= sbf(spec)(thmT(var l)) , and under "var l proves B"
--        bridges  codeFormula B -> codeFormula A  (sbfEq_codeFormula +
--        the renaming round-trip  substF m (var 1) B = A).
--   The functor lives on the THIRD variable  var l , so neither
--   ruleInst(var k := g)  (no-op on A , var k fresh) nor
--   ruleInst(var 1 := var m)  (which turns the conclusion A into B)
--   disturbs it.  Assemble  box_l B -> B , ruleInst (var l := var 1) to
--   box_1 B -> B , apply  lobThm1 B , and rename B back to A .

lobThmK :
  (A : Formula) (k : Nat)
  (nfk : notFreeF k A) ->
  Deriv (imp (atomic (eqn (ap1 thmT (var k)) (codeFormula A))) A) ->
  Deriv A
lobThmK A k nfk hLobK =
  let
    -- Two scratch indices  m = M , l = suc M , both  >= 2 , > k , > maxVarF A .
    bigN : Nat
    bigN = maxN (suc (suc zero)) (maxN (suc k) (maxVarF A))

    m : Nat
    m = bigN

    l : Nat
    l = suc bigN

    le2m : NatLe (suc (suc zero)) m
    le2m = maxN-le-left (suc (suc zero)) (maxN (suc k) (maxVarF A))

    leMaxm : NatLe (maxVarF A) m
    leMaxm = le-trans (maxN-le-right (suc k) (maxVarF A))
                      (maxN-le-right (suc (suc zero)) (maxN (suc k) (maxVarF A)))

    leMaxl : NatLe (maxVarF A) l
    leMaxl = le-suc-right leMaxm

    -- Disequalities.
    eq1m : Eq (natEq (suc zero) m) false
    eq1m = eqTrans (natEq_sym (suc zero) m) (natEq-lt-false m (suc zero) le2m)

    eq1l : Eq (natEq (suc zero) l) false
    eq1l = eqTrans (natEq_sym (suc zero) l)
                   (natEq-lt-false l (suc zero) (le-suc-right le2m))

    eqlm : Eq (natEq l m) false
    eqlm = natEq-lt-false l m (le-refl (suc bigN))

    -- A's freshness facts at the scratch indices.
    nfmA : notFreeF m A
    nfmA = notFree_above_F m A leMaxm

    nflA : notFreeF l A
    nflA = notFree_above_F l A leMaxl

    -- The renamed sentence  B = A[var m / var 1]  (var 1 not free in B).
    B : Formula
    B = substF (suc zero) (var m) A

    nfB1 : notFreeF (suc zero) B
    nfB1 = notFree_self_after_F (suc zero) m A eq1m

    nflB : notFreeF l B
    nflB = notFree_preserve_at_F (suc zero) l m A nflA eqlm

    -- The proof-code functor  g = sb(spec, var l) , spec = (m, codeTerm(var 1)).
    spec : Term
    spec = ap2 Pair (natCode m) (codeTerm (var (suc zero)))

    gl : Term
    gl = ap2 Pair (natCode tag_sb) (ap2 Pair spec (var l))

    -- sbf spec (codeFormula B) =Deriv= codeFormula A   (renaming back).
    sbfToA : Deriv (eqF (ap2 sbf spec (codeFormula B)) (codeFormula A))
    sbfToA =
      eqSubst (\ z -> Deriv (eqF (ap2 sbf spec (codeFormula B)) (codeFormula z)))
              (substF_back_at (suc zero) m A nfmA)
              (sbfEq_codeFormula m (var (suc zero)) B)

    -- (1)  box_l B  ->  thmT(gl) = codeFormula A     (box_l B = thmT(var l) = code B).
    boxBl : Formula
    boxBl = atomic (eqn (ap1 thmT (var l)) (codeFormula B))

    c1 : Deriv (imp boxBl (eqF (ap1 thmT gl)
                                (ap2 sbf spec (ap1 thmT (var l)))))
    c1 = impLift {boxBl} (thmT_at_sb spec (var l))

    c2 : Deriv (imp boxBl (eqF (ap2 sbf spec (ap1 thmT (var l)))
                                (ap2 sbf spec (codeFormula B))))
    c2 = impCongR {boxBl} sbf (ap1 thmT (var l)) (codeFormula B) spec
                  (impRefl boxBl)

    c3 : Deriv (imp boxBl (eqF (ap2 sbf spec (codeFormula B)) (codeFormula A)))
    c3 = impLift {boxBl} sbfToA

    eFun : Deriv (imp boxBl (eqF (ap1 thmT gl) (codeFormula A)))
    eFun =
      impEqTrans {boxBl}
        (ap1 thmT gl) (ap2 sbf spec (codeFormula B)) (codeFormula A)
        (impEqTrans {boxBl}
          (ap1 thmT gl)
          (ap2 sbf spec (ap1 thmT (var l)))
          (ap2 sbf spec (codeFormula B))
          c1 c2)
        c3

    -- e2A :  thmT(gl) = codeFormula A  ->  A    (Loeb hyp at proof code gl).
    hInstK :
      Deriv (substF k gl
              (imp (atomic (eqn (ap1 thmT (var k)) (codeFormula A))) A))
    hInstK = ruleInst k gl hLobK

    -- substT k gl (var k) = gl   (natEq k k = true).
    r1k :
      Deriv (imp (atomic (eqn (ap1 thmT gl) (substT k gl (codeFormula A))))
                  (substF k gl A))
    r1k =
      eqSubst
        (\ b -> Deriv (imp (atomic (eqn (ap1 thmT (boolCase b gl (var k)))
                                         (substT k gl (codeFormula A))))
                            (substF k gl A)))
        (natEq-refl k)
        hInstK

    -- substT k gl (codeFormula A) = codeFormula A   (closed).
    r2k :
      Deriv (imp (atomic (eqn (ap1 thmT gl) (codeFormula A)))
                  (substF k gl A))
    r2k =
      eqSubst
        (\ z -> Deriv (imp (atomic (eqn (ap1 thmT gl) z)) (substF k gl A)))
        (closedAt (closed_codeFormula A) k gl)
        r1k

    -- substF k gl A = A   (var k not free in A).
    e2A : Deriv (imp (atomic (eqn (ap1 thmT gl) (codeFormula A))) A)
    e2A =
      eqSubst (\ X -> Deriv (imp (atomic (eqn (ap1 thmT gl) (codeFormula A))) X))
              (substF_notFree k A gl nfk)
              r2k

    -- box_l B -> A , then ruleInst (var 1 := var m) to get  box_l B -> B .
    eBlA : Deriv (imp boxBl A)
    eBlA = impTrans eFun e2A

    -- substT 1 (var m) (var l) = var l   (l /= 1).
    subLl : Eq (substT (suc zero) (var m) (var l)) (var l)
    subLl = eqSubst (\ b -> Eq (boolCase b (var m) (var l)) (var l))
                    (eqSym eq1l) refl

    -- ruleInst (var 1 := var m) on  box_l B -> A :  conclusion A becomes B ;
    -- the box's closed  codeFormula B  and the  var l  leaf are rewritten back.
    eBlB0 : Deriv (imp (atomic (eqn (ap1 thmT (substT (suc zero) (var m) (var l)))
                                     (substT (suc zero) (var m) (codeFormula B))))
                        B)
    eBlB0 = ruleInst (suc zero) (var m) eBlA

    eBlB1 : Deriv (imp (atomic (eqn (ap1 thmT (substT (suc zero) (var m) (var l)))
                                     (codeFormula B)))
                        B)
    eBlB1 =
      eqSubst (\ z -> Deriv (imp (atomic (eqn (ap1 thmT (substT (suc zero) (var m) (var l)))
                                               z)) B))
              (closedAt (closed_codeFormula B) (suc zero) (var m))
              eBlB0

    eBlB : Deriv (imp boxBl B)
    eBlB =
      eqSubst (\ z -> Deriv (imp (atomic (eqn (ap1 thmT z) (codeFormula B))) B))
              subLl
              eBlB1

    -- ruleInst (var l := var 1) :  box_1 B -> B .
    subLl2 : Eq (substT l (var (suc zero)) (var l)) (var (suc zero))
    subLl2 = eqSubst (\ b -> Eq (boolCase b (var (suc zero)) (var l)) (var (suc zero)))
                     (eqSym (natEq-refl l)) refl

    hB0 :
      Deriv (imp (atomic (eqn (ap1 thmT (substT l (var (suc zero)) (var l)))
                               (substT l (var (suc zero)) (codeFormula B))))
                  (substF l (var (suc zero)) B))
    hB0 = ruleInst l (var (suc zero)) eBlB

    hB1' :
      Deriv (imp (atomic (eqn (ap1 thmT (substT l (var (suc zero)) (var l)))
                               (codeFormula B)))
                  (substF l (var (suc zero)) B))
    hB1' =
      eqSubst (\ z -> Deriv (imp (atomic (eqn (ap1 thmT (substT l (var (suc zero)) (var l)))
                                               z)) (substF l (var (suc zero)) B)))
              (closedAt (closed_codeFormula B) l (var (suc zero)))
              hB0

    hB1 :
      Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula B)))
                  (substF l (var (suc zero)) B))
    hB1 =
      eqSubst (\ z -> Deriv (imp (atomic (eqn (ap1 thmT z) (codeFormula B)))
                                  (substF l (var (suc zero)) B)))
              subLl2
              hB1'

    hLobB1 :
      Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula B))) B)
    hLobB1 =
      eqSubst (\ X -> Deriv (imp (atomic (eqn (ap1 thmT (var (suc zero))) (codeFormula B))) X))
              (substF_notFree l B (var (suc zero)) nflB)
              hB1

    -- Loeb for B (var 1 fresh) ; rename  B = A[var m/var 1]  back to A .
    dB : Deriv B
    dB = lobThm1 B nfB1 hLobB1
  in eqSubst (\ F -> Deriv F)
             (substF_back_at (suc zero) m A nfmA)
             (ruleInst m (var (suc zero)) dB)
