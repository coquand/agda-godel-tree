{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KdefConjRecog -- BLOCK 4, part 1: the recognition bridge at the
-- TWO-SLOT conjunction K-shape  Kfunctor(num x0, r)  of surprise-GII.
--
-- This is the num-raw analog of  T4.KdefRecog , re-pointed from the
-- single-atom  Kcode L / Kdef L x  (T4.Kdef) to the big-conjunction
--
--   KCode enum N a  =  /\_{j<=N} cNeg (definePCode j a)
--
-- (T4.DefinePExp), whose subject  a  rides in the  ap1 num a  data slot
-- of EACH conjunct.   The recogniser machinery of  T4.KdefRecog  is GENERIC
-- in the code-builder  ( Kcode L : Fun1 )  and the projector  ( out : Fun1 );
-- the ONLY shape-specific ingredient is  outKdef_correct .   So this file
-- ships exactly that ingredient at the conjunction shape and then re-derives
-- the four recogniser facts ( eval / le_one / dNeg / fires ) verbatim.
--
--   * KcodeConj N : Fun1   -- the curried code-builder  ap1 (KcodeConj N) a
--       = ap2 (Kfunctor N) a O = KCode N a   (the conjunction is  r -free; the
--       second  Fun2  slot is fed the dummy  O ).
--   * outKdefConj N : Fun1 = decode . projConj N . thmT   -- reads the subject
--       a  back out of the FIRST ( highest-index ) conjunct's  num a  slot.
--   * outKdefConj_correct :  thmT w = ap1 (KcodeConj N) x'  ==>  outKdefConj N w = x'
--       -- num-raw, NO isNat ( the slot is  num x' , decode (num x') = x' ).
--   * hitKdefConj / *_eval / *_le_one / dNeg_from_hitKdefConj / hitKdefConj_fires
--       -- the recogniser, exactly as  T4.KdefRecog  but at the conjunction shape.

module T4.KdefConjRecog where

open import T4.Base
open import T4.Tags using ( tag_neg ; tag_imp ; tag_eq ; tag_ap1 ; tag_ap2 )
open import T4.Code using ( codeFun1 ; codeFun2 )
open import T4.Num  using ( num )
open import T4.ThmT using ( thmT )
open import T4.Kdef using ( runProg )
open import T4.Decode using ( decode ; decode_num_id_at )
open import T4.CountingObj using ( eqIndF ; eqIndF_eq )
open import T4.Counting    using ( eqInd ; eqInd_le_one )
open import T4.Bridge      using ( eqInd_sound )
open import T4.KFire       using ( eqInd_at_eq )

import T4.DefinePExp as DP

open import BRA3.Church      using ( sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.Logic       using ( prependEqLeft )
open import BRA3.PairAlgebra using ( compose1U ; compose1U_eq ; axComp )

-- enum : the enumerator of Berry's finite program set (Fun1 must be in scope
-- BEFORE the telescope, so the section parameter lives in an inner module).
module _ (enum : Fun1) where

  ------------------------------------------------------------------------
  -- Local abbreviations for the  enum -fixed  DefinePExp  family.

 KCode : Nat -> Term -> Term
 KCode = DP.KCode enum

 negDefineCode : Nat -> Term -> Term
 negDefineCode = DP.negDefineCode enum

 definePCode : Nat -> Term -> Term
 definePCode = DP.definePCode enum

 pcodeOf : Nat -> Term
 pcodeOf = DP.pcodeOf enum

 Kfunctor : Nat -> Fun2
 Kfunctor = DP.Kfunctor enum

 Kfunctor_code :
   (N : Nat) (a b : Term) ->
   Deriv (eqF (ap2 (Kfunctor N) a b) (KCode N a))
 Kfunctor_code = DP.Kfunctor_code enum

 ------------------------------------------------------------------------
 -- SECTION 1.  The curried code-builder  KcodeConj N : Fun1 .
 --   ap1 (KcodeConj N) a = ap2 (Kfunctor N) (u a) (constN 0 a) = ap2 (Kfunctor N) a O
 --                       = KCode N a .

 KcodeConj : Nat -> Fun1
 KcodeConj N = C (Kfunctor N) u (constN zero)

 KcodeConj_eval :
   (N : Nat) (a : Term) ->
   Deriv (eqF (ap1 (KcodeConj N) a) (KCode N a))
 KcodeConj_eval N a =
   let s1 : Deriv (eqF (ap1 (KcodeConj N) a)
                       (ap2 (Kfunctor N) (ap1 u a) (ap1 (constN zero) a)))
       s1 = ax_C (Kfunctor N) u (constN zero) a

       s2 : Deriv (eqF (ap2 (Kfunctor N) (ap1 u a) (ap1 (constN zero) a))
                       (ap2 (Kfunctor N) a (ap1 (constN zero) a)))
       s2 = congL (Kfunctor N) (ap1 (constN zero) a) (ax_u a)

       s3 : Deriv (eqF (ap2 (Kfunctor N) a (ap1 (constN zero) a))
                       (ap2 (Kfunctor N) a (natCode zero)))
       s3 = congR (Kfunctor N) a (constN_eq zero a)

       s4 : Deriv (eqF (ap2 (Kfunctor N) a (natCode zero)) (KCode N a))
       s4 = Kfunctor_code N a (natCode zero)
   in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

 ------------------------------------------------------------------------
 -- SECTION 2.  The atom projector  projAtom -- reads  num a  out of one conjunct
 --   negDefineCode j a = cNeg (cEqTm (cAp2f runProg (pcodeOf j) (num a)) (cAp1f s (natCode j)))
 --                     = Pair(tag_neg, Pair(tag_eq, Pair( Pair(tag_ap2, Pair(cf2, Pair(pcodeOf j, num a))), _ )))
 -- so the path to  num a  is  Snd ; Snd ; Fst ; Snd ; Snd ; Snd .

 projAtom : Fun1
 projAtom =
   compose1U Snd
     (compose1U Snd
       (compose1U Snd
         (compose1U Fst
           (compose1U Snd Snd))))

 projAtom_at :
   (j : Nat) (a : Term) ->
   Deriv (eqF (ap1 projAtom (negDefineCode j a)) (ap1 num a))
 projAtom_at j a =
   let t0 : Term                         -- negDefineCode j a
       t0 = negDefineCode j a

       atomL : Term                      -- cAp2f runProg (pcodeOf j) (num a)
       atomL = ap2 Pair (natCode tag_ap2)
                 (ap2 Pair (codeFun2 runProg) (ap2 Pair (pcodeOf j) (ap1 num a)))
       atomR : Term                      -- cAp1f s (natCode j)
       atomR = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 s) (natCode j))

       P4 : Term                         -- Pair(pcodeOf j, num a)
       P4 = ap2 Pair (pcodeOf j) (ap1 num a)
       P3 : Term                         -- Pair(codeFun2 runProg, P4)
       P3 = ap2 Pair (codeFun2 runProg) P4
       P2 : Term                         -- Pair(atomL, atomR)
       P2 = ap2 Pair atomL atomR

       inner : Fun1
       inner = compose1U Snd Snd
       c2 : Fun1
       c2 = compose1U Fst inner
       c3 : Fun1
       c3 = compose1U Snd c2
       c4 : Fun1
       c4 = compose1U Snd c3

       inner_eq : Deriv (eqF (ap1 inner t0) P2)
       inner_eq =
         ruleTrans (compose1U_eq Snd Snd t0)
           (ruleTrans (cong1 Snd (axSnd (natCode tag_neg) (definePCode j a)))
                      (axSnd (natCode tag_eq) P2))

       c2_eq : Deriv (eqF (ap1 c2 t0) atomL)
       c2_eq =
         ruleTrans (compose1U_eq Fst inner t0)
           (ruleTrans (cong1 Fst inner_eq)
                      (axFst atomL atomR))

       c3_eq : Deriv (eqF (ap1 c3 t0) P3)
       c3_eq =
         ruleTrans (compose1U_eq Snd c2 t0)
           (ruleTrans (cong1 Snd c2_eq)
                      (axSnd (natCode tag_ap2) P3))

       c4_eq : Deriv (eqF (ap1 c4 t0) P4)
       c4_eq =
         ruleTrans (compose1U_eq Snd c3 t0)
           (ruleTrans (cong1 Snd c3_eq)
                      (axSnd (codeFun2 runProg) P4))
   in ruleTrans (compose1U_eq Snd c4 t0)
        (ruleTrans (cong1 Snd c4_eq)
                   (axSnd (pcodeOf j) (ap1 num a)))

 ------------------------------------------------------------------------
 -- SECTION 3.  The conjunction projector  projConj N .
 --   N = 0 :  KCode 0 a = negDefineCode 0 a , so  projConj 0 = projAtom .
 --   N = suc n :  KCode (suc n) a = cAnd (negDefineCode (suc n) a) (KCode n a)
 --               = Pair(tag_neg, Pair(tag_imp, Pair( negDefineCode (suc n) a , Pair(tag_neg, KCode n a))));
 --     strip to the head conjunct by  Fst ; Snd ; Snd , then  projAtom .

 headProj : Fun1
 headProj = compose1U Fst (compose1U Snd Snd)

 headProj_at :
   (X Y : Term) ->
   Deriv (eqF (ap1 headProj (ap2 Pair (natCode tag_neg)
                              (ap2 Pair (natCode tag_imp)
                                (ap2 Pair X (ap2 Pair (natCode tag_neg) Y)))))
              X)
 headProj_at X Y =
   let cAndXY : Term
       cAndXY = ap2 Pair (natCode tag_neg)
                  (ap2 Pair (natCode tag_imp)
                    (ap2 Pair X (ap2 Pair (natCode tag_neg) Y)))
       Z : Term
       Z = ap2 Pair (natCode tag_imp) (ap2 Pair X (ap2 Pair (natCode tag_neg) Y))
       W : Term
       W = ap2 Pair X (ap2 Pair (natCode tag_neg) Y)

       ssEq : Deriv (eqF (ap1 (compose1U Snd Snd) cAndXY) W)
       ssEq = ruleTrans (compose1U_eq Snd Snd cAndXY)
                (ruleTrans (cong1 Snd (axSnd (natCode tag_neg) Z))
                           (axSnd (natCode tag_imp) W))
   in ruleTrans (compose1U_eq Fst (compose1U Snd Snd) cAndXY)
        (ruleTrans (cong1 Fst ssEq)
                   (axFst X (ap2 Pair (natCode tag_neg) Y)))

 projConj : Nat -> Fun1
 projConj zero    = projAtom
 projConj (suc n) = compose1U projAtom headProj

 projConj_at :
   (N : Nat) (a : Term) ->
   Deriv (eqF (ap1 (projConj N) (KCode N a)) (ap1 num a))
 projConj_at zero    a = projAtom_at zero a
 projConj_at (suc n) a =
   ruleTrans (compose1U_eq projAtom headProj (KCode (suc n) a))
     (ruleTrans (cong1 projAtom (headProj_at (negDefineCode (suc n) a) (KCode n a)))
                (projAtom_at (suc n) a))

 ------------------------------------------------------------------------
 -- SECTION 4.  The subject projector  outKdefConj  and its num-raw correctness.

 outKdefConj : Nat -> Fun1
 outKdefConj N = compose1U decode (compose1U (projConj N) thmT)

 outKdefConj_correct :
   (N : Nat) (w x' : Term) ->
   Deriv (eqF (ap1 thmT w) (ap1 (KcodeConj N) x')) ->
   Deriv (eqF (ap1 (outKdefConj N) w) x')
 outKdefConj_correct N w x' matched =
   let e1 : Deriv (eqF (ap1 (outKdefConj N) w)
                       (ap1 decode (ap1 (compose1U (projConj N) thmT) w)))
       e1 = compose1U_eq decode (compose1U (projConj N) thmT) w

       e2 : Deriv (eqF (ap1 (compose1U (projConj N) thmT) w)
                       (ap1 (projConj N) (ap1 thmT w)))
       e2 = compose1U_eq (projConj N) thmT w

       -- thmT w = ap1 (KcodeConj N) x' = KCode N x'  ; project to  num x' .
       e3 : Deriv (eqF (ap1 (projConj N) (ap1 thmT w)) (ap1 num x'))
       e3 = ruleTrans (cong1 (projConj N) (ruleTrans matched (KcodeConj_eval N x')))
                      (projConj_at N x')

       e4 : Deriv (eqF (ap1 decode (ap1 num x')) x')
       e4 = decode_num_id_at x'
   in ruleTrans e1 (ruleTrans (cong1 decode (ruleTrans e2 e3)) e4)

 ------------------------------------------------------------------------
 -- SECTION 5.  The recogniser indicator (generic; mirrors T4.KdefRecog).

 hitKdefConj : Nat -> Fun1 -> Fun1
 hitKdefConj N out = C eqIndF thmT (compose1U (KcodeConj N) out)

 hitKdefConj_eval :
   (N : Nat) (out : Fun1) (w : Term) ->
   Deriv (eqF (ap1 (hitKdefConj N out) w)
              (eqInd (ap1 thmT w) (ap1 (KcodeConj N) (ap1 out w))))
 hitKdefConj_eval N out w =
   ruleTrans (ax_C eqIndF thmT (compose1U (KcodeConj N) out) w)
     (ruleTrans (congR eqIndF (ap1 thmT w) (axComp (KcodeConj N) out w))
                (eqIndF_eq (ap1 thmT w) (ap1 (KcodeConj N) (ap1 out w))))

 hitKdefConj_le_one :
   (N : Nat) (out : Fun1) (w : Term) ->
   Deriv (leq (ap1 (hitKdefConj N out) w) (ap1 s O))
 hitKdefConj_le_one N out w =
   let c0 : Term
       c0 = ap1 (hitKdefConj N out) w
       c1 : Term
       c1 = eqInd (ap1 thmT w) (ap1 (KcodeConj N) (ap1 out w))
       rw : Deriv (imp (leq c1 (ap1 s O)) (leq c0 (ap1 s O)))
       rw = prependEqLeft (ap2 sub c0 (ap1 s O)) (ap2 sub c1 (ap1 s O)) O
              (congL sub (ap1 s O) (hitKdefConj_eval N out w))
   in mp rw (eqInd_le_one (ap1 thmT w) (ap1 (KcodeConj N) (ap1 out w)))

 ------------------------------------------------------------------------
 -- SECTION 6.  Firing  ==>  dNeg .  Subject  x' := ap1 out w0 .

 dNeg_from_hitKdefConj :
   (N : Nat) (out : Fun1) (w0 : Term) ->
   Deriv (eqF (ap1 (hitKdefConj N out) w0) (ap1 s O)) ->
   Deriv (eqF (ap1 thmT w0) (ap1 (KcodeConj N) (ap1 out w0)))
 dNeg_from_hitKdefConj N out w0 h =
   let match : Deriv (eqF (eqInd (ap1 thmT w0) (ap1 (KcodeConj N) (ap1 out w0)))
                          (ap1 s O))
       match = ruleTrans (ruleSym (hitKdefConj_eval N out w0)) h
   in eqInd_sound (ap1 thmT w0) (ap1 (KcodeConj N) (ap1 out w0)) match

 ------------------------------------------------------------------------
 -- SECTION 7.  The other direction: a provability hypothesis fires the recogniser.

 hitKdefConj_fires :
   (N : Nat) (w x : Term) ->
   Deriv (eqF (ap1 thmT w) (ap1 (KcodeConj N) x)) ->
   Deriv (eqF (ap1 (hitKdefConj N (outKdefConj N)) w) (ap1 s O))
 hitKdefConj_fires N w x hyp =
   let A : Term
       A = ap1 thmT w
       B : Term
       B = ap1 (KcodeConj N) (ap1 (outKdefConj N) w)
       bIsKx : Deriv (eqF B (ap1 (KcodeConj N) x))
       bIsKx = cong1 (KcodeConj N) (outKdefConj_correct N w x hyp)
   in ruleTrans (hitKdefConj_eval N (outKdefConj N) w)
        (ruleTrans (ruleSym (eqIndF_eq A B))
          (ruleTrans (congL eqIndF B hyp)
            (ruleTrans (congR eqIndF (ap1 (KcodeConj N) x) bIsKx)
              (ruleTrans (eqIndF_eq (ap1 (KcodeConj N) x) (ap1 (KcodeConj N) x))
                (eqInd_at_eq (ap1 (KcodeConj N) x))))))
