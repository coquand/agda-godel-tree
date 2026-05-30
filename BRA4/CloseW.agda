{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CloseW -- closes the user's witness w at vars 0 and 1, via two
-- ruleInst applications + three structural-induction closure lemmas.
--
-- Lets BRA4.ChaitinG1CoreNumRaw expose the EXACT fixed target signature
--   CGI_core_num_raw :
--     (w x : Term) ->
--     Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)) ->
--     Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
-- without any closure-of-w hypotheses.   The trick:
--   1. ruleInst (suc zero) O hyp :  substitute  var 1 -> O  everywhere in
--      the user's Deriv.
--   2. ruleInst zero O on the result :  substitute  var 0 -> O .
-- The resulting Deriv is about  w' := substT 0 O (substT 1 O w) , which
-- by structural induction has  substT 0 a w' = w' ,  substT 1 a w' = w' ,
-- and  simSubstT 0 a 1 b w' = w'  -- exactly the three closure facts
-- DischargeKdef wants (via  k_max = ap2 gRec_of_kmax O (ap1 s w') ).

module BRA4.CloseW where

open import BRA4.Base

open import BRA3.RuleInst2 using ( simSubstT )

------------------------------------------------------------------------
-- The closing operation.

closeW : Term -> Term
closeW w = substT zero O (substT (suc zero) O w)

------------------------------------------------------------------------
-- LEMMA 1.   substT 0 a (closeW w)  =  closeW w .
--
-- The outer  substT 0 O  has eliminated every  var 0  occurrence; another
-- substT 0 a  hits no var 0 and is identity.   Proved by structural
-- induction on w.

cl_w_sub0 :
  (w : Term) (a : Term) -> Eq (substT zero a (closeW w)) (closeW w)
cl_w_sub0 O                       a = refl
cl_w_sub0 (var zero)              a = refl
cl_w_sub0 (var (suc zero))        a = refl
cl_w_sub0 (var (suc (suc m)))     a = refl
cl_w_sub0 (ap1 f t)               a =
  eqCong (ap1 f) (cl_w_sub0 t a)
cl_w_sub0 (ap2 g x y)             a =
  eqTrans (eqCong (\ z -> ap2 g z (substT zero a (substT zero O (substT (suc zero) O y))))
                  (cl_w_sub0 x a))
          (eqCong (\ z -> ap2 g (substT zero O (substT (suc zero) O x)) z)
                  (cl_w_sub0 y a))

------------------------------------------------------------------------
-- LEMMA 2.   substT 1 a (closeW w)  =  closeW w .
--
-- The inner  substT 1 O  has eliminated every  var 1  occurrence;  substT
-- 0 O  does not introduce  var 1  (it only inserts O, which has no vars);
-- substT 1 a  hits no var 1 and is identity.   Proved by structural
-- induction on w.

cl_w_sub1 :
  (w : Term) (a : Term) -> Eq (substT (suc zero) a (closeW w)) (closeW w)
cl_w_sub1 O                       a = refl
cl_w_sub1 (var zero)              a = refl
cl_w_sub1 (var (suc zero))        a = refl
cl_w_sub1 (var (suc (suc m)))     a = refl
cl_w_sub1 (ap1 f t)               a =
  eqCong (ap1 f) (cl_w_sub1 t a)
cl_w_sub1 (ap2 g x y)             a =
  eqTrans (eqCong (\ z -> ap2 g z (substT (suc zero) a (substT zero O (substT (suc zero) O y))))
                  (cl_w_sub1 x a))
          (eqCong (\ z -> ap2 g (substT zero O (substT (suc zero) O x)) z)
                  (cl_w_sub1 y a))

------------------------------------------------------------------------
-- LEMMA 3.   simSubstT 0 a 1 b (closeW w)  =  closeW w .
--
-- closeW w has no free  var 0  or  var 1 , so simSubstT (which only acts
-- at those two var positions) is identity.   Proved by structural
-- induction on w.

cl_w_sim :
  (w : Term) (a b : Term) -> Eq (simSubstT zero a (suc zero) b (closeW w)) (closeW w)
cl_w_sim O                       a b = refl
cl_w_sim (var zero)              a b = refl
cl_w_sim (var (suc zero))        a b = refl
cl_w_sim (var (suc (suc m)))     a b = refl
cl_w_sim (ap1 f t)               a b =
  eqCong (ap1 f) (cl_w_sim t a b)
cl_w_sim (ap2 g x y)             a b =
  eqTrans (eqCong (\ z -> ap2 g z (simSubstT zero a (suc zero) b
                                     (substT zero O (substT (suc zero) O y))))
                  (cl_w_sim x a b))
          (eqCong (\ z -> ap2 g (substT zero O (substT (suc zero) O x)) z)
                  (cl_w_sim y a b))
