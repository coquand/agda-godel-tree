{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.FnGlueAp2RcongRedex -- the erased R-node non-redex fact for the ap2 Rcong
-- dispatch, assembled by a SHAPE caseElim on the marked child's head:
--
--   redexErasedRcongO :
--     imp (neg (b = O))
--        (imp (Fst g = 8)
--        (imp (neg (Fst (mFun b) = 3))
--             (redexHere (tmAp2 g (erase a) (erase b)) = O)))
--
-- The marked child  b (= mMb sk)  is either an ap1 node (head 1) or an ap2 node
-- (head /= 1); either way erase b has head in {1,2} (/= 0) and fun-head Fst (mFun b),
-- so the erased R-node is not a redex (redex_ap2_Rcong_neg_ctx3).  The two shape
-- cases use the ap1 / ap2-neg object bridges of T4.FnEraseHeadImpNe (no reconTag2:
-- erase forks only on head 1, so neg (Fst b = 1) reaches the ap2 cell).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.FnGlueAp2RcongRedex where

open import T4.Base

open import T4.PrCodeObj using ( tmAp2 )
open import T4.FnErase using ( erase )
open import T4.FnMark using ( mFun )
open import T4.FnTerm using ( bfunhF ; redexHere )

open import T4.FnGlueAp2RcongHelpers using ( redex_ap2_Rcong_neg_ctx3 )
open import T4.FnEraseHeadImpNe
  using ( negEqTransport
        ; erasedHeadNe0_ap1_obj ; erasedBfunh_ap1_obj
        ; erasedHeadNe0_ap2_neg_obj ; erasedBfunh_ap2_neg_obj )

open import BRA3.ChurchCM using ( caseElim )
open import BRA3.Contrapositive using ( identP )
open import T4.CtxKit using ( lift4 ; get4a ; get4b ; get4c ; get4d ; ap4c )

------------------------------------------------------------------------

redexErasedRcongO : (g a b : Term) ->
  Deriv (imp (neg (eqF b O))
        (imp (eqF (ap1 Fst g) (natCode 8))
        (imp (neg (eqF (ap1 Fst (mFun b)) (natCode 3)))
             (eqF (ap1 redexHere (tmAp2 g (ap1 erase a) (ap1 erase b))) O))))
redexErasedRcongO g a b =
  let node : Term
      node = tmAp2 g (ap1 erase a) (ap1 erase b)
      P1 : Formula                                     -- Fst b = 1
      P1 = eqF (ap1 Fst b) (natCode 1)
      NE : Formula                                     -- neg (b = O)
      NE = neg (eqF b O)
      F8 : Formula                                     -- Fst g = 8
      F8 = eqF (ap1 Fst g) (natCode 8)
      NF : Formula                                     -- neg (Fst (mFun b) = 3)
      NF = neg (eqF (ap1 Fst (mFun b)) (natCode 3))
      Rf : Formula
      Rf = imp NE (imp F8 (imp NF (eqF (ap1 redexHere node) O)))
      -- given the erased head-ne0 + bfunh-eq facts (imp[4]), assemble the redex.
      assemble : (S : Formula) ->
        Deriv (imp S (imp NE (imp F8 (imp NF (neg (eqF (ap1 Fst (ap1 erase b)) (natCode 0))))))) ->
        Deriv (imp S (imp NE (imp F8 (imp NF (eqF (ap1 bfunhF node) (ap1 Fst (mFun b))))))) ->
        Deriv (imp S (imp NE (imp F8 (imp NF (eqF (ap1 redexHere node) O)))))
      assemble S headNe0 bfunhEq =
        let f8I : Deriv (imp S (imp NE (imp F8 (imp NF F8))))
            f8I = get4c S NE F8 NF
            bfunhNe3 : Deriv (imp S (imp NE (imp F8 (imp NF (neg (eqF (ap1 bfunhF node) (natCode 3)))))))
            bfunhNe3 = ap4c (ap4c (lift4 S NE F8 NF
                              (negEqTransport (ap1 bfunhF node) (ap1 Fst (mFun b)) 3)) bfunhEq)
                            (get4d S NE F8 NF)
        in ap4c (ap4c (ap4c (lift4 S NE F8 NF (redex_ap2_Rcong_neg_ctx3 g (ap1 erase a) (ap1 erase b)))
                       f8I) headNe0) bfunhNe3
      -- branch 1:  Fst b = 1  (ap1 shape).
      b1 : Deriv (imp P1 Rf)
      b1 =
        let headNe0 : Deriv (imp P1 (imp NE (imp F8 (imp NF
                        (neg (eqF (ap1 Fst (ap1 erase b)) (natCode 0)))))))
            headNe0 = ap4c (lift4 P1 NE F8 NF (erasedHeadNe0_ap1_obj b)) (get4a P1 NE F8 NF)
            bfunhEq : Deriv (imp P1 (imp NE (imp F8 (imp NF
                        (eqF (ap1 bfunhF node) (ap1 Fst (mFun b)))))))
            bfunhEq = ap4c (lift4 P1 NE F8 NF (erasedBfunh_ap1_obj b g (ap1 erase a))) (get4a P1 NE F8 NF)
        in assemble P1 headNe0 bfunhEq
      -- branch 2:  neg (Fst b = 1)  (ap2 shape; ne from NE).
      b2 : Deriv (imp (neg P1) Rf)
      b2 =
        let headNe0 : Deriv (imp (neg P1) (imp NE (imp F8 (imp NF
                        (neg (eqF (ap1 Fst (ap1 erase b)) (natCode 0)))))))
            headNe0 = ap4c (ap4c (lift4 (neg P1) NE F8 NF (erasedHeadNe0_ap2_neg_obj b))
                        (get4b (neg P1) NE F8 NF)) (get4a (neg P1) NE F8 NF)
            bfunhEq : Deriv (imp (neg P1) (imp NE (imp F8 (imp NF
                        (eqF (ap1 bfunhF node) (ap1 Fst (mFun b)))))))
            bfunhEq = ap4c (ap4c (lift4 (neg P1) NE F8 NF (erasedBfunh_ap2_neg_obj b g (ap1 erase a)))
                        (get4b (neg P1) NE F8 NF)) (get4a (neg P1) NE F8 NF)
        in assemble (neg P1) headNe0 bfunhEq
  in caseElim {X = P1} {Y = neg P1} {Rf = Rf} (identP (neg P1)) b1 b2
