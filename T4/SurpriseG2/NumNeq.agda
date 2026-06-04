{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.NumNeq -- numeral-discrimination utilities used by the
-- pigeonhole base case.
--
-- Two pieces:
--
--   s_neq_O  : (X : Term) -> Deriv (neg (eqF (ap1 s X) O))
--              -- the universal "successor is not zero" (ax_succ_nonzero
--              -- itself only covers  X := O ).
--
--   numNeq   : (i j : Nat) ->
--              Not (Eq i j) ->
--              Deriv (neg (eqF (natCode i) (natCode j)))
--              -- distinct meta-Nats give distinct BRA numerals.
--
-- Both are proved via the standard  axContrapos +  isZero  /  predecessor
-- discriminators.  No new mathematics.

module T4.SurpriseG2.NumNeq where

open import T4.Base
open import BRA3.Logic         using ( impTrans ; eqSymImp ; prependEqLeft
                                      ; appendEqRight )
open import BRA3.Contrapositive using ( axContrapos ; liftP )
open import BRA3.Church        using ( isZero ; TisZeroZ ; TisZeroSucc
                                      ; predecessor ; T_p_S_v0 )

------------------------------------------------------------------------
-- Meta-level negation (Empty / emptyElim come from BRA3.Base via Base).

Not : Set -> Set
Not P = P -> Empty

------------------------------------------------------------------------
-- Universal successor-nonzero.
--
-- Strategy: build  imp (s X = O) (s O = O)  via  cong1 isZero  +
-- TisZeroZ / TisZeroSucc , then  axContrapos  +  ax_succ_nonzero .

s_neq_O : (X : Term) -> Deriv (neg (eqF (ap1 s X) O))
s_neq_O X =
  let -- isZero(s X) = O .
      isZ_sX : Deriv (eqF (ap1 isZero (ap1 s X)) O)
      isZ_sX = ruleInst 0 X TisZeroSucc

      -- step1 :  imp (s X = O) (isZero (s X) = isZero O) .
      step1 : Deriv (imp (eqF (ap1 s X) O)
                          (eqF (ap1 isZero (ap1 s X)) (ap1 isZero O)))
      step1 = ax_eqCong1 isZero (ap1 s X) O

      -- step2 :  imp (isZero (s X) = isZero O) (O = isZero O) .
      step2 : Deriv (imp (eqF (ap1 isZero (ap1 s X)) (ap1 isZero O))
                          (eqF O (ap1 isZero O)))
      step2 = prependEqLeft O (ap1 isZero (ap1 s X)) (ap1 isZero O)
                              (ruleSym isZ_sX)

      -- step3 :  imp (O = isZero O) (O = s O) .
      step3 : Deriv (imp (eqF O (ap1 isZero O)) (eqF O (ap1 s O)))
      step3 = appendEqRight O (ap1 isZero O) (ap1 s O) TisZeroZ

      -- step4 :  imp (O = s O) (s O = O) .
      step4 : Deriv (imp (eqF O (ap1 s O)) (eqF (ap1 s O) O))
      step4 = eqSymImp O (ap1 s O)

      -- chain :  imp (s X = O) (s O = O) .
      chain : Deriv (imp (eqF (ap1 s X) O) (eqF (ap1 s O) O))
      chain = impTrans (impTrans (impTrans step1 step2) step3) step4

      -- contra :  imp (neg (s O = O)) (neg (s X = O)) .
      contra : Deriv (imp (neg (eqF (ap1 s O) O))
                          (neg (eqF (ap1 s X) O)))
      contra = mp (axContrapos (eqF (ap1 s X) O) (eqF (ap1 s O) O)) chain
  in mp contra ax_succ_nonzero

------------------------------------------------------------------------
-- Symmetric variant : O =/= s X .

O_neq_s : (X : Term) -> Deriv (neg (eqF O (ap1 s X)))
O_neq_s X =
  let -- imp (O = s X) (s X = O) .
      flip : Deriv (imp (eqF O (ap1 s X)) (eqF (ap1 s X) O))
      flip = eqSymImp O (ap1 s X)

      -- imp (neg (s X = O)) (neg (O = s X)) .
      contra : Deriv (imp (neg (eqF (ap1 s X) O))
                          (neg (eqF O (ap1 s X))))
      contra = mp (axContrapos (eqF O (ap1 s X)) (eqF (ap1 s X) O)) flip
  in mp contra (s_neq_O X)

------------------------------------------------------------------------
-- s-injectivity inside Deriv :  s a = s b  -> a = b .
-- Proof via  cong1 predecessor  +  T_p_S_v0  (instantiated twice).

s_inj : (a b : Term) ->
        Deriv (eqF (ap1 s a) (ap1 s b)) -> Deriv (eqF a b)
s_inj a b h =
  let -- predecessor(s a) = predecessor(s b) .
      cong_h : Deriv (eqF (ap1 predecessor (ap1 s a))
                          (ap1 predecessor (ap1 s b)))
      cong_h = cong1 predecessor h

      pSa_eq_a : Deriv (eqF (ap1 predecessor (ap1 s a)) a)
      pSa_eq_a = ruleInst 0 a T_p_S_v0

      pSb_eq_b : Deriv (eqF (ap1 predecessor (ap1 s b)) b)
      pSb_eq_b = ruleInst 0 b T_p_S_v0
  in ruleTrans (ruleSym pSa_eq_a) (ruleTrans cong_h pSb_eq_b)

------------------------------------------------------------------------
-- numNeq : distinct meta-Nats give distinct BRA numerals.
--
-- By simultaneous meta-induction on (i, j).  The (suc, suc) case
-- peels one  s  via  cong1 predecessor  and recurses.

numNeq : (i j : Nat) ->
         Not (Eq i j) ->
         Deriv (neg (eqF (natCode i) (natCode j)))
numNeq zero    zero    ne = emptyElim (ne refl)
numNeq zero    (suc m) ne = O_neq_s (natCode m)
numNeq (suc n) zero    ne = s_neq_O (natCode n)
numNeq (suc n) (suc m) ne =
  let -- Recursive IH : neg (eqF (natCode n) (natCode m)) , for n /= m .
      ne_pred : Not (Eq n m)
      ne_pred eq = ne (eqCong suc eq)

      ih : Deriv (neg (eqF (natCode n) (natCode m)))
      ih = numNeq n m ne_pred

      -- step1 :  imp (s natCode n = s natCode m) (natCode n = natCode m) .
      sInjImp : Deriv (imp (eqF (ap1 s (natCode n)) (ap1 s (natCode m)))
                           (eqF (natCode n) (natCode m)))
      sInjImp =
        let -- ax_eqCong1 predecessor (s nc_n) (s nc_m) :
            --   imp (s nc_n = s nc_m) (p (s nc_n) = p (s nc_m)) .
            cstep : Deriv (imp (eqF (ap1 s (natCode n)) (ap1 s (natCode m)))
                               (eqF (ap1 predecessor (ap1 s (natCode n)))
                                    (ap1 predecessor (ap1 s (natCode m)))))
            cstep = ax_eqCong1 predecessor (ap1 s (natCode n)) (ap1 s (natCode m))

            pSn_eq_n : Deriv (eqF (ap1 predecessor (ap1 s (natCode n))) (natCode n))
            pSn_eq_n = ruleInst 0 (natCode n) T_p_S_v0

            pSm_eq_m : Deriv (eqF (ap1 predecessor (ap1 s (natCode m))) (natCode m))
            pSm_eq_m = ruleInst 0 (natCode m) T_p_S_v0

            -- imp (p (s nc_n) = p (s nc_m)) (nc_n = p (s nc_m)) .
            replaceL : Deriv (imp (eqF (ap1 predecessor (ap1 s (natCode n)))
                                       (ap1 predecessor (ap1 s (natCode m))))
                                  (eqF (natCode n)
                                       (ap1 predecessor (ap1 s (natCode m)))))
            replaceL = prependEqLeft (natCode n)
                                      (ap1 predecessor (ap1 s (natCode n)))
                                      (ap1 predecessor (ap1 s (natCode m)))
                                      (ruleSym pSn_eq_n)

            -- imp (nc_n = p (s nc_m)) (nc_n = nc_m) .
            replaceR : Deriv (imp (eqF (natCode n) (ap1 predecessor (ap1 s (natCode m))))
                                  (eqF (natCode n) (natCode m)))
            replaceR = appendEqRight (natCode n)
                                      (ap1 predecessor (ap1 s (natCode m)))
                                      (natCode m)
                                      pSm_eq_m
        in impTrans cstep (impTrans replaceL replaceR)

      -- contra :  imp (neg (nc_n = nc_m)) (neg (s nc_n = s nc_m)) .
      contra : Deriv (imp (neg (eqF (natCode n) (natCode m)))
                          (neg (eqF (ap1 s (natCode n)) (ap1 s (natCode m)))))
      contra = mp (axContrapos (eqF (ap1 s (natCode n)) (ap1 s (natCode m)))
                               (eqF (natCode n) (natCode m)))
                  sInjImp
  in mp contra ih
