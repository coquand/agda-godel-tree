{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.HeadClash -- the OBJECT constructor-distinctness atom: the coded
-- constructors  ze#  and  su# X  are provably DISTINCT in BRA,
--
--     negZeSu : (X : Term) -> Deriv (neg (eqF ze# (su# X)))
--
-- i.e. the object  0 != s0  lifted to the term coding.  This is the object
-- analog of the meta  zeNeqSu (T4.ParHeadline) and the object core of the
-- Church-Rosser headline clash (attempt3 §2d).
--
-- Proof: an equation  ze# = su# X  would force the head tags equal,
-- tagZe = tagSu  i.e.  O = s O  (by congruence on  Fst  + hd_ze / hd_su),
-- contradicting  ax_succ_nonzero : neg (eqF (s O) O).  Pure object logic:
-- build  imp (ze# = su# X) (s O = O)  then contrapose against
-- ax_succ_nonzero.

module T4.HeadClash where

open import T4.Base

open import T4.TrsCodeObj using ( ze# ; su# ; tagZe ; tagSu ; hd ; hd_ze ; hd_su )

open import BRA3.Classical     using ( axContrapos )
open import BRA3.Contrapositive using ( bComb )

------------------------------------------------------------------------
-- Implication composition (B-combinator) from axS / axK.

impTrans : {A B Cf : Formula} ->
           Deriv (imp A B) -> Deriv (imp B Cf) -> Deriv (imp A Cf)
impTrans {A} {B} {Cf} f g =
  mp (mp (axS A B Cf) (mp (axK (imp B Cf) A) g)) f

------------------------------------------------------------------------
-- Object distinctness of the coded constructors.

negZeSu : (X : Term) -> Deriv (neg (eqF ze# (su# X)))
negZeSu X =
  let H : Formula
      H = eqF ze# (su# X)
      Q : Formula                       -- the atom  ax_succ_nonzero  negates
      Q = eqF tagSu tagZe               -- = eqF (ap1 s O) O

      a : Term
      a = hd ze#                        -- = ap1 Fst ze#
      b : Term
      b = hd (su# X)                    -- = ap1 Fst (su# X)

      -- M :  ze# = su# X  ->  hd ze# = hd (su# X)   (congruence on Fst).
      congFst : Deriv (imp H (eqF a b))
      congFst = ax_eqCong1 Fst ze# (su# X)

      -- imp (a = b) (b = tagZe)   using  hd_ze : a = tagZe .
      impMbO : Deriv (imp (eqF a b) (eqF b tagZe))
      impMbO =
        bComb (ax_eqTrans a b tagZe) (mp (axK (eqF a tagZe) (eqF a b)) hd_ze)

      -- imp (b = tagZe) (tagSu = tagZe)   using  hd_su : b = tagSu .
      impTags : Deriv (imp (eqF b tagZe) (eqF tagSu tagZe))
      impTags = mp (ax_eqTrans b tagSu tagZe) (hd_su X)

      -- imp H Q   by composition.
      impHQ : Deriv (imp H Q)
      impHQ = impTrans congFst (impTrans impMbO impTags)

  in mp (mp (axContrapos H Q) impHQ) ax_succ_nonzero
