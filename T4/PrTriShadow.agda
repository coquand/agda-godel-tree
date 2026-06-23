{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrTriShadow -- the META SHADOW of the triangle map and the bridge
--   triShadowU : triF (codeDer d) = codeDer (triMeta d)
-- generalising T4.TriPresShadow / DerTriShadow.  The shadow FULLY shadows the
-- fun-code structure (Fun1M / Fun2M, mutually recursive) so that (a) triMeta can
-- dispatch on the carried function and the right child by Agda pattern matching,
-- and (b) the residual congruences a redex triangle creates (over the redex's
-- own arbitrary funs g/h1/h2) are representable as shadow congruences.
-- triShadowU is one structural induction chaining the 15 object triF equations.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrTriShadow where

open import T4.Base

open import T4.PrDerCode
  using ( derLeaf ; ap1c ; ap2c ; derO ; derU ; derV ; derC ; derRb ; derRs
        ; dgAp1c ; dgAp2c ; dgRo ; dgRu ; dgRv ; dgRC ; dgRb ; dgRs ; filler ; bun3 )
open import T4.PrCodeObj
  using ( cSuc ; cZero ; cId ; cComp ; cProj ; cRec
        ; tgSuc ; tgZero ; tgId ; tgComp ; tgProj )
open import T4.PrTri
  using ( triF ; triF_reflO
        ; triF_ap1c_s ; triF_ap1c_o ; triF_ap1c_u ; triF_ap1c_C
        ; triF_ap2c_v ; triF_O ; triF_U ; triF_V ; triF_C ; triF_Rb ; triF_Rs )
open import T4.PrTri2
  using ( triF_ap2c_Rb ; triF_ap2c_Rs
        ; triF_ap2c_Rcong_notAp1c ; triF_ap2c_Rcong_ap1cNotSuc )

open import T4.BinTree using ( binNode )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------
-- SECTION 1.  Mutually-recursive fun-code shadows.

data Fun1M : Set
data Fun2M : Set

data Fun1M where
  f1S    : Fun1M
  f1Zero : Fun1M
  f1Id   : Fun1M
  f1Comp : Fun2M -> Fun1M -> Fun1M -> Fun1M   -- C g h1 h2 : g Fun2, h1 h2 Fun1

data Fun2M where
  f2Proj : Fun2M
  f2Rec  : Fun1M -> Fun2M -> Fun2M -> Fun2M    -- R g h1 h2 : g Fun1, h1 h2 Fun2

codeF1 : Fun1M -> Term
codeF2 : Fun2M -> Term
codeF1 f1S              = cSuc
codeF1 f1Zero           = cZero
codeF1 f1Id             = cId
codeF1 (f1Comp g h1 h2) = cComp (codeF2 g) (codeF1 h1) (codeF1 h2)
codeF2 f2Proj           = cProj
codeF2 (f2Rec g h1 h2)  = cRec (codeF1 g) (codeF2 h1) (codeF2 h2)

------------------------------------------------------------------------
-- SECTION 2.  Refined derivation shadow.

data DerM : Set where
  mRefl : DerM
  mAp1c : Fun1M -> DerM -> DerM
  mAp2c : Fun2M -> DerM -> DerM -> DerM
  mO    : DerM -> DerM
  mU    : DerM -> DerM
  mV    : DerM -> DerM -> DerM
  mC    : Fun2M -> Fun1M -> Fun1M -> DerM -> DerM
  mRb   : Fun1M -> Fun2M -> Fun2M -> DerM -> DerM
  mRs   : Fun1M -> Fun2M -> Fun2M -> DerM -> DerM -> DerM

codeDer : DerM -> Term
codeDer mRefl           = derLeaf
codeDer (mAp1c fm d)    = ap1c (codeF1 fm) (codeDer d)
codeDer (mAp2c fm d1 d2) = ap2c (codeF2 fm) (codeDer d1) (codeDer d2)
codeDer (mO d)          = derO (codeDer d)
codeDer (mU d)          = derU (codeDer d)
codeDer (mV d1 d2)      = derV (codeDer d1) (codeDer d2)
codeDer (mC g h1 h2 d)  = derC (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d)
codeDer (mRb g h1 h2 d) = derRb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d)
codeDer (mRs g h1 h2 d1 d2) = derRs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2)

------------------------------------------------------------------------
-- SECTION 3.  The shadow triangle map (mirrors the object triF cell exactly).

triMeta : DerM -> DerM
triMeta mRefl                       = mRefl
triMeta (mAp1c f1S d)               = mAp1c f1S (triMeta d)
triMeta (mAp1c f1Zero d)            = mO (triMeta d)
triMeta (mAp1c f1Id d)              = mU (triMeta d)
triMeta (mAp1c (f1Comp g h1 h2) d)  = mC g h1 h2 (triMeta d)
triMeta (mAp2c f2Proj d1 d2)        = mV (triMeta d1) (triMeta d2)
triMeta (mAp2c (f2Rec g h1 h2) d1 mRefl)                    = mRb g h1 h2 (triMeta d1)
triMeta (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1S e))            = mRs g h1 h2 (triMeta d1) (triMeta e)
triMeta (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Zero e))         = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mAp1c f1Zero e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Id e))           = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mAp1c f1Id e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mAp1c (f1Comp a b c) e)) = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mAp1c (f1Comp a b c) e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mAp2c fm e1 e2))         = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mAp2c fm e1 e2))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mO e))                  = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mO e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mU e))                  = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mU e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mV e1 e2))              = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mV e1 e2))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mC a b c e))            = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mC a b c e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mRb a b c e))           = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mRb a b c e))
triMeta (mAp2c (f2Rec g h1 h2) d1 (mRs a b c e1 e2))       = mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta (mRs a b c e1 e2))
triMeta (mO d)                      = mRefl
triMeta (mU d)                      = triMeta d
triMeta (mV d1 d2)                  = triMeta d2
triMeta (mC g h1 h2 d)              = mAp2c g (mAp1c h1 (triMeta d)) (mAp1c h2 (triMeta d))
triMeta (mRb g h1 h2 d)             = mAp1c g (triMeta d)
triMeta (mRs g h1 h2 d1 d2)         =
  mAp2c h1 (mAp2c h2 (triMeta d1) (triMeta d2))
           (mAp2c (f2Rec g h1 h2) (triMeta d1) (triMeta d2))

------------------------------------------------------------------------
-- SECTION 4.  Congruence helpers (child equalities of a binNode).

congL1 : (n r l l' : Term) -> Deriv (eqF l l') ->
         Deriv (eqF (binNode n l r) (binNode n l' r))
congL1 n r l l' eq = congR pi (natCode 2) (congR pi n (congL pi r eq))

cong2 : (n l l' r r' : Term) -> Deriv (eqF l l') -> Deriv (eqF r r') ->
        Deriv (eqF (binNode n l r) (binNode n l' r'))
cong2 n l l' r r' el er =
  ruleTrans (congL1 n r l l' el)
            (congR pi (natCode 2) (congR pi n (congR pi l' er)))

-- specialised: cong on the single child of an ap1c-shaped node.
cAp1c : (f X X' : Term) -> Deriv (eqF X X') -> Deriv (eqF (ap1c f X) (ap1c f X'))
cAp1c f X X' eq = congL1 (ap2 Pair dgAp1c f) filler X X' eq

cAp2c : (g X1 X1' X2 X2' : Term) -> Deriv (eqF X1 X1') -> Deriv (eqF X2 X2') ->
        Deriv (eqF (ap2c g X1 X2) (ap2c g X1' X2'))
cAp2c g X1 X1' X2 X2' e1 e2 = cong2 (ap2 Pair dgAp2c g) X1 X1' X2 X2' e1 e2

------------------------------------------------------------------------
-- SECTION 5.  The bridge  triShadowU  by structural induction.

triShadowU : (d : DerM) -> Deriv (eqF (ap1 triF (codeDer d)) (codeDer (triMeta d)))
triShadowU mRefl = triF_reflO
triShadowU (mAp1c f1S d) =
  ruleTrans (triF_ap1c_s (codeDer d))
            (cAp1c cSuc (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d))
triShadowU (mAp1c f1Zero d) =
  ruleTrans (triF_ap1c_o (codeDer d))
            (congL1 (ap2 Pair dgRo O) filler (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d))
triShadowU (mAp1c f1Id d) =
  ruleTrans (triF_ap1c_u (codeDer d))
            (congL1 (ap2 Pair dgRu O) filler (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d))
triShadowU (mAp1c (f1Comp g h1 h2) d) =
  ruleTrans (triF_ap1c_C (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d))
            (congL1 (ap2 Pair dgRC (bun3 (codeF2 g) (codeF1 h1) (codeF1 h2))) filler
              (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d))
triShadowU (mAp2c f2Proj d1 d2) =
  ruleTrans (triF_ap2c_v (codeDer d1) (codeDer d2))
            (cong2 (ap2 Pair dgRv O) (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (codeDer d2)) (codeDer (triMeta d2)) (triShadowU d1) (triShadowU d2))
triShadowU (mO d)     = triF_O (codeDer d)
triShadowU (mU d)     = ruleTrans (triF_U (codeDer d)) (triShadowU d)
triShadowU (mV d1 d2) = ruleTrans (triF_V (codeDer d1) (codeDer d2)) (triShadowU d2)
triShadowU (mC g h1 h2 d) =
  ruleTrans (triF_C (codeF2 g) (codeF1 h1) (codeF1 h2) (codeDer d))
            (cAp2c (codeF2 g)
              (ap1c (codeF1 h1) (ap1 triF (codeDer d))) (ap1c (codeF1 h1) (codeDer (triMeta d)))
              (ap1c (codeF1 h2) (ap1 triF (codeDer d))) (ap1c (codeF1 h2) (codeDer (triMeta d)))
              (cAp1c (codeF1 h1) (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d))
              (cAp1c (codeF1 h2) (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d)))
triShadowU (mRb g h1 h2 d) =
  ruleTrans (triF_Rb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d))
            (cAp1c (codeF1 g) (ap1 triF (codeDer d)) (codeDer (triMeta d)) (triShadowU d))
triShadowU (mRs g h1 h2 d1 d2) =
  ruleTrans (triF_Rs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer d2))
            (cAp2c (codeF2 h1)
              (ap2c (codeF2 h2) (ap1 triF (codeDer d1)) (ap1 triF (codeDer d2)))
              (ap2c (codeF2 h2) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
              (ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 triF (codeDer d1)) (ap1 triF (codeDer d2)))
              (ap2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (codeDer (triMeta d1)) (codeDer (triMeta d2)))
              (cAp2c (codeF2 h2) (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
                (ap1 triF (codeDer d2)) (codeDer (triMeta d2)) (triShadowU d1) (triShadowU d2))
              (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
                (ap1 triF (codeDer d2)) (codeDer (triMeta d2)) (triShadowU d1) (triShadowU d2)))
-- ap2c-cRec depth-2.
triShadowU (mAp2c (f2Rec g h1 h2) d1 mRefl) =
  ruleTrans (triF_ap2c_Rb (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1))
            (congL1 (ap2 Pair dgRb (bun3 (codeF1 g) (codeF2 h1) (codeF2 h2))) filler
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1)) (triShadowU d1))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1S e)) =
  ruleTrans (triF_ap2c_Rs (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1) (codeDer e))
            (cong2 (ap2 Pair dgRs (bun3 (codeF1 g) (codeF2 h1) (codeF2 h2)))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (codeDer e)) (codeDer (triMeta e)) (triShadowU d1) (triShadowU e))
-- Rcong else cases: each instantiates the relevant Rcong lemma at codeDer d2's shape.
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Zero e)) =
  ruleTrans (triF_ap2c_Rcong_ap1cNotSuc (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (ap1c cZero (codeDer e)) cZero (codeDer e) filler 4 (axRefl (ap1c cZero (codeDer e))) (axFst tgZero O) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (ap1c cZero (codeDer e))) (codeDer (triMeta (mAp1c f1Zero e)))
              (triShadowU d1) (triShadowU (mAp1c f1Zero e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mAp1c f1Id e)) =
  ruleTrans (triF_ap2c_Rcong_ap1cNotSuc (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (ap1c cId (codeDer e)) cId (codeDer e) filler 5 (axRefl (ap1c cId (codeDer e))) (axFst tgId O) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (ap1c cId (codeDer e))) (codeDer (triMeta (mAp1c f1Id e)))
              (triShadowU d1) (triShadowU (mAp1c f1Id e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mAp1c (f1Comp a b c) e)) =
  ruleTrans (triF_ap2c_Rcong_ap1cNotSuc (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (ap1c (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (codeDer e))
              (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (codeDer e) filler 6 (axRefl (ap1c (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (codeDer e)))
              (axFst tgComp (bun3 (codeF2 a) (codeF1 b) (codeF1 c))) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (ap1c (cComp (codeF2 a) (codeF1 b) (codeF1 c)) (codeDer e)))
              (codeDer (triMeta (mAp1c (f1Comp a b c) e)))
              (triShadowU d1) (triShadowU (mAp1c (f1Comp a b c) e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mAp2c fm e1 e2)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (ap2c (codeF2 fm) (codeDer e1) (codeDer e2))
              (ap2 Pair dgAp2c (codeF2 fm)) (codeDer e1) (codeDer e2) 2 (axRefl (ap2c (codeF2 fm) (codeDer e1) (codeDer e2)))
              (axFst dgAp2c (codeF2 fm)) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (ap2c (codeF2 fm) (codeDer e1) (codeDer e2)))
              (codeDer (triMeta (mAp2c fm e1 e2)))
              (triShadowU d1) (triShadowU (mAp2c fm e1 e2)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mO e)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (derO (codeDer e)) (ap2 Pair dgRo O) (codeDer e) filler 3 (axRefl (derO (codeDer e)))
              (axFst dgRo O) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (derO (codeDer e))) (codeDer (triMeta (mO e)))
              (triShadowU d1) (triShadowU (mO e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mU e)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (derU (codeDer e)) (ap2 Pair dgRu O) (codeDer e) filler 4 (axRefl (derU (codeDer e)))
              (axFst dgRu O) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (derU (codeDer e))) (codeDer (triMeta (mU e)))
              (triShadowU d1) (triShadowU (mU e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mV e1 e2)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (derV (codeDer e1) (codeDer e2)) (ap2 Pair dgRv O) (codeDer e1) (codeDer e2) 5 (axRefl (derV (codeDer e1) (codeDer e2)))
              (axFst dgRv O) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (derV (codeDer e1) (codeDer e2))) (codeDer (triMeta (mV e1 e2)))
              (triShadowU d1) (triShadowU (mV e1 e2)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mC a b c e)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (derC (codeF2 a) (codeF1 b) (codeF1 c) (codeDer e))
              (ap2 Pair dgRC (bun3 (codeF2 a) (codeF1 b) (codeF1 c))) (codeDer e) filler 6 (axRefl (derC (codeF2 a) (codeF1 b) (codeF1 c) (codeDer e)))
              (axFst dgRC (bun3 (codeF2 a) (codeF1 b) (codeF1 c))) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (derC (codeF2 a) (codeF1 b) (codeF1 c) (codeDer e)))
              (codeDer (triMeta (mC a b c e)))
              (triShadowU d1) (triShadowU (mC a b c e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mRb a b c e)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (derRb (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e))
              (ap2 Pair dgRb (bun3 (codeF1 a) (codeF2 b) (codeF2 c))) (codeDer e) filler 7 (axRefl (derRb (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e)))
              (axFst dgRb (bun3 (codeF1 a) (codeF2 b) (codeF2 c))) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (derRb (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e)))
              (codeDer (triMeta (mRb a b c e)))
              (triShadowU d1) (triShadowU (mRb a b c e)))
triShadowU (mAp2c (f2Rec g h1 h2) d1 (mRs a b c e1 e2)) =
  ruleTrans (triF_ap2c_Rcong_notAp1c (codeF1 g) (codeF2 h1) (codeF2 h2) (codeDer d1)
              (derRs (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e1) (codeDer e2))
              (ap2 Pair dgRs (bun3 (codeF1 a) (codeF2 b) (codeF2 c))) (codeDer e1) (codeDer e2) 8 (axRefl (derRs (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e1) (codeDer e2)))
              (axFst dgRs (bun3 (codeF1 a) (codeF2 b) (codeF2 c))) (\ ()))
            (cAp2c (cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
              (ap1 triF (codeDer d1)) (codeDer (triMeta d1))
              (ap1 triF (derRs (codeF1 a) (codeF2 b) (codeF2 c) (codeDer e1) (codeDer e2)))
              (codeDer (triMeta (mRs a b c e1 e2)))
              (triShadowU d1) (triShadowU (mRs a b c e1 e2)))
