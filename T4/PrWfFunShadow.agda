{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrWfFunShadow -- DEEP soundness of funcode validity: every shadow funcode
-- validates,  wfFun (codeF1 fm) = O  /  wfFun (codeF2 fm) = O , by mutual
-- structural induction on the funcode shadows Fun1M / Fun2M (T4.PrTriShadow).
-- The compound cases use wfFun_cComp/cRec + piBothO + the IHs (deep), so the
-- whole funcode tree is validated.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrWfFunShadow where

open import T4.Base

open import T4.PrTriShadow
  using ( Fun1M ; Fun2M ; f1S ; f1Zero ; f1Id ; f1Comp ; f2Proj ; f2Rec
        ; codeF1 ; codeF2 )
open import T4.PrWfFun
  using ( wfFun ; wfFun_cSuc ; wfFun_cZero ; wfFun_cId ; wfFun_cProj
        ; wfFun_cComp ; wfFun_cRec )
open import T4.PrWfRedFull using ( piBothO )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------

-- pi (wfFun g) (pi (wfFun h1) (wfFun h2)) = O  from the three validities.
private
  fv3O : (g h1 h2 : Term) ->
    Deriv (eqF (ap1 wfFun g) O) -> Deriv (eqF (ap1 wfFun h1) O) -> Deriv (eqF (ap1 wfFun h2) O) ->
    Deriv (eqF (ap2 pi (ap1 wfFun g) (ap2 pi (ap1 wfFun h1) (ap1 wfFun h2))) O)
  fv3O g h1 h2 eg e1 e2 =
    piBothO (ap1 wfFun g) (ap2 pi (ap1 wfFun h1) (ap1 wfFun h2)) eg
            (piBothO (ap1 wfFun h1) (ap1 wfFun h2) e1 e2)

wfFun_codeF1 : (fm : Fun1M) -> Deriv (eqF (ap1 wfFun (codeF1 fm)) O)
wfFun_codeF2 : (fm : Fun2M) -> Deriv (eqF (ap1 wfFun (codeF2 fm)) O)
wfFun_codeF1 f1S              = wfFun_cSuc
wfFun_codeF1 f1Zero           = wfFun_cZero
wfFun_codeF1 f1Id             = wfFun_cId
wfFun_codeF1 (f1Comp g h1 h2) =
  ruleTrans (wfFun_cComp (codeF2 g) (codeF1 h1) (codeF1 h2))
            (fv3O (codeF2 g) (codeF1 h1) (codeF1 h2)
                  (wfFun_codeF2 g) (wfFun_codeF1 h1) (wfFun_codeF1 h2))
wfFun_codeF2 f2Proj           = wfFun_cProj
wfFun_codeF2 (f2Rec g h1 h2)  =
  ruleTrans (wfFun_cRec (codeF1 g) (codeF2 h1) (codeF2 h2))
            (fv3O (codeF1 g) (codeF2 h1) (codeF2 h2)
                  (wfFun_codeF1 g) (wfFun_codeF2 h1) (wfFun_codeF2 h2))
