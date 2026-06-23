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
open import T4.PrCodeObj using ( cComp ; cRec )
open import T4.PrFunValidCanon
  using ( funValidF ; funValidF_eq ; funValid_cComp ; funValid_cRec )
open import T4.ParEnds using ( pi_O_O )

open import BRA3.Church using ( pi )

------------------------------------------------------------------------

private
  piBothO : (l r : Term) -> Deriv (eqF l O) -> Deriv (eqF r O) ->
            Deriv (eqF (ap2 pi l r) O)
  piBothO l r el er =
    ruleTrans (congL pi r el) (ruleTrans (congR pi O er) pi_O_O)

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
  let G = codeF2 g
      H1 = codeF1 h1
      H2 = codeF1 h2
      selfO : Deriv (eqF (ap1 funValidF (cComp G H1 H2)) O)
      selfO = ruleTrans (funValidF_eq (cComp G H1 H2)) (funValid_cComp G H1 H2)
  in ruleTrans (wfFun_cComp G H1 H2)
       (piBothO (ap1 funValidF (cComp G H1 H2))
                (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2)))
                selfO
                (fv3O G H1 H2 (wfFun_codeF2 g) (wfFun_codeF1 h1) (wfFun_codeF1 h2)))
wfFun_codeF2 f2Proj           = wfFun_cProj
wfFun_codeF2 (f2Rec g h1 h2)  =
  let G = codeF1 g
      H1 = codeF2 h1
      H2 = codeF2 h2
      selfO : Deriv (eqF (ap1 funValidF (cRec G H1 H2)) O)
      selfO = ruleTrans (funValidF_eq (cRec G H1 H2)) (funValid_cRec G H1 H2)
  in ruleTrans (wfFun_cRec G H1 H2)
       (piBothO (ap1 funValidF (cRec G H1 H2))
                (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2)))
                selfO
                (fv3O G H1 H2 (wfFun_codeF1 g) (wfFun_codeF2 h1) (wfFun_codeF2 h2)))
