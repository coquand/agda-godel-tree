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
        ; wfFun_cComp ; wfFun_cRec ; isF1 ; isF2 )
open import T4.PrCodeObj
  using ( cSuc ; cZero ; cId ; cProj ; cComp ; cRec
        ; hd_cSuc ; hd_cZero ; hd_cId ; hd_cProj ; hd_cComp ; hd_cRec )
open import T4.PrFunValidCanon
  using ( funValidF ; funValidF_eq ; funValid_cComp ; funValid_cRec )
open import T4.ParEnds using ( pi_O_O )

open import BRA3.Church using ( pi )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.SubT.V2NatNeq using ( natEqF_at_neq ; decideNatNeq )

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

  -- arity head-checks pass for shadow funcodes (heads are concrete).
  nHO : (f : Term) (m k : Nat) -> Deriv (eqF (ap1 Fst f) (natCode m)) -> ((Eq m k) -> Empty) ->
        Deriv (eqF (ap2 natEqF (ap1 Fst f) (natCode k)) O)
  nHO f m k hd w = ruleTrans (congL natEqF (natCode k) hd) (natEqF_at_neq m k (decideNatNeq m k w))
  isF1O : (f : Term) (m : Nat) -> Deriv (eqF (ap1 Fst f) (natCode m)) ->
          ((Eq m 7) -> Empty) -> ((Eq m 8) -> Empty) -> ((Eq m 1) -> Empty) -> Deriv (eqF (isF1 f) O)
  isF1O f m hd w7 w8 w1 =
    piBothO (ap2 natEqF (ap1 Fst f) (natCode 7))
      (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 8)) (ap2 natEqF (ap1 Fst f) (natCode 1)))
      (nHO f m 7 hd w7)
      (piBothO (ap2 natEqF (ap1 Fst f) (natCode 8)) (ap2 natEqF (ap1 Fst f) (natCode 1))
        (nHO f m 8 hd w8) (nHO f m 1 hd w1))
  isF2O : (f : Term) (m : Nat) -> Deriv (eqF (ap1 Fst f) (natCode m)) ->
          ((Eq m 3) -> Empty) -> ((Eq m 4) -> Empty) -> ((Eq m 5) -> Empty) -> ((Eq m 6) -> Empty) -> ((Eq m 1) -> Empty) ->
          Deriv (eqF (isF2 f) O)
  isF2O f m hd w3 w4 w5 w6 w1 =
    piBothO (ap2 natEqF (ap1 Fst f) (natCode 3))
      (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 4))
        (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 5))
          (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 6)) (ap2 natEqF (ap1 Fst f) (natCode 1)))))
      (nHO f m 3 hd w3)
      (piBothO (ap2 natEqF (ap1 Fst f) (natCode 4))
        (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 5))
          (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 6)) (ap2 natEqF (ap1 Fst f) (natCode 1))))
        (nHO f m 4 hd w4)
        (piBothO (ap2 natEqF (ap1 Fst f) (natCode 5))
          (ap2 pi (ap2 natEqF (ap1 Fst f) (natCode 6)) (ap2 natEqF (ap1 Fst f) (natCode 1)))
          (nHO f m 5 hd w5)
          (piBothO (ap2 natEqF (ap1 Fst f) (natCode 6)) (ap2 natEqF (ap1 Fst f) (natCode 1))
            (nHO f m 6 hd w6) (nHO f m 1 hd w1))))

isF1_codeF1 : (fm : Fun1M) -> Deriv (eqF (isF1 (codeF1 fm)) O)
isF2_codeF2 : (fm : Fun2M) -> Deriv (eqF (isF2 (codeF2 fm)) O)
isF1_codeF1 f1S    = isF1O cSuc  3 hd_cSuc  (\ ()) (\ ()) (\ ())
isF1_codeF1 f1Zero = isF1O cZero 4 hd_cZero (\ ()) (\ ()) (\ ())
isF1_codeF1 f1Id   = isF1O cId   5 hd_cId   (\ ()) (\ ()) (\ ())
isF1_codeF1 (f1Comp g h1 h2) = isF1O (cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) 6 (hd_cComp (codeF2 g) (codeF1 h1) (codeF1 h2)) (\ ()) (\ ()) (\ ())
isF2_codeF2 f2Proj = isF2O cProj 7 hd_cProj (\ ()) (\ ()) (\ ()) (\ ()) (\ ())
isF2_codeF2 (f2Rec g h1 h2) = isF2O (cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) 8 (hd_cRec (codeF1 g) (codeF2 h1) (codeF2 h2)) (\ ()) (\ ()) (\ ()) (\ ()) (\ ())

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
                (ap2 pi (isF2 G) (ap2 pi (isF1 H1) (ap2 pi (isF1 H2)
                  (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2))))))
                selfO
                (piBothO (isF2 G) (ap2 pi (isF1 H1) (ap2 pi (isF1 H2)
                          (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2)))))
                   (isF2_codeF2 g)
                   (piBothO (isF1 H1) (ap2 pi (isF1 H2)
                             (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2))))
                      (isF1_codeF1 h1)
                      (piBothO (isF1 H2) (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2)))
                         (isF1_codeF1 h2)
                         (fv3O G H1 H2 (wfFun_codeF2 g) (wfFun_codeF1 h1) (wfFun_codeF1 h2))))))
wfFun_codeF2 f2Proj           = wfFun_cProj
wfFun_codeF2 (f2Rec g h1 h2)  =
  let G = codeF1 g
      H1 = codeF2 h1
      H2 = codeF2 h2
      selfO : Deriv (eqF (ap1 funValidF (cRec G H1 H2)) O)
      selfO = ruleTrans (funValidF_eq (cRec G H1 H2)) (funValid_cRec G H1 H2)
  in ruleTrans (wfFun_cRec G H1 H2)
       (piBothO (ap1 funValidF (cRec G H1 H2))
                (ap2 pi (isF1 G) (ap2 pi (isF2 H1) (ap2 pi (isF2 H2)
                  (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2))))))
                selfO
                (piBothO (isF1 G) (ap2 pi (isF2 H1) (ap2 pi (isF2 H2)
                          (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2)))))
                   (isF1_codeF1 g)
                   (piBothO (isF2 H1) (ap2 pi (isF2 H2)
                             (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2))))
                      (isF2_codeF2 h1)
                      (piBothO (isF2 H2) (ap2 pi (ap1 wfFun G) (ap2 pi (ap1 wfFun H1) (ap1 wfFun H2)))
                         (isF2_codeF2 h2)
                         (fv3O G H1 H2 (wfFun_codeF1 g) (wfFun_codeF2 h1) (wfFun_codeF2 h2))))))
