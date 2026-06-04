{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SumProjGen -- the GENERIC bounded single-summand projection : for ANY
-- indicator  f : Fun2  ( read  ap2 f i q  as  "f i"  at parameter  q ), the sum
--
--   gFun q n  =  sum_{i=0}^{n} f (I i) q        ( = sumRec f I )
--
-- is  O  iff every summand is, so a zero sum projects each summand below the bound:
--
--   sumProjGen :
--     Deriv (imp (eqF (ap2 gFun q (var 0)) O)                 -- g n = O  ( g = sum f )
--                (imp (leq (var 1) (var 0))                   -- x <= n
--                     (eqF (ap2 f (ap1 I (var 1)) q) O)))     -- f x = O
--
-- "g n = O  =>  ( x <= n  =>  f x = O )", the clean conjunction-projection the
-- Chaitin bridge calls for ( the bounded big-conjunction  /\_{i<n} f i = O  as the
-- single atom  g n = O ).   Generalises  T4.SumProjN  ( = this at  f := defIndN ),
-- verbatim proof:  object  ruleIndNat  on the bound, telescoped by  T4.SigmaZeroN .
--  q  must avoid  var 0 / var 1  ( the  Closed q  witness coerces the motive ).

open import T4.Base
open import BRA3.ChurchLeq       using ( leq )
open import BRA3.Church          using ( sigma )
open import BRA3.ChurchT82       using ( T82 )
open import BRA3.Logic           using ( prependEqLeft )
open import BRA3.RuleInst2       using ( ruleInst2 )
open import BRA3.Contrapositive  using ( compI ; liftP ; bCombTwo ; axContrapos ; DNE )
open import BRA3.Dispatch        using ( Closed )
open import T4.Counting          using ( mapUnder1 ; mapUnder2 )
open import T4.CountingObj
  using ( identImp ; trans2 ; mapUnder3 ; mapUnder4 ; trans4 ; negIntroUnder3
        ; closeCoe ; sumRec ; sumRec_at_O ; sumRec_succ )
open import T4.BoundedCases      using ( leqO_eq )
open import T4.Thm12.ImpHelpers  using ( impCong1 ; impCongL )
open import T4.SigmaZeroN        using ( sigmaZeroL ; sigmaZeroR )

module T4.SumProjGen (f : Fun2) (q : Term) (cq : Closed q) where

gFun : Fun2
gFun = sumRec f I

------------------------------------------------------------------------
-- A 3-carried-hypothesis by-cases ( mirror CountingObj.byCasesUnder2 ).

byCasesUnder3 :
  (h1 h2 h3 A Goal : Formula) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp A Goal)))) ->
  Deriv (imp h1 (imp h2 (imp h3 (imp (neg A) Goal)))) ->
  Deriv (imp h1 (imp h2 (imp h3 Goal)))
byCasesUnder3 h1 h2 h3 A Goal c1 c2 =
  let e1 : Deriv (imp h1 (imp h2 (imp h3 (imp (neg Goal) (neg A)))))
      e1 = mapUnder3 h1 h2 h3 (axContrapos A Goal) c1
      e2 : Deriv (imp h1 (imp h2 (imp h3 (imp (neg Goal) (neg (neg A))))))
      e2 = mapUnder3 h1 h2 h3 (axContrapos (neg A) Goal) c2
      nng : Deriv (imp h1 (imp h2 (imp h3 (neg (neg Goal)))))
      nng = negIntroUnder3 h1 h2 h3 (neg Goal) (neg A) e1 e2
  in mapUnder3 h1 h2 h3 (DNE Goal) nng

------------------------------------------------------------------------

Gf : Formula
Gf = eqF (ap2 f (ap1 I (var (suc zero))) q) O

P : Formula
P = imp (eqF (ap2 gFun q (var zero)) O)
        (imp (leq (var (suc zero)) (var zero)) Gf)

base : Deriv (imp (eqF (ap2 gFun q O) O)
                  (imp (leq (var (suc zero)) O) Gf))
base =
  let H1b : Formula
      H1b = eqF (ap2 gFun q O) O
      H2b : Formula
      H2b = leq (var (suc zero)) O
      dIO0 : Term
      dIO0 = ap2 f (ap1 I O) q
      sv1 : Term
      sv1 = ap2 f (ap1 I (var (suc zero))) q
      dIO : Deriv (imp H1b (eqF dIO0 O))
      dIO = prependEqLeft dIO0 (ap2 gFun q O) O (ruleSym (sumRec_at_O f I q))
      eqI : Deriv (imp H2b (eqF (ap1 I (var (suc zero))) (ap1 I O)))
      eqI = impCong1 I (var (suc zero)) O (leqO_eq (var (suc zero)))
      congd : Deriv (imp H2b (eqF sv1 dIO0))
      congd = impCongL f (ap1 I (var (suc zero))) (ap1 I O) q eqI
      congd' : Deriv (imp H1b (imp H2b (eqF sv1 dIO0)))
      congd' = liftP H1b congd
      dIO' : Deriv (imp H1b (imp H2b (eqF dIO0 O)))
      dIO' = mapUnder1 H1b (axK (eqF dIO0 O) H2b) dIO
  in trans2 H1b H2b sv1 dIO0 O congd' dIO'

step : Deriv (imp P
        (imp (eqF (ap2 gFun q (ap1 s (var zero))) O)
             (imp (leq (var (suc zero)) (ap1 s (var zero))) Gf)))
step =
  let v0 : Term
      v0 = var zero
      v1 : Term
      v1 = var (suc zero)
      phi : Formula
      phi = eqF (ap2 gFun q (ap1 s v0)) O
      psi : Formula
      psi = leq v1 (ap1 s v0)
      negA : Formula
      negA = neg (leq v1 v0)
      sumv0 : Term
      sumv0 = ap2 gFun q v0
      topS : Term
      topS = ap2 f (ap1 I (ap1 s v0)) q
      X : Formula
      X = eqF sumv0 O
      Y : Formula
      Y = imp (leq v1 v0) Gf
      sig0 : Deriv (imp phi (eqF (ap2 sigma sumv0 topS) O))
      sig0 = prependEqLeft (ap2 sigma sumv0 topS)
                           (ap2 gFun q (ap1 s v0)) O
                           (ruleSym (sumRec_succ f I q v0))
      prefix : Deriv (imp phi (eqF sumv0 O))
      prefix = compI sig0 (sigmaZeroL sumv0 topS)
      top : Deriv (imp phi (eqF topS O))
      top = compI sig0 (sigmaZeroR sumv0 topS)
      pp : Deriv (imp P (imp phi (imp X Y)))
      pp = mapUnder1 P (axK P phi) (identImp P)
      xx : Deriv (imp P (imp phi X))
      xx = liftP P prefix
      pY : Deriv (imp P (imp phi Y))
      pY = bCombTwo pp xx
      c1 : Deriv (imp P (imp phi (imp psi (imp (leq v1 v0) Gf))))
      c1 = mapUnder2 P phi (axK Y psi) pY
      t82i : Deriv (imp psi (imp negA (eqF v1 (ap1 s v0))))
      t82i = ruleInst2 0 v1 1 v0 refl T82
      eqv1q : Deriv (imp P (imp phi (imp psi (imp negA (eqF v1 (ap1 s v0))))))
      eqv1q = liftP P (liftP phi t82i)
      cIq : Deriv (imp P (imp phi (imp psi (imp negA
               (eqF (ap1 I v1) (ap1 I (ap1 s v0)))))))
      cIq = mapUnder4 P phi psi negA (ax_eqCong1 I v1 (ap1 s v0)) eqv1q
      cdq : Deriv (imp P (imp phi (imp psi (imp negA
               (eqF (ap2 f (ap1 I v1) q) topS)))))
      cdq = mapUnder4 P phi psi negA
               (ax_eqCongL f (ap1 I v1) (ap1 I (ap1 s v0)) q) cIq
      topq : Deriv (imp P (imp phi (imp psi (imp negA (eqF topS O)))))
      topq = liftP P
                (mapUnder2 phi psi (axK (eqF topS O) negA)
                  (mapUnder1 phi (axK (eqF topS O) psi) top))
      c2 : Deriv (imp P (imp phi (imp psi (imp negA Gf))))
      c2 = trans4 P phi psi negA (ap2 f (ap1 I v1) q) topS O cdq topq
  in byCasesUnder3 P phi psi (leq v1 v0) Gf c1 c2

motiveBase : Term -> Formula
motiveBase X =
  imp (eqF (ap2 gFun X O) O)
      (imp (leq (var (suc zero)) O)
           (eqF (ap2 f (ap1 I (var (suc zero))) X) O))

motiveStep : Term -> Formula
motiveStep X =
  imp P (imp (eqF (ap2 gFun X (ap1 s (var zero))) O)
             (imp (leq (var (suc zero)) (ap1 s (var zero)))
                  (eqF (ap2 f (ap1 I (var (suc zero))) X) O)))

sumProjGen : Deriv P
sumProjGen =
  ruleIndNat zero {P = P}
    (closeCoe cq zero O motiveBase base)
    (closeCoe cq zero (ap1 s (var zero)) motiveStep step)
