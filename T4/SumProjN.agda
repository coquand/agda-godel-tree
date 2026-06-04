{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SumProjN -- the bounded single-summand projection
-- ( SURPRISE-GII-NUMBERCODE-HANDOFF S3.3 ).
--
--   sumProjN q :
--     Deriv (imp (eqF (ap2 defCountN q (var 0)) O)              -- sum_{j<=bound} = O
--                (imp (leq (var 1) (var 0))                     -- proj index <= bound
--                     (eqF (ap2 defIndN (ap1 I (var 1)) q) O))) -- that summand = O
--
-- "in an object sum  sum_{j=0}^{m} defIndN(j, q)  that equals O, every summand at
-- an index  <= m  is itself O".   Pure BRA arithmetic ( object  ruleIndNat  on the
-- bound  var 0 , telescoping by the converse sigma-zero  T4.SigmaZeroN ), Sigma_1-
-- free.   This is the surprise analog of Chaitin-GI's substitution clash : the
-- diagonal's number  n0  ( with  n0 < N  the proven  dLenStarDefN.sizePinN )
-- projects its own summand out of  g N = 0 .
--
-- The bound  var 0  is the induction variable and the projection index  var 1  is
-- open ;   q  must avoid  var 0 / var 1  ( it does in use :  q = pi z y  with the
-- subject / fuel taken from  var 2 / var 3  or closed ).   The summand is left as
-- the folded  defIndN (ap1 I (var 1)) q ;  apply  axI  to drop the  I .

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
        ; closeCoe )
open import T4.BoundedCases      using ( leqO_eq )
open import T4.Thm12.ImpHelpers  using ( impCong1 ; impCongL )
open import T4.SigmaZeroN        using ( sigmaZeroL ; sigmaZeroR )
open import T4.DefIndN
  using ( defCountN ; defIndN ; defCountN_at_O ; defCountN_succ )

module T4.SumProjN (q : Term) (cq : Closed q) where

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
-- The projection conclusion ( fixed ; summand at the open index var 1 ).

Gf : Formula
Gf = eqF (ap2 defIndN (ap1 I (var (suc zero))) q) O

P : Formula
P = imp (eqF (ap2 defCountN q (var zero)) O)
        (imp (leq (var (suc zero)) (var zero)) Gf)

------------------------------------------------------------------------
-- Base ( bound := O ) :   leq (var 1) O  pins  var 1 = O , so the single
-- summand IS the whole sum, which is O.

base : Deriv (imp (eqF (ap2 defCountN q O) O)
                  (imp (leq (var (suc zero)) O) Gf))
base =
  let H1b : Formula
      H1b = eqF (ap2 defCountN q O) O
      H2b : Formula
      H2b = leq (var (suc zero)) O
      dIO0 : Term                       -- defIndN (I O) q
      dIO0 = ap2 defIndN (ap1 I O) q
      sv1 : Term                        -- the summand at var 1
      sv1 = ap2 defIndN (ap1 I (var (suc zero))) q

      dIO : Deriv (imp H1b (eqF dIO0 O))
      dIO = prependEqLeft dIO0 (ap2 defCountN q O) O (ruleSym (defCountN_at_O q))

      eqI : Deriv (imp H2b (eqF (ap1 I (var (suc zero))) (ap1 I O)))
      eqI = impCong1 I (var (suc zero)) O (leqO_eq (var (suc zero)))

      congd : Deriv (imp H2b (eqF sv1 dIO0))
      congd = impCongL defIndN (ap1 I (var (suc zero))) (ap1 I O) q eqI

      congd' : Deriv (imp H1b (imp H2b (eqF sv1 dIO0)))
      congd' = liftP H1b congd

      dIO' : Deriv (imp H1b (imp H2b (eqF dIO0 O)))
      dIO' = mapUnder1 H1b (axK (eqF dIO0 O) H2b) dIO
  in trans2 H1b H2b sv1 dIO0 O congd' dIO'

------------------------------------------------------------------------
-- Step ( bound := s var0 ) :   the sum telescopes
--   sum (s v0) = sigma (sum v0) (summand (s v0)) ,
-- so  = O  splits ( converse sigma-zero ) into  sum v0 = O  and  summand (s v0) = O .
-- By-cases on  leq v1 v0 :  yes -> IH on the prefix ;  no -> v1 = s v0 ( T82 ), so
-- the projected summand IS  summand (s v0) = O .

step : Deriv (imp P
        (imp (eqF (ap2 defCountN q (ap1 s (var zero))) O)
             (imp (leq (var (suc zero)) (ap1 s (var zero))) Gf)))
step =
  let v0 : Term
      v0 = var zero
      v1 : Term
      v1 = var (suc zero)
      phi : Formula
      phi = eqF (ap2 defCountN q (ap1 s v0)) O
      psi : Formula
      psi = leq v1 (ap1 s v0)
      negA : Formula
      negA = neg (leq v1 v0)
      sumv0 : Term
      sumv0 = ap2 defCountN q v0
      topS : Term                       -- summand (s v0) = defIndN (I (s v0)) q
      topS = ap2 defIndN (ap1 I (ap1 s v0)) q
      X : Formula                       -- P's antecedent
      X = eqF sumv0 O
      Y : Formula                       -- P's consequent
      Y = imp (leq v1 v0) Gf

      sig0 : Deriv (imp phi (eqF (ap2 sigma sumv0 topS) O))
      sig0 = prependEqLeft (ap2 sigma sumv0 topS)
                           (ap2 defCountN q (ap1 s v0)) O
                           (ruleSym (defCountN_succ q v0))

      prefix : Deriv (imp phi (eqF sumv0 O))
      prefix = compI sig0 (sigmaZeroL sumv0 topS)

      top : Deriv (imp phi (eqF topS O))
      top = compI sig0 (sigmaZeroR sumv0 topS)

      ----------------------------------------------------------------
      -- yes-branch :  leq v1 v0  ->  IH gives the summand.
      pp : Deriv (imp P (imp phi (imp X Y)))
      pp = mapUnder1 P (axK P phi) (identImp P)

      xx : Deriv (imp P (imp phi X))
      xx = liftP P prefix

      pY : Deriv (imp P (imp phi Y))
      pY = bCombTwo pp xx

      c1 : Deriv (imp P (imp phi (imp psi (imp (leq v1 v0) Gf))))
      c1 = mapUnder2 P phi (axK Y psi) pY

      ----------------------------------------------------------------
      -- no-branch :  neg (leq v1 v0)  ->  v1 = s v0  ->  summand IS top.
      t82i : Deriv (imp psi (imp negA (eqF v1 (ap1 s v0))))
      t82i = ruleInst2 0 v1 1 v0 refl T82

      eqv1q : Deriv (imp P (imp phi (imp psi (imp negA (eqF v1 (ap1 s v0))))))
      eqv1q = liftP P (liftP phi t82i)

      cIq : Deriv (imp P (imp phi (imp psi (imp negA
               (eqF (ap1 I v1) (ap1 I (ap1 s v0)))))))
      cIq = mapUnder4 P phi psi negA (ax_eqCong1 I v1 (ap1 s v0)) eqv1q

      cdq : Deriv (imp P (imp phi (imp psi (imp negA
               (eqF (ap2 defIndN (ap1 I v1) q) topS)))))
      cdq = mapUnder4 P phi psi negA
               (ax_eqCongL defIndN (ap1 I v1) (ap1 I (ap1 s v0)) q) cIq

      topq : Deriv (imp P (imp phi (imp psi (imp negA (eqF topS O)))))
      topq = liftP P
                (mapUnder2 phi psi (axK (eqF topS O) negA)
                  (mapUnder1 phi (axK (eqF topS O) psi) top))

      c2 : Deriv (imp P (imp phi (imp psi (imp negA Gf))))
      c2 = trans4 P phi psi negA (ap2 defIndN (ap1 I v1) q) topS O cdq topq
  in byCasesUnder3 P phi psi (leq v1 v0) Gf c1 c2

------------------------------------------------------------------------

motiveBase : Term -> Formula
motiveBase X =
  imp (eqF (ap2 defCountN X O) O)
      (imp (leq (var (suc zero)) O)
           (eqF (ap2 defIndN (ap1 I (var (suc zero))) X) O))

motiveStep : Term -> Formula
motiveStep X =
  imp P (imp (eqF (ap2 defCountN X (ap1 s (var zero))) O)
             (imp (leq (var (suc zero)) (ap1 s (var zero)))
                  (eqF (ap2 defIndN (ap1 I (var (suc zero))) X) O)))

sumProjN : Deriv P
sumProjN =
  ruleIndNat zero {P = P}
    (closeCoe cq zero O motiveBase base)
    (closeCoe cq zero (ap1 s (var zero)) motiveStep step)
