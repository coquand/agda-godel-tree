{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.TriUNodeKit -- the SIGNATURE-GENERIC node glue for the full-PR CR dispatch.
--
-- Every rule's sub-glue has the same shape: the opaque triangle map sends the
-- node sK to a residual N (built from triF of the children), and the Church-
-- Rosser triangle then reduces to FOUR per-node facts
--     triF sK = N        (the opaque triF residual, possibly after reconstruction)
--     wfRed N = O,  wfFunRec N = O        (N is well-formed)
--     srcF N = tgtF sK                    (source endpoint)
--     tgtF N = devF (srcF sK)             (target endpoint = development)
-- and `nodeGlue` assembles those four into  imp ... PA Bgoal  uniformly.  Only
-- those four facts are rule-specific; ALL the plumbing (the depth-4 Hilbert
-- context [negLeaf, htag, fh, PA], the validity split, the qcheck assembly,
-- the Cnj-folding of extra funhead antecedents) lives here, ONCE.
--
-- Parameterized by  htag  (the node-tag formula, e.g. dtag sK = dgAp1c/dgAp2c).
--
-- No holes, no postulates, no termination warnings (only the benign
-- RuleInst3:328 unreachable-clauses warning); --safe --without-K --exact-split.

open import T4.Base

module T4.TriUNodeKit (htag : Formula) where

open import T4.PrTriUGlue
  using ( sK ; PA ; negLeaf ; Bgoal ; ne_sK ; pa2a ; pa2phik ; rebound )
open import T4.PrWfRed using ( wfRed )
open import T4.PrWfFunRec using ( wfFunRec )
open import T4.PrWfRedFull using ( wfRedFull ; wfRedFull_eq )
open import T4.PrTri using ( triF )
open import T4.PrSrc using ( srcF )
open import T4.PrTgt using ( tgtF )
open import T4.PrDev using ( devF )
open import T4.PrQCheckU using ( conj3 )
open import T4.PrQCheckProjU using ( PhiKU ; QofChildU )
open import T4.PrCRGlueU using ( conj3_unfold )
open import T4.PrCRGlueImpU
  using ( childV_imp ; childS_imp ; childT_imp ; eqDecO_complete_imp ; sigmaBothO_imp
        ; piBothO_imp ; piZeroL_imp ; piZeroR_imp )
open import T4.EqDecO using ( eqDecO )
open import T4.PrCodeObj using ( tmAp1 ; tmAp2 ; tgAp1 ; tgAp2 )

open import BRA3.Logic using ( prependEqLeft ; eqSymImp )
open import BRA3.Contrapositive using ( compI ; identP ; liftP )
open import T4.Thm12.ImpHelpers using ( impCong1 ; impCongR ; impCongL )
open import T4.GammaCtx using ( Cnj ; cnjL ; cnjR )
open import T4.CtxKit
  using ( lift2 ; ap2c ; lift3 ; ap3c ; trans3c
        ; lift4 ; get4a ; get4b ; get4c ; get4d ; ap4c ; trans4c )
open import BRA3.Church using ( pi ; sigma )
open import BRA3.ChurchLeq using ( leq )

------------------------------------------------------------------------
-- A context fact:  imp negLeaf (imp htag (imp fh (imp PA X))) .

Ctx : Formula -> Formula -> Formula
Ctx fh X = imp negLeaf (imp htag (imp fh (imp PA X)))

private
  Aform : Formula
  Aform = eqF (ap1 wfRedFull sK) O

  afToWfRed : Deriv (imp Aform (eqF (ap1 wfRed sK) O))
  afToWfRed = compI (prependEqLeft (ap2 pi (ap1 wfRed sK) (ap1 wfFunRec sK)) (ap1 wfRedFull sK) O
                       (ruleSym (wfRedFull_eq sK)))
                    (piZeroL_imp (ap1 wfRed sK) (ap1 wfFunRec sK))
  afToWfFun : Deriv (imp Aform (eqF (ap1 wfFunRec sK) O))
  afToWfFun = compI (prependEqLeft (ap2 pi (ap1 wfRed sK) (ap1 wfFunRec sK)) (ap1 wfRedFull sK) O
                       (ruleSym (wfRedFull_eq sK)))
                    (piZeroR_imp (ap1 wfRed sK) (ap1 wfFunRec sK))

------------------------------------------------------------------------
-- Depth-4 ctx kit over  [negLeaf, htag, fh, PA] .

l4 : (fh : Formula) {X : Formula} -> Deriv X -> Deriv (Ctx fh X)
l4 fh d = lift4 negLeaf htag fh PA d

G4cong : (f : Fun1) (a b : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF a b)) -> Deriv (Ctx fh (eqF (ap1 f a) (ap1 f b)))
G4cong f a b fh d = ap4c (l4 fh (impCong1 f a b (identP (eqF a b)))) d

G4sym : (a b : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF a b)) -> Deriv (Ctx fh (eqF b a))
G4sym a b fh d = ap4c (l4 fh (eqSymImp a b)) d

G4trans : (a b c : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF a b)) -> Deriv (Ctx fh (eqF b c)) -> Deriv (Ctx fh (eqF a c))
G4trans a b c fh d e = trans4c a b c d e

addPA4 : (fh : Formula) {X : Formula} ->
  Deriv (imp negLeaf (imp htag (imp fh X))) -> Deriv (Ctx fh X)
addPA4 fh {X} d = ap3c (lift3 negLeaf htag fh (axK X PA)) d

addFunPA4 : (fh : Formula) {X : Formula} ->
  Deriv (imp negLeaf (imp htag X)) -> Deriv (Ctx fh X)
addFunPA4 fh {X} d = ap2c (lift2 negLeaf htag (compI (axK X PA) (axK (imp PA X) fh))) d

paA : (fh : Formula) -> Deriv (Ctx fh Aform)
paA fh = ap4c (l4 fh pa2a) (get4d negLeaf htag fh PA)
wfRedSK4 : (fh : Formula) -> Deriv (Ctx fh (eqF (ap1 wfRed sK) O))
wfRedSK4 fh = ap4c (l4 fh afToWfRed) (paA fh)
wfFunSK4 : (fh : Formula) -> Deriv (Ctx fh (eqF (ap1 wfFunRec sK) O))
wfFunSK4 fh = ap4c (l4 fh afToWfFun) (paA fh)

piB4 : (fh : Formula) (X Y : Term) ->
  Deriv (Ctx fh (eqF X O)) -> Deriv (Ctx fh (eqF Y O)) ->
  Deriv (Ctx fh (eqF (ap2 pi X Y) O))
piB4 fh X Y dX dY = ap4c (ap4c (l4 fh (piBothO_imp X Y)) dX) dY

mkWfRedFull4 : (fh : Formula) (t : Term) ->
  Deriv (Ctx fh (eqF (ap1 wfRed t) O)) -> Deriv (Ctx fh (eqF (ap1 wfFunRec t) O)) ->
  Deriv (Ctx fh (eqF (ap1 wfRedFull t) O))
mkWfRedFull4 fh t wr wf =
  G4trans (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) O fh
    (l4 fh (wfRedFull_eq t)) (piB4 fh (ap1 wfRed t) (ap1 wfFunRec t) wr wf)

mkChildCjFull4 : (fh : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
  Deriv (Ctx fh (eqF (ap1 wfRedFull child) O)) -> Deriv (Ctx fh (eqF (ap1 conj3 child) O))
mkChildCjFull4 fh child leqCh cvf =
  ap4c (ap4c (l4 fh (QofChildU child leqCh)) (ap4c (l4 fh pa2phik) (get4d negLeaf htag fh PA))) cvf

splitL4 : (fh : Formula) (t : Term) ->
  Deriv (Ctx fh (eqF (ap1 wfRedFull t) O)) -> Deriv (Ctx fh (eqF (ap1 wfRed t) O))
splitL4 fh t d =
  ap4c (l4 fh (piZeroL_imp (ap1 wfRed t) (ap1 wfFunRec t)))
    (G4trans (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O fh
      (G4sym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) fh (l4 fh (wfRedFull_eq t))) d)
splitR4 : (fh : Formula) (t : Term) ->
  Deriv (Ctx fh (eqF (ap1 wfRedFull t) O)) -> Deriv (Ctx fh (eqF (ap1 wfFunRec t) O))
splitR4 fh t d =
  ap4c (l4 fh (piZeroR_imp (ap1 wfRed t) (ap1 wfFunRec t)))
    (G4trans (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) (ap1 wfRedFull t) O fh
      (G4sym (ap1 wfRedFull t) (ap2 pi (ap1 wfRed t) (ap1 wfFunRec t)) fh (l4 fh (wfRedFull_eq t))) d)

gPiL4 : (fh : Formula) (X Y : Term) ->
  Deriv (Ctx fh (eqF (ap2 pi X Y) O)) -> Deriv (Ctx fh (eqF X O))
gPiL4 fh X Y d = ap4c (l4 fh (piZeroL_imp X Y)) d
gPiR4 : (fh : Formula) (X Y : Term) ->
  Deriv (Ctx fh (eqF (ap2 pi X Y) O)) -> Deriv (Ctx fh (eqF Y O))
gPiR4 fh X Y d = ap4c (l4 fh (piZeroR_imp X Y)) d

fromFh : (fh : Formula) {X : Formula} -> Deriv (imp fh X) -> Deriv (Ctx fh X)
fromFh fh d = ap4c (l4 fh d) (get4c negLeaf htag fh PA)

-- a child's qcheck conjunct from its full validity.
childCj : (fh : Formula) (child : Term) -> Deriv (leq child (var 0)) ->
  Deriv (Ctx fh (eqF (ap1 wfRed child) O)) -> Deriv (Ctx fh (eqF (ap1 wfFunRec child) O)) ->
  Deriv (Ctx fh (eqF (ap1 conj3 child) O))
childCj fh child leqCh wr wf = mkChildCjFull4 fh child leqCh (mkWfRedFull4 fh child wr wf)

------------------------------------------------------------------------
-- Term-builder congruences (tmAp1 / tmAp2) in context.

private
  tmAp1ArgImp : (f a b : Term) -> Deriv (imp (eqF a b) (eqF (tmAp1 f a) (tmAp1 f b)))
  tmAp1ArgImp f a b =
    impCongR Pair (ap2 Pair f a) (ap2 Pair f b) tgAp1 (impCongR Pair a b f (identP (eqF a b)))
  tmAp1HeadImp : (f g Yv : Term) -> Deriv (imp (eqF f g) (eqF (tmAp1 f Yv) (tmAp1 g Yv)))
  tmAp1HeadImp f g Yv =
    impCongR Pair (ap2 Pair f Yv) (ap2 Pair g Yv) tgAp1 (impCongL Pair f g Yv (identP (eqF f g)))
  tmAp2Arg1Imp : (gg a a' b : Term) -> Deriv (imp (eqF a a') (eqF (tmAp2 gg a b) (tmAp2 gg a' b)))
  tmAp2Arg1Imp gg a a' b =
    impCongR Pair (ap2 Pair gg (ap2 Pair a b)) (ap2 Pair gg (ap2 Pair a' b)) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a' b) gg (impCongL Pair a a' b (identP (eqF a a'))))
  tmAp2Arg2Imp : (gg a b b' : Term) -> Deriv (imp (eqF b b') (eqF (tmAp2 gg a b) (tmAp2 gg a b')))
  tmAp2Arg2Imp gg a b b' =
    impCongR Pair (ap2 Pair gg (ap2 Pair a b)) (ap2 Pair gg (ap2 Pair a b')) tgAp2
      (impCongR Pair (ap2 Pair a b) (ap2 Pair a b') gg (impCongR Pair b b' a (identP (eqF b b'))))
  tmAp2HeadImp : (f g a b : Term) -> Deriv (imp (eqF f g) (eqF (tmAp2 f a b) (tmAp2 g a b)))
  tmAp2HeadImp f g a b =
    impCongR Pair (ap2 Pair f (ap2 Pair a b)) (ap2 Pair g (ap2 Pair a b)) tgAp2
      (impCongL Pair f g (ap2 Pair a b) (identP (eqF f g)))

G4TmAp1 : (f a b : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF a b)) -> Deriv (Ctx fh (eqF (tmAp1 f a) (tmAp1 f b)))
G4TmAp1 f a b fh d = ap4c (l4 fh (tmAp1ArgImp f a b)) d
G4TmAp1Head : (f g Yv : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF f g)) -> Deriv (Ctx fh (eqF (tmAp1 f Yv) (tmAp1 g Yv)))
G4TmAp1Head f g Yv fh d = ap4c (l4 fh (tmAp1HeadImp f g Yv)) d
G4Ap2Arg1 : (gg a a' b : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF a a')) -> Deriv (Ctx fh (eqF (tmAp2 gg a b) (tmAp2 gg a' b)))
G4Ap2Arg1 gg a a' b fh d = ap4c (l4 fh (tmAp2Arg1Imp gg a a' b)) d
G4Ap2Arg2 : (gg a b b' : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF b b')) -> Deriv (Ctx fh (eqF (tmAp2 gg a b) (tmAp2 gg a b')))
G4Ap2Arg2 gg a b b' fh d = ap4c (l4 fh (tmAp2Arg2Imp gg a b b')) d
G4Ap2Head : (f g a b : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF f g)) -> Deriv (Ctx fh (eqF (tmAp2 f a b) (tmAp2 g a b)))
G4Ap2Head f g a b fh d = ap4c (l4 fh (tmAp2HeadImp f g a b)) d
G4Ap2R : (gg a a' b b' : Term) (fh : Formula) ->
  Deriv (Ctx fh (eqF a a')) -> Deriv (Ctx fh (eqF b b')) ->
  Deriv (Ctx fh (eqF (tmAp2 gg a b) (tmAp2 gg a' b')))
G4Ap2R gg a a' b b' fh dA dB =
  G4trans (tmAp2 gg a b) (tmAp2 gg a' b) (tmAp2 gg a' b') fh
    (G4Ap2Arg1 gg a a' b fh dA) (G4Ap2Arg2 gg a' b b' fh dB)

------------------------------------------------------------------------
-- Cnj-folding:  fold extra funhead antecedents of an opaque eq into  fh .

uncurryImp : (A B Cf : Formula) -> Deriv (imp (imp A (imp B Cf)) (imp (Cnj A B) Cf))
uncurryImp A B Cf =
  let hD = axK (imp A (imp B Cf)) (Cnj A B)
      hA = liftP (imp A (imp B Cf)) (cnjL A B)
      hB = liftP (imp A (imp B Cf)) (cnjR A B)
  in ap2c (ap2c hD hA) hB

-- fold ONE extra antecedent:  imp negLeaf (imp htag (imp A (imp B X)))
--   ->  imp negLeaf (imp htag (imp (Cnj A B) X)) .
fold2 : (A B : Formula) (X : Formula) ->
  Deriv (imp negLeaf (imp htag (imp A (imp B X)))) ->
  Deriv (imp negLeaf (imp htag (imp (Cnj A B) X)))
fold2 A B X d = ap2c (lift2 negLeaf htag (uncurryImp A B X)) d

------------------------------------------------------------------------
-- assembly:  the four endpoint facts  =>  Bgoal .

assembleConj34 : (fh : Formula) ->
  Deriv (Ctx fh (eqF (ap1 wfRedFull (ap1 triF sK)) O)) ->
  Deriv (Ctx fh (eqF (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) ->
  Deriv (Ctx fh (eqF (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) ->
  Deriv (Ctx fh Bgoal)
assembleConj34 fh factV factS factT =
  let eqS = eqDecO (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK)
      eqT = eqDecO (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK))
      sO = ap4c (l4 fh (eqDecO_complete_imp (ap1 srcF (ap1 triF sK)) (ap1 tgtF sK))) factS
      tO = ap4c (l4 fh (eqDecO_complete_imp (ap1 tgtF (ap1 triF sK)) (ap1 devF (ap1 srcF sK)))) factT
      inner = ap4c (ap4c (l4 fh (sigmaBothO_imp eqS eqT)) sO) tO
      outer = ap4c (ap4c (l4 fh (sigmaBothO_imp (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT))) factV) inner
  in G4trans (ap1 conj3 sK) (ap2 sigma (ap1 wfRedFull (ap1 triF sK)) (ap2 sigma eqS eqT)) O fh
       (l4 fh (conj3_unfold sK)) outer

------------------------------------------------------------------------
-- THE GENERIC NODE GLUE.
--
-- Given the residual N and the FOUR per-node facts, produce the goal.  This is
-- the entire rule-independent content of a sub-glue; every rule supplies only
-- (triEq, wrN, wfN, srcN, tgtN).

nodeGlue : (fh : Formula) (N : Term) ->
  Deriv (Ctx fh (eqF (ap1 triF sK) N)) ->
  Deriv (Ctx fh (eqF (ap1 wfRed N) O)) ->
  Deriv (Ctx fh (eqF (ap1 wfFunRec N) O)) ->
  Deriv (Ctx fh (eqF (ap1 srcF N) (ap1 tgtF sK))) ->
  Deriv (Ctx fh (eqF (ap1 tgtF N) (ap1 devF (ap1 srcF sK)))) ->
  Deriv (Ctx fh Bgoal)
nodeGlue fh N triEq wrN wfN srcN tgtN =
  let factV = mkWfRedFull4 fh (ap1 triF sK)
                (G4trans (ap1 wfRed (ap1 triF sK)) (ap1 wfRed N) O fh (G4cong wfRed (ap1 triF sK) N fh triEq) wrN)
                (G4trans (ap1 wfFunRec (ap1 triF sK)) (ap1 wfFunRec N) O fh (G4cong wfFunRec (ap1 triF sK) N fh triEq) wfN)
      factS = G4trans (ap1 srcF (ap1 triF sK)) (ap1 srcF N) (ap1 tgtF sK) fh
                (G4cong srcF (ap1 triF sK) N fh triEq) srcN
      factT = G4trans (ap1 tgtF (ap1 triF sK)) (ap1 tgtF N) (ap1 devF (ap1 srcF sK)) fh
                (G4cong tgtF (ap1 triF sK) N fh triEq) tgtN
  in assembleConj34 fh factV factS factT
