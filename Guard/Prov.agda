{-# OPTIONS --safe --without-K --exact-split #-}

-- Guard.Prov -- provability predicate and combinators.
--
-- Per UNIFIED-DESIGN-REV2-5C.md step 2.  Prov packages an encoded
-- proof tree with its thmT-correctness witness.
--
-- Design note.  The spec signature for Prov is a plain Sigma:
--
--   Prov P = Sigma (e : Term) (Deriv (atomic (eqn (ap1 thmT e)
--                                             (reify (codeFormula P)))))
--
-- In order to compose proofs via the encoders from
-- Guard.ProofEncUnify / Guard.ProofEncFormula, each combinator needs
-- (i) a Pair decomposition of the encoded Term  e , and (ii) a
-- tag-opacity witness ("Pass") on  e  -- the fact that  e  is a
-- valid outer encoding, not a raw natCode.  Both pieces are
-- standard (every existing encoder satisfies them), so we bundle
-- them in the record  Prov  itself.  A plain Sigma view is
-- recovered via  provToSigma  for consumers who only need the
-- bare correctness witness.
--
-- Combinators exposed in this module:
--   provRefl   -- reflexivity             axRefl t.
--   provSym    -- symmetry                encRuleSym.
--   (more to come in a subsequent commit: provTrans, provCongL,
--    provCongR, provMp, provInst.)

module Guard.Prov where

open import Guard.Base
open import Guard.Term
open import Guard.Formula
open import Guard.DerivF
open import Guard.ThFunTForHF using (thmT ; ndDispatchV3)
open import Guard.ThFunTForDefs using (sndArg2)
open import Guard.ThFun using (codeEqn)
open import Guard.ThFunTForV3DefsUnify using (intermediateGenericV3)
open import Guard.ThFunTForV3PassUnify using (ndDispatchV3PairMiss ; passthroughSucV3)
open import Guard.SubstOpUnify using (substOp ; substOpCorrect)
open import Guard.ProofEncUnify using
  ( encAxRefl ; encAxReflCorr ; encAxReflPass
  ; encRuleSym ; encRuleSymCorr ; encRuleSymPass
  ; encRuleTrans ; encRuleTransCorr ; encRuleTransPass
  ; encCongL ; encCongLCorr ; encCongLPass
  ; encCongR ; encCongRCorr ; encCongRPass
  ; encRuleCong1 ; encRuleCong1Corr ; encRuleCong1Pass
  ; encRuleInst ; encRuleInstCorr ; encRuleInstPass
  )
open import Guard.ProofEncFormula using
  ( encMp ; encMpCorr ; encMpPass
  )
open import Guard.TreeEqSelfUnify using (treeEqSelf)

------------------------------------------------------------------------
-- The provability predicate (rich form).
--
-- Prov P packages:
--   * prov1, prov2      : the outer Pair components of the encoded
--                         proof tree.  (We always compose encoded
--                         proofs as  ap2 Pair prov1 prov2 .)
--   * provCorr          : thmT applied to the encoded tree yields
--                         the Gödel code of the formula being proved.
--   * provPass          : tag-opacity.  When used as the tag of a
--                         larger Pair, this encoding's head does not
--                         match any ndDispatchV3 branch, so dispatch
--                         falls through to sndArg2.

record Prov (P : Formula) : Set where
  constructor mkProv
  field
    prov1    : Term
    prov2    : Term
    provCorr : Deriv (eqF (ap1 thmT (ap2 Pair prov1 prov2))
                          (reify (codeFormula P)))
    provPass : (x rcs : Term) ->
      Deriv (eqF (ap2 ndDispatchV3
                       (ap2 Pair (ap2 Pair prov1 prov2) x) rcs)
                 (ap2 sndArg2
                       (ap2 Pair (ap2 Pair prov1 prov2) x) rcs))
open Prov public

------------------------------------------------------------------------
-- Tag-number aliases for the encoders we reference below.

private
  n0  : Nat ; n0  = zero
  n1  : Nat ; n1  = suc n0
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n4  : Nat ; n4  = suc n3
  n5  : Nat ; n5  = suc n4
  n6  : Nat ; n6  = suc n5
  n7  : Nat ; n7  = suc n6
  n8  : Nat ; n8  = suc n7
  n9  : Nat ; n9  = suc n8
  n10 : Nat ; n10 = suc n9
  n11 : Nat ; n11 = suc n10
  n12 : Nat ; n12 = suc n11
  n13 : Nat ; n13 = suc n12
  n14 : Nat ; n14 = suc n13
  n15 : Nat ; n15 = suc n14
  n16 : Nat ; n16 = suc n15
  n17 : Nat ; n17 = suc n16
  n18 : Nat ; n18 = suc n17
  n19 : Nat ; n19 = suc n18
  n20 : Nat ; n20 = suc n19
  n21 : Nat ; n21 = suc n20
  n22 : Nat ; n22 = suc n21
  n23 : Nat ; n23 = suc n22
  n24 : Nat ; n24 = suc n23
  n25 : Nat ; n25 = suc n24
  n26 : Nat ; n26 = suc n25
  n27 : Nat ; n27 = suc n26
  n28 : Nat ; n28 = suc n27
  n29 : Nat ; n29 = suc n28
  n30 : Nat ; n30 = suc n29
  n31 : Nat ; n31 = suc n30
  n32 : Nat ; n32 = suc n31
  n33 : Nat ; n33 = suc n32

------------------------------------------------------------------------
-- Full encoded Term of a proof.

provTerm : {P : Formula} -> Prov P -> Term
provTerm p = ap2 Pair (prov1 p) (prov2 p)

------------------------------------------------------------------------
-- Spec-level Sigma projection.

provToSigma : {P : Formula} -> Prov P ->
  Sigma Term (\ e -> Deriv (eqF (ap1 thmT e) (reify (codeFormula P))))
provToSigma p = mkSigma (provTerm p) (provCorr p)

------------------------------------------------------------------------
-- provRefl: reflexivity.  For any Term t, t = t is provable.
--
-- Uses encAxRefl / encAxReflCorr / encAxReflPass from
-- Guard.ProofEncUnify.
--
--   encAxRefl tC = ap2 Pair (reify (natCode n17)) (ap2 Pair tC O)
--
-- where tC = reify (code t).
-- Target codeFormula (atomic (eqn t t))
--      = codeEqn (eqn t t)
--      = nd (code t) (code t).
-- reify of that = ap2 Pair tC tC, which encAxReflCorr delivers.

provRefl : (t : Term) -> Prov (atomic (eqn t t))
provRefl t =
  let tC : Term ; tC = reify (code t) in
  mkProv
    (reify (natCode n17))
    (ap2 Pair tC O)
    (encAxReflCorr tC)
    (\ x rcs -> encAxReflPass t x rcs)

------------------------------------------------------------------------
-- provSym: symmetry.  From  t = u  conclude  u = t .
--
-- Wraps encRuleSym.  The input's  prov1 , prov2  become the
-- sub-encoding's  paR , pbR  for encRuleSymCorr; tC , uC  are the
-- reified codes of the equation's sides.
--
--   encRuleSym enc = ap2 Pair (reify (natCode n18))
--                             (ap2 Pair (reify tagVar) enc)
--
-- so the output's outer Pair decomposition is
--   prov1_out = reify (natCode n18)
--   prov2_out = ap2 Pair (reify tagVar) enc_in .

provSym : (t u : Term) -> Prov (atomic (eqn t u)) ->
          Prov (atomic (eqn u t))
provSym t u p =
  let paR : Term ; paR = prov1 p
      pbR : Term ; pbR = prov2 p
      tC  : Term ; tC  = reify (code t)
      uC  : Term ; uC  = reify (code u)
  in mkProv
       (reify (natCode n18))
       (ap2 Pair (reify tagVar) (ap2 Pair paR pbR))
       (encRuleSymCorr paR pbR tC uC (provCorr p))
       (\ x rcs -> encRuleSymPass paR pbR x rcs)

------------------------------------------------------------------------
-- thmT-over-Pair adapter.
--
-- Given Prov witnesses for P and Q, build the "thmT of the Pair
-- of the two encoded proofs" equation that combinators like
-- encMpCorr / encRuleTransCorr expect as their bodyCorr.
--
-- The key step is  intermediateGenericV3 : thmT unfolds through a
-- Pair whose outer tag is tag-opaque (which every encoded proof is,
-- via its  Pass  lemma).  Here the outer tag is the first proof's
-- Term, playing the role of  tagT  in intermediateGenericV3.

thmTOverPair :
  {P Q : Formula} (p : Prov P) (q : Prov Q) ->
  Deriv (eqF (ap1 thmT (ap2 Pair (provTerm p) (provTerm q)))
             (ap2 Pair (reify (codeFormula P)) (reify (codeFormula Q))))
thmTOverPair {P} {Q} p q =
  let pT : Term ; pT = provTerm p
      qT : Term ; qT = provTerm q
      codeP : Term ; codeP = reify (codeFormula P)
      step1 :
        Deriv (eqF (ap1 thmT (ap2 Pair pT (ap2 Pair (prov1 q) (prov2 q))))
                   (ap2 Pair (ap1 thmT pT)
                             (ap1 thmT (ap2 Pair (prov1 q) (prov2 q)))))
      step1 = intermediateGenericV3 pT qT (prov1 q) (prov2 q) (provPass p)
      step2 :
        Deriv (atomic (eqn (ap2 Pair (ap1 thmT pT) (ap1 thmT qT))
                           (ap2 Pair codeP (ap1 thmT qT))))
      step2 = congL Pair (ap1 thmT qT) (provCorr p)
      step3 :
        Deriv (atomic (eqn (ap2 Pair codeP (ap1 thmT qT))
                           (ap2 Pair codeP (reify (codeFormula Q)))))
      step3 = congR Pair codeP (provCorr q)
  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- provMp: formula-level modus ponens.
--
-- From Prov P and Prov (P imp Q) conclude Prov Q.  Wraps encMp /
-- encMpCorr with bodyCorr supplied by thmTOverPair.

provMp : {P Q : Formula} -> Prov P -> Prov (P imp Q) -> Prov Q
provMp {P} {Q} pP pPQ =
  let sub1 : Term ; sub1 = provTerm pP
      sub2 : Term ; sub2 = provTerm pPQ
      body : Deriv (eqF (ap1 thmT (ap2 Pair sub1 sub2))
                        (ap2 Pair (reify (codeFormula P))
                                  (reify (codeFormula (P imp Q)))))
      body = thmTOverPair {P} {P imp Q} pP pPQ
  in mkProv
       (reify (natCode n33))
       (ap2 Pair sub1 sub2)
       (encMpCorr sub1 sub2 P Q body)
       (\ x rcs -> encMpPass sub1 sub2 x rcs)

------------------------------------------------------------------------
-- provTrans: equational transitivity.  From  t = u  and  u = v ,
-- conclude  t = v .
--
-- Wraps encRuleTrans / encRuleTransCorr.  Supplies  pass1  from the
-- first Prov's provPass and  uCSelf  from treeEqSelf.

provTrans : (t u v : Term) ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn u v)) ->
            Prov (atomic (eqn t v))
provTrans t u v p q =
  let pa1R : Term ; pa1R = prov1 p
      pb1R : Term ; pb1R = prov2 p
      pa2R : Term ; pa2R = prov1 q
      pb2R : Term ; pb2R = prov2 q
      tC   : Term ; tC   = reify (code t)
      uC   : Term ; uC   = reify (code u)
      vC   : Term ; vC   = reify (code v)
  in mkProv
       (reify (natCode n19))
       (ap2 Pair (ap2 Pair pa1R pb1R) (ap2 Pair pa2R pb2R))
       (encRuleTransCorr pa1R pb1R pa2R pb2R tC uC vC
          (provPass p) (provCorr p) (provCorr q) (treeEqSelf uC))
       (\ x rcs -> encRuleTransPass pa1R pb1R pa2R pb2R x rcs)

------------------------------------------------------------------------
-- dispMiss for tag  Pair (reify (codeF2 g)) xC  used inside
-- encCongL / encCongR.  ndDispatchV3 does not match any branch
-- because the outer head is itself a Pair (the reified codeF2 g).
--
-- Case analysis on g: codeF2 g = nd (natCode N_g) body_g , so
-- reify(codeF2 g) = Pair (reify (natCode N_g)) (reify body_g) , and
-- ndDispatchV3PairMiss applies with a1 = reify (natCode N_g),
-- a2 = reify body_g , b = xC.

f2xDispMiss : (g : Fun2) (xC x' rc' : Term) ->
  Deriv (eqF (ap2 ndDispatchV3
                   (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) x') rc')
             (ap2 sndArg2
                   (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) x') rc'))
f2xDispMiss Pair          xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n26)) O xC x' rc'
f2xDispMiss Const         xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n27)) O xC x' rc'
f2xDispMiss (Lift f)      xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n28)) (reify (codeF1 f)) xC x' rc'
f2xDispMiss (Post f h)    xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n29))
    (ap2 Pair (reify (codeF1 f)) (reify (codeF2 h))) xC x' rc'
f2xDispMiss (Fan h1 h2 h) xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n30))
    (ap2 Pair (reify (codeF2 h1))
              (ap2 Pair (reify (codeF2 h2)) (reify (codeF2 h))))
    xC x' rc'
f2xDispMiss IfLf          xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n31)) O xC x' rc'
f2xDispMiss TreeEq        xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n32)) O xC x' rc'
f2xDispMiss (RecP s)      xC x' rc' =
  ndDispatchV3PairMiss (reify (natCode n33))
    (reify (codeF2 s)) xC x' rc'

------------------------------------------------------------------------
-- provCongL: left-argument congruence for a binary functor.  From
--  t = u  conclude  g t x = g u x .
--
-- Wraps encCongL / encCongLCorr.  f2xDispMiss supplies the inner-tag
-- tag-opacity for  Pair (reify (codeF2 g)) xC .

provCongL : (g : Fun2) (x : Term) {t u : Term} ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap2 g t x) (ap2 g u x)))
provCongL g x {t} {u} p =
  let paR : Term ; paR = prov1 p
      pbR : Term ; pbR = prov2 p
      xC  : Term ; xC  = reify (code x)
      tC  : Term ; tC  = reify (code t)
      uC  : Term ; uC  = reify (code u)
  in mkProv
       (reify (natCode n21))
       (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) (ap2 Pair paR pbR))
       (encCongLCorr g xC paR pbR tC uC (f2xDispMiss g xC) (provCorr p))
       (\ x' rcs -> encCongLPass g xC paR pbR x' rcs)

------------------------------------------------------------------------
-- provCongR: right-argument congruence for a binary functor.  From
--  t = u  conclude  g x t = g x u .

provCongR : (g : Fun2) (x : Term) {t u : Term} ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap2 g x t) (ap2 g x u)))
provCongR g x {t} {u} p =
  let paR : Term ; paR = prov1 p
      pbR : Term ; pbR = prov2 p
      xC  : Term ; xC  = reify (code x)
      tC  : Term ; tC  = reify (code t)
      uC  : Term ; uC  = reify (code u)
  in mkProv
       (reify (natCode n22))
       (ap2 Pair (ap2 Pair (reify (codeF2 g)) xC) (ap2 Pair paR pbR))
       (encCongRCorr g xC paR pbR tC uC (f2xDispMiss g xC) (provCorr p))
       (\ x' rcs -> encCongRPass g xC paR pbR x' rcs)

------------------------------------------------------------------------
-- dispMiss for tag  reify (codeF1 f)  used inside encRuleCong1.
-- For every Fun1 constructor, codeF1 f = nd (natCode N_f) body_f
-- with  N_f > 0  (tags start at n26), so reify(codeF1 f) has outer
-- shape  Pair O (reify (natCode (N_f - 1)))  paired with reify body_f,
-- matching  passthroughSucV3 .

f1DispMiss : (f : Fun1) (x' rc' : Term) ->
  Deriv (eqF (ap2 ndDispatchV3 (ap2 Pair (reify (codeF1 f)) x') rc')
             (ap2 sndArg2     (ap2 Pair (reify (codeF1 f)) x') rc'))
f1DispMiss I              x' rc' =
  passthroughSucV3 n25 lf x' rc'
f1DispMiss Fst            x' rc' =
  passthroughSucV3 n26 lf x' rc'
f1DispMiss Snd            x' rc' =
  passthroughSucV3 n27 lf x' rc'
f1DispMiss (Comp f g)     x' rc' =
  passthroughSucV3 n28 (nd (codeF1 f) (codeF1 g)) x' rc'
f1DispMiss (Comp2 h f g)  x' rc' =
  passthroughSucV3 n29 (nd (codeF2 h) (nd (codeF1 f) (codeF1 g))) x' rc'
f1DispMiss (Rec z s)      x' rc' =
  passthroughSucV3 n30 (nd (code z) (codeF2 s)) x' rc'
f1DispMiss (KT t)         x' rc' =
  passthroughSucV3 n31 (code t) x' rc'

------------------------------------------------------------------------
-- provCong1: unary-functor congruence.  From  t = u  conclude
--  f t = f u  for any Fun1  f .

provCong1 : (f : Fun1) {t u : Term} ->
            Prov (atomic (eqn t u)) ->
            Prov (atomic (eqn (ap1 f t) (ap1 f u)))
provCong1 f {t} {u} p =
  let paR : Term ; paR = prov1 p
      pbR : Term ; pbR = prov2 p
      tC  : Term ; tC  = reify (code t)
      uC  : Term ; uC  = reify (code u)
  in mkProv
       (reify (natCode n20))
       (ap2 Pair (reify (codeF1 f)) (ap2 Pair paR pbR))
       (encRuleCong1Corr f paR pbR tC uC (f1DispMiss f) (provCorr p))
       (\ x' rcs -> encRuleCong1Pass f paR pbR x' rcs)

------------------------------------------------------------------------
-- dispMiss for tag  Pair (reify (code t)) (reify (natCode x))  used
-- inside encRuleInst.  Case analysis on t: code t is always of shape
-- nd tag_t body_t, so reify(code t) = Pair (reify tag_t) (reify body_t)
-- and the full tag has shape  Pair (Pair _ _) _ .

aRDispMiss : (t : Term) (x : Nat) (x' rc' : Term) ->
  Deriv (eqF (ap2 ndDispatchV3
                   (ap2 Pair
                     (ap2 Pair (reify (code t)) (reify (natCode x))) x') rc')
             (ap2 sndArg2
                   (ap2 Pair
                     (ap2 Pair (reify (code t)) (reify (natCode x))) x') rc'))
aRDispMiss O          x x' rc' =
  ndDispatchV3PairMiss O O (reify (natCode x)) x' rc'
aRDispMiss (var n)    x x' rc' =
  ndDispatchV3PairMiss (reify tagVar) (reify (natCode n))
                                (reify (natCode x)) x' rc'
aRDispMiss (ap1 f t)  x x' rc' =
  ndDispatchV3PairMiss (reify tagAp1)
    (ap2 Pair (reify (codeF1 f)) (reify (code t)))
    (reify (natCode x)) x' rc'
aRDispMiss (ap2 g a b) x x' rc' =
  ndDispatchV3PairMiss (reify tagAp2)
    (ap2 Pair (reify (codeF2 g)) (ap2 Pair (reify (code a)) (reify (code b))))
    (reify (natCode x)) x' rc'

------------------------------------------------------------------------
-- provInst: substitution (Guard's rule (i)) for atomic equations.
--
-- From  l = r'  conclude  subst x t l = subst x t r' .
--
-- Wraps encRuleInst / encRuleInstCorr.  Inner aR is
-- Pair (reify (code t)) (reify (natCode x)) ; aRDispMiss discharges
-- its tag-opacity.  The Term-level  substOp  output is bridged to
--  reify (code (subst x t _))  via substOpCorrect.

provInst : (x : Nat) (t : Term) {l r' : Term} ->
           Prov (atomic (eqn l r')) ->
           Prov (atomic (eqn (subst x t l) (subst x t r')))
provInst x t {l} {r'} p =
  let paR : Term ; paR = prov1 p
      pbR : Term ; pbR = prov2 p
      lC  : Term ; lC  = reify (code l)
      r'C : Term ; r'C = reify (code r')
      aR  : Term ; aR  = ap2 Pair (reify (code t)) (reify (natCode x))
      step1 :
        Deriv (eqF (ap1 thmT (encRuleInst aR (ap2 Pair paR pbR)))
                   (ap2 Pair (ap2 substOp aR lC)
                             (ap2 substOp aR r'C)))
      step1 = encRuleInstCorr aR paR pbR lC r'C
                (aRDispMiss t x) (provCorr p)
      step2 :
        Deriv (atomic (eqn (ap2 Pair (ap2 substOp aR lC)
                                     (ap2 substOp aR r'C))
                           (ap2 Pair (reify (code (subst x t l)))
                                     (reify (code (subst x t r'))))))
      step2 =
        ruleTrans
          (congL Pair (ap2 substOp aR r'C) (substOpCorrect t x l))
          (congR Pair (reify (code (subst x t l)))
                 (substOpCorrect t x r'))
  in mkProv
       (reify (natCode n23))
       (ap2 Pair aR (ap2 Pair paR pbR))
       (ruleTrans step1 step2)
       (\ x' rcs -> encRuleInstPass aR paR pbR x' rcs)
