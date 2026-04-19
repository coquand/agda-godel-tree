{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFunCorrect where

open import Guard.Base
open import Guard.Term
open import Guard.Step
open import Guard.ThFun
open import Guard.SubstCorrect

------------------------------------------------------------------------
-- Proof witness: a tree p such that thFun p = codeEqn eq

Proof : Equation -> Set
Proof eq = Sigma Tree (\p -> Eq (thFun p) (codeEqn eq))

------------------------------------------------------------------------
-- Structural rule helpers

thm14Sym : {t u : Term} -> Proof (eqn t u) -> Proof (eqn u t)
thm14Sym {t} {u} (mkSigma p pf) =
  mkSigma (encSym p) (eqCong (\eq -> nd (rightT eq) (leftT eq)) pf)

thm14Trans : {t u v : Term} -> Proof (eqn t u) -> Proof (eqn u v) -> Proof (eqn t v)
thm14Trans {t} {u} {v} (mkSigma p1 pf1) (mkSigma p2 pf2) =
  mkSigma (encTrans p1 p2)
          (eqCong2 (\eq1 eq2 -> nd (leftT eq1) (rightT eq2)) pf1 pf2)

thm14Cong1 : {t u : Term} (f : Fun1) -> Proof (eqn t u) ->
             Proof (eqn (ap1 f t) (ap1 f u))
thm14Cong1 {t} {u} f (mkSigma p pf) =
  mkSigma (encCong1 (codeF1 f) p)
          (eqCong (\eq -> nd (mkAp1 (codeF1 f) (leftT eq))
                             (mkAp1 (codeF1 f) (rightT eq))) pf)

thm14CongL : {t u : Term} (g : Fun2) (x : Term) -> Proof (eqn t u) ->
             Proof (eqn (ap2 g t x) (ap2 g u x))
thm14CongL {t} {u} g x (mkSigma p pf) =
  mkSigma (encCongL (codeF2 g) (code x) p)
          (eqCong (\eq -> nd (mkAp2 (codeF2 g) (leftT eq) (code x))
                             (mkAp2 (codeF2 g) (rightT eq) (code x))) pf)

thm14CongR : {t u : Term} (g : Fun2) (x : Term) -> Proof (eqn t u) ->
             Proof (eqn (ap2 g x t) (ap2 g x u))
thm14CongR {t} {u} g x (mkSigma p pf) =
  mkSigma (encCongR (codeF2 g) (code x) p)
          (eqCong (\eq -> nd (mkAp2 (codeF2 g) (code x) (leftT eq))
                             (mkAp2 (codeF2 g) (code x) (rightT eq))) pf)

thm14Inst : {l r' : Term} (x : Nat) (t : Term) ->
            Proof (eqn l r') -> Proof (eqn (subst x t l) (subst x t r'))
thm14Inst {l} {r'} x t (mkSigma p pf) =
  mkSigma (encInst (code t) (natCode x) p)
    (eqTrans (eqCong (\eq -> nd (codedSubst (code t) (natCode x) (leftT eq))
                                (codedSubst (code t) (natCode x) (rightT eq))) pf)
             (eqCong2 nd (csCorrect t x l) (csCorrect t x r')))

-- Schema F: thFun(encF fC gC zC sC sp1 sp2 sp3 sp4) = nd(mkAp1 fC var0C)(mkAp1 gC var0C)
thm14F : (f g : Fun1) (z : Term) (s : Fun2) ->
         Proof (eqn (ap1 f O) z) ->
         Proof (eqn (ap1 f (ap2 Pair (var zero) (var (suc zero))))
                    (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                           (ap2 Pair (ap1 f (var zero)) (ap1 f (var (suc zero)))))) ->
         Proof (eqn (ap1 g O) z) ->
         Proof (eqn (ap1 g (ap2 Pair (var zero) (var (suc zero))))
                    (ap2 s (ap2 Pair (var zero) (var (suc zero)))
                           (ap2 Pair (ap1 g (var zero)) (ap1 g (var (suc zero)))))) ->
         Proof (eqn (ap1 f (var zero)) (ap1 g (var zero)))
thm14F f g z s (mkSigma p1 pf1) (mkSigma p2 pf2) (mkSigma p3 pf3) (mkSigma p4 pf4) =
  mkSigma (encF (codeF1 f) (codeF1 g) (code z) (codeF2 s) p1 p2 p3 p4) refl

------------------------------------------------------------------------
-- Theorem 14

thm14 : {hyp : Equation} {eq : Equation} ->
        Deriv hyp eq -> Proof hyp -> Proof eq
thm14 (axI t) ph = mkSigma (encAxI (code t)) refl
thm14 (axFst a b) ph = mkSigma (encAxFst (code a) (code b)) refl
thm14 (axSnd a b) ph = mkSigma (encAxSnd (code a) (code b)) refl
thm14 (axConst a b) ph = mkSigma (encAxConst (code a) (code b)) refl
thm14 (axComp f g t) ph = mkSigma (encAxComp (codeF1 f) (codeF1 g) (code t)) refl
thm14 (axComp2 h f g t) ph = mkSigma (encAxComp2 (codeF2 h) (codeF1 f) (codeF1 g) (code t)) refl
thm14 (axLift f a b) ph = mkSigma (encAxLift (codeF1 f) (code a) (code b)) refl
thm14 (axPost f h a b) ph = mkSigma (encAxPost (codeF1 f) (codeF2 h) (code a) (code b)) refl
thm14 (axFan h1 h2 h a b) ph = mkSigma (encAxFan (codeF2 h1) (codeF2 h2) (codeF2 h) (code a) (code b)) refl
thm14 (axKT t x) ph = mkSigma (encAxKT (code t) (code x)) refl
thm14 (axRecLf z s) ph = mkSigma (encAxRecLf (code z) (codeF2 s)) refl
thm14 (axRecNd z s a b) ph = mkSigma (encAxRecNd (code z) (codeF2 s) (code a) (code b)) refl
thm14 (axIfLfL a b) ph = mkSigma (encAxIfLfL (code a) (code b)) refl
thm14 (axIfLfN x y a b) ph = mkSigma (encAxIfLfN (code x) (code y) (code a) (code b)) refl
thm14 axTreeEqLL ph = mkSigma encAxTreeEqLL refl
thm14 (axTreeEqLN a b) ph = mkSigma (encAxTreeEqLN (code a) (code b)) refl
thm14 (axTreeEqNL a b) ph = mkSigma (encAxTreeEqNL (code a) (code b)) refl
thm14 (axTreeEqNN a1 a2 b1 b2) ph = mkSigma (encAxTreeEqNN (code a1) (code a2) (code b1) (code b2)) refl
thm14 (axRefl t) ph = mkSigma (encRefl (code t)) refl
thm14 (ruleSym d) ph = thm14Sym (thm14 d ph)
thm14 (ruleTrans d1 d2) ph = thm14Trans (thm14 d1 ph) (thm14 d2 ph)
thm14 (cong1 f d) ph = thm14Cong1 f (thm14 d ph)
thm14 (congL g x d) ph = thm14CongL g x (thm14 d ph)
thm14 (congR g x d) ph = thm14CongR g x (thm14 d ph)
thm14 (ruleInst x t {eqn l r'} d) ph = thm14Inst x t (thm14 d ph)
thm14 ruleHyp ph = ph
thm14 (ruleF f g z s bf sf bg sg) ph = thm14F f g z s (thm14 bf ph) (thm14 sf ph) (thm14 bg ph) (thm14 sg ph)
