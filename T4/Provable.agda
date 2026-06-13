{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.Provable -- object-level provability predicate built on the new
-- closed existential former  E : Fun1 -> Formula .
--
--   Provable A  :=  E (provFun A)
--
-- where  provFun A : Fun1  maps a candidate proof-code  x  to
--   sub (s O) (natEqF (thmT x) (codeFormula A))
-- which equals  O  exactly when  natEqF (thmT x) (codeFormula A) = s O ,
-- i.e. exactly when  thmT  accepts  x  as a checked proof of  A .  So
--   Provable A  =  "exists x. thmT x = codeFormula A" .

module T4.Provable where

open import T4.Base
open import T4.Code            using ( codeFormula )
open import T4.ThmT            using ( thmT )
open import T4.Encode          using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.CodeCantorCollapse using ( natEqF_codeF_refl )
open import T4.NegAtomCode     using ( NoVar_codeFormula )
open import T4.Thm12.ConstTermFun1 using ( constTermFun1 ; constTermFun1_eq ; NoVar )

open import BRA3.Church        using ( sub )
open import BRA3.SubT.NatEq    using ( natEqF )
open import BRA3.RecBRA3AtPairUniv using ( sub_self )
open import BRA3.Logic         using ( impTrans )

------------------------------------------------------------------------
-- provFun A :  x |-> sub (s O) (natEqF (thmT x) (codeFormula A)) .
-- ap1 (provFun A) x = ap2 sub (ap1 s O) (ap2 natEqF (ap1 thmT x) (codeFormula A)).

provFun : Formula -> Fun1
provFun A = C sub (constTermFun1 (ap1 s O))
                  (C natEqF thmT (constTermFun1 (codeFormula A)))

------------------------------------------------------------------------
-- Provable A := E (provFun A) -- a CLOSED formula.

Provable : Formula -> Formula
Provable A = E (provFun A)

------------------------------------------------------------------------
-- Necessitation :  Deriv A  ->  Deriv (Provable A) .
--
-- The proof-code  encode dA  is the EXISTENTIAL WITNESS supplied to
-- E_intro : it is the (large) term hidden behind the  E , while the
-- formula  Provable A  itself depends only on  codeFormula A .  At the
-- witness,  thmT (encode dA) = codeFormula A  (thmT-completeness), so
-- the  natEqF -test returns  s O  and  provFun A  evaluates to  O .

necessitation : {A : Formula} (dA : Deriv A) -> Deriv (Provable A)
necessitation {A} dA =
  let t : Term
      t = encode dA

      cA : Term
      cA = codeFormula A

      h2 : Fun1
      h2 = C natEqF thmT (constTermFun1 cA)

      -- (1)  ap1 (provFun A) t = ap2 sub (ap1 (constTermFun1 (s O)) t) (ap1 h2 t) .
      e1 : Deriv (eqF (ap1 (provFun A) t)
                       (ap2 sub (ap1 (constTermFun1 (ap1 s O)) t) (ap1 h2 t)))
      e1 = ax_C sub (constTermFun1 (ap1 s O)) h2 t

      -- (2)  first sub-arg :  ap1 (constTermFun1 (s O)) t = s O .
      h1_eq : Deriv (eqF (ap1 (constTermFun1 (ap1 s O)) t) (ap1 s O))
      h1_eq = constTermFun1_eq (ap1 s O) tt t

      -- (3)  second sub-arg :  ap1 h2 t = natEqF (thmT t) (codeFormula A) .
      h2_eq : Deriv (eqF (ap1 h2 t) (ap2 natEqF (ap1 thmT t) cA))
      h2_eq =
        ruleTrans (ax_C natEqF thmT (constTermFun1 cA) t)
                  (congR natEqF (ap1 thmT t)
                         (constTermFun1_eq cA (NoVar_codeFormula A) t))

      -- (4)  ap1 (provFun A) t = sub (s O) (natEqF (thmT t) (codeFormula A)) .
      e2 : Deriv (eqF (ap1 (provFun A) t)
                       (ap2 sub (ap1 s O) (ap2 natEqF (ap1 thmT t) cA)))
      e2 = ruleTrans e1
             (ruleTrans (congL sub (ap1 h2 t) h1_eq)
                        (congR sub (ap1 s O) h2_eq))

      -- (5)  thmT t = codeFormula A   (verifier-completeness at the witness).
      ih : Deriv (eqF (ap1 thmT t) cA)
      ih = thmT_complete_rec dA

      -- (6)  natEqF (thmT t) (codeFormula A) = s O .
      natEqF_sO : Deriv (eqF (ap2 natEqF (ap1 thmT t) cA) (ap1 s O))
      natEqF_sO = ruleTrans (congL natEqF cA ih) (natEqF_codeF_refl A)

      -- (7)  sub (s O) (s O) = O .
      sub_O : Deriv (eqF (ap2 sub (ap1 s O) (ap1 s O)) O)
      sub_O = sub_self (ap1 s O)

      -- (8)  ap1 (provFun A) t = O .
      provFun_O : Deriv (eqF (ap1 (provFun A) t) O)
      provFun_O =
        ruleTrans e2
          (ruleTrans (congR sub (ap1 s O) natEqF_sO) sub_O)
  in E_intro (provFun A) t provFun_O

------------------------------------------------------------------------
-- E-congruence (the logical core of the Provable-tower bridge).
--
--   If  f  and  g  agree at the eigenvariable  var a  (extensionally),
--   then  E f  entails  E g .  This is exactly what lets a small-coded
--   stage sentence  E gFun_r  be exchanged for  Provable (Tower r) =
--   E (provFun (Tower r))  when their test-Fun1s coincide at  var a .
--
-- The proof needs exists-introduction in IMPLICATION form  -- the
-- axiom  eIntroAx g (var a) : imp (g(va)=O) (E g)  -- which the rule
-- E_intro alone could not supply (the deduction-theorem obstruction).
-- The eigenvariable side condition is trivial : E g is CLOSED.

E_cong :
  (f g : Fun1) (a : Nat) ->
  Deriv (eqF (ap1 f (var a)) (ap1 g (var a))) ->
  Deriv (E f) -> Deriv (E g)
E_cong f g a cong ef =
  let nf : (t : Term) -> Eq (substF a t (E g)) (E g)
      nf t = refl

      -- imp (f(va)=O) (g(va)=O)  via eqTrans on the congruence.
      step1 : Deriv (imp (eqF (ap1 f (var a)) O) (eqF (ap1 g (var a)) O))
      step1 = mp (ax_eqTrans (ap1 f (var a)) (ap1 g (var a)) O) cong

      -- compose with the exists-intro AXIOM  imp (g(va)=O) (E g) .
      minor : Deriv (imp (eqF (ap1 f (var a)) O) (E g))
      minor = impTrans step1 (eIntroAx g (var a))
  in E_elim f a (E g) nf minor ef
