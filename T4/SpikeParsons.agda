{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SpikeParsons -- the explicit Skolem-witness toy for the Kritchman-Raz
-- surprise-exam induction (SPIKE-KR-COMPLEXITY-PARSONS.md).
--
-- THE POINT (the user's complexity test, made concrete in Agda).  The KR
-- induction is on  i  (up to  2^{L+1}+1) over  psi(i) = "T proves (m >= i)" =
-- Pr_T(<m>=i>) , which is Σ₁ (the `exists` is over the PROOF), over a DECIDABLE
-- matrix in BRA (bounded-Comp count, m>=i = comp_count N <= sub N i).  By
-- Parsons (IΣ₁ Π₂-conservative over PRA) Σ₁-induction is fine in a PRA-like
-- system, and the Skolem WITNESS FUNCTION exists.  BRA's  ruleIndNat  is
-- quantifier-free induction ONLY (no object `exists`), so the Σ₁ is SKOLEMIZED
-- to a QF motive with an EXPLICIT primitive-recursive proof-builder  q : Fun1 :
--
--   INV(j) := eqF (ap1 thmT (ap1 q j)) (ap1 cMGE j)        -- "thmT proves m>=j"
--   q O      = O
--   q (s j)  = cmp (necCode j) (q j)                       -- a genuine R-recursion
--
-- This file builds  q  CONCRETELY (a Fun1, R-built), proves its recursion
-- equations, and assembles the induction with the REAL thmT-internal modus
-- ponens (D3 = imp_encoded_mp) for the stepReal and a CONCRETE Con-finish (D3 +
-- ConSchema + axExFalso, the con_inj shape).  Only the thmT-CONTENT facts
-- (cMGE/necCode the formula/proof-code builders, and  dBaseNec / dStepNec /
-- dRef  the D1-necessitations that KR-A/Chaitin will realise) are PARAMETERS --
-- exactly the SpikeD/SpikeB/SpikeC methodology.  No  closeCoe : the range  N
-- never appears in the QF motive (only  q / cMGE , which are Fun1), so
-- ruleIndNat + ruleInst at the Bin-compressed  s N  are capture-free.
--
-- What this validates: the Parsons-Skolemization of the Σ₁ surprise-exam
-- induction is genuinely MECHANIZABLE with the real D1/D3 machinery -- the one
-- thing the complexity argument says SHOULD work and that SpikeD left abstract.
-- The Agda term stays poly(ell): ONE rule + ruleInst at Bin  N+1 , never the
-- exp-length meta-induction (feasibility = SPIKE-A/KR-B exp-totality).

module T4.SpikeParsons where

open import T4.Base
open import T4.Code   using ( codeFalse ; falseF )
open import T4.Tags   using ( tag_imp ; tag_mp )
open import T4.ThmT   using ( thmT )
open import T4.Thm12.EncodedMp using ( encoded_mp ; imp_encoded_mp )

open import T4.CountingObj using ( identImp )

open import BRA3.Logic          using ( prependEqLeft )
open import BRA3.Contrapositive using ( axExFalso ; compI ; liftP )

------------------------------------------------------------------------
-- Code-builders shared with ConInj / SpikeChaitin.

cimp : Term -> Term -> Term
cimp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

cmp : Term -> Term -> Term
cmp pImp pA = ap2 Pair (natCode tag_mp) (ap2 Pair pImp pA)

ConSchema : Formula
ConSchema = neg (eqF (ap1 thmT (var zero)) codeFalse)

------------------------------------------------------------------------
-- The Skolemized Σ₁ surprise-exam induction.

module Induction
  (N : Term)                       -- the (Bin-compressed) range bound  2^{L+1}
  (cMGE : Fun1)                    -- ap1 cMGE j = code of the Δ₀ formula "m >= j"
  (necCode : Fun1)                 -- ap1 necCode j = proof-code of "m>=j -> m>=j+1"
  (con : Deriv ConSchema)          -- Con(T)
  (cRef : Term)                    -- proof-code of "m>=N+1 -> 0=1" (the count refutation)
  -- D1 necessitations (KR-A/Chaitin realise these; here parameters):
  (dBaseNec : Deriv (eqF (ap1 thmT O) (ap1 cMGE O)))                   -- thmT proves m>=0
  (dStepNec : (j : Term) ->                                            -- thmT proves (m>=j -> m>=j+1)
       Deriv (eqF (ap1 thmT (ap1 necCode j))
                  (cimp (ap1 cMGE j) (ap1 cMGE (ap1 s j)))))
  (dRef : Deriv (eqF (ap1 thmT cRef)                                   -- thmT proves (m>=N+1 -> 0=1)
                     (cimp (ap1 cMGE (ap1 s N)) codeFalse)))
  where

  ------------------------------------------------------------------------
  -- SECTION 1.  The explicit Skolem proof-builder  q : Fun1 .
  --   ap1 q O      = O
  --   ap1 q (s j)  = cmp (necCode j) (ap1 q j)
  -- via the BRA recursor R, recursing on the argument (first arg fixed to O).

  stepFun : Fun2
  stepFun = Fan (Lift1 (constN tag_mp))
                (Fan (Lift1 (compose1U necCode Snd)) v Pair)
                Pair

  qRec : Fun2
  qRec = R o stepFun Pair

  q : Fun1
  q = C qRec o u

  -- stepFun (Pair x j) prev = cmp (necCode j) prev.
  stepFun_eq :
    (x j prev : Term) ->
    Deriv (eqF (ap2 stepFun (ap2 Pair x j) prev) (cmp (ap1 necCode j) prev))
  stepFun_eq x j prev =
    let pkg : Term
        pkg = ap2 Pair x j
        BB : Fun2
        BB = Fan (Lift1 (compose1U necCode Snd)) v Pair

        e1 : Deriv (eqF (ap2 stepFun pkg prev)
                        (ap2 Pair (ap2 (Lift1 (constN tag_mp)) pkg prev)
                                  (ap2 BB pkg prev)))
        e1 = axFan (Lift1 (constN tag_mp)) BB Pair pkg prev

        eHead : Deriv (eqF (ap2 (Lift1 (constN tag_mp)) pkg prev) (natCode tag_mp))
        eHead = ruleTrans (axLift (constN tag_mp) pkg prev) (constN_eq tag_mp pkg)

        eBody : Deriv (eqF (ap2 BB pkg prev)
                           (ap2 Pair (ap1 necCode j) prev))
        eBody =
          let f1 : Deriv (eqF (ap2 BB pkg prev)
                              (ap2 Pair (ap2 (Lift1 (compose1U necCode Snd)) pkg prev)
                                        (ap2 v pkg prev)))
              f1 = axFan (Lift1 (compose1U necCode Snd)) v Pair pkg prev
              fLeft : Deriv (eqF (ap2 (Lift1 (compose1U necCode Snd)) pkg prev)
                                 (ap1 necCode j))
              fLeft = ruleTrans (axLift (compose1U necCode Snd) pkg prev)
                        (ruleTrans (axComp necCode Snd pkg)
                                   (cong1 necCode (axSnd x j)))
              fRight : Deriv (eqF (ap2 v pkg prev) prev)
              fRight = ax_v pkg prev
          in ruleTrans f1
               (ruleTrans (congL Pair (ap2 v pkg prev) fLeft)
                          (congR Pair (ap1 necCode j) fRight))
    in ruleTrans e1
         (ruleTrans (congL Pair (ap2 BB pkg prev) eHead)
                    (congR Pair (natCode tag_mp) eBody))

  -- q t = qRec O t  (the C-unfold, o t = O, u t = t).
  q_unfold : (t : Term) -> Deriv (eqF (ap1 q t) (ap2 qRec O t))
  q_unfold t =
    ruleTrans (ax_C qRec o u t)
      (ruleTrans (congL qRec (ap1 u t) (ax_o t))
                 (congR qRec O (ax_u t)))

  q_at_O : Deriv (eqF (ap1 q O) O)
  q_at_O =
    ruleTrans (q_unfold O)
      (ruleTrans (ax_R_base o stepFun Pair O) (ax_o O))

  q_at_succ :
    (j : Term) ->
    Deriv (eqF (ap1 q (ap1 s j)) (cmp (ap1 necCode j) (ap1 q j)))
  q_at_succ j =
    let e1 : Deriv (eqF (ap1 q (ap1 s j)) (ap2 qRec O (ap1 s j)))
        e1 = q_unfold (ap1 s j)
        e2 : Deriv (eqF (ap2 qRec O (ap1 s j))
                        (ap2 stepFun (ap2 Pair O j) (ap2 qRec O j)))
        e2 = ax_R_step o stepFun Pair O j
        e3 : Deriv (eqF (ap2 stepFun (ap2 Pair O j) (ap2 qRec O j))
                        (cmp (ap1 necCode j) (ap2 qRec O j)))
        e3 = stepFun_eq O j (ap2 qRec O j)
        e4 : Deriv (eqF (cmp (ap1 necCode j) (ap2 qRec O j))
                        (cmp (ap1 necCode j) (ap1 q j)))
        e4 = congR Pair (natCode tag_mp)
               (congR Pair (ap1 necCode j) (ruleSym (q_unfold j)))
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))

  ------------------------------------------------------------------------
  -- SECTION 2.  The Skolemized QF motive + the ONE ruleIndNat.

  INV : Term -> Formula
  INV j = eqF (ap1 thmT (ap1 q j)) (ap1 cMGE j)

  -- baseReal:  substF zero O (INV (var 0)) = INV O .
  baseReal : Deriv (INV O)
  baseReal = ruleTrans (cong1 thmT q_at_O) dBaseNec

  -- stepReal (uniform in j):  INV j -> INV (s j) , by REAL imp_encoded_mp (D3).
  stepReal : (j : Term) -> Deriv (imp (INV j) (INV (ap1 s j)))
  stepReal j =
    let ime : Deriv (imp (INV j)
                (eqF (ap1 thmT (cmp (ap1 necCode j) (ap1 q j)))
                     (ap1 cMGE (ap1 s j))))
        ime = imp_encoded_mp (INV j) (ap1 necCode j) (ap1 q j)
                (ap1 cMGE j) (ap1 cMGE (ap1 s j))
                (liftP (INV j) (dStepNec j))
                (identImp (INV j))
        rew : Deriv (imp (eqF (ap1 thmT (cmp (ap1 necCode j) (ap1 q j)))
                              (ap1 cMGE (ap1 s j)))
                         (INV (ap1 s j)))
        rew = prependEqLeft (ap1 thmT (ap1 q (ap1 s j)))
                            (ap1 thmT (cmp (ap1 necCode j) (ap1 q j)))
                            (ap1 cMGE (ap1 s j))
                            (cong1 thmT (q_at_succ j))
    in compI ime rew

  ind : Deriv (INV (var zero))
  ind = ruleIndNat zero {P = INV (var zero)} baseReal (stepReal (var zero))

  -- instantiate the single induction at the Bin-compressed boundary  N+1
  -- (cost O(|N|)); no closeCoe -- N is not in the motive.
  indAtN1 : Deriv (INV (ap1 s N))
  indAtN1 = ruleInst zero (ap1 s N) ind

  ------------------------------------------------------------------------
  -- SECTION 3.  The Con-finish (D3 + ConSchema + axExFalso; con_inj shape).
  --   thmT proves (m>=N+1) [induction] and thmT proves (m>=N+1 -> 0=1) [dRef,
  --   the false-count refutation], so thmT proves 0=1; Con refutes it.

  godelII_toy : Deriv falseF
  godelII_toy =
    let finalProof : Term
        finalProof = cmp cRef (ap1 q (ap1 s N))
        provesFalse : Deriv (eqF (ap1 thmT finalProof) codeFalse)
        provesFalse = encoded_mp cRef (ap1 q (ap1 s N))
                        (ap1 cMGE (ap1 s N)) codeFalse dRef indAtN1
        con_inst : Deriv (neg (eqF (ap1 thmT finalProof) codeFalse))
        con_inst = ruleInst zero finalProof con
    in mp (mp (axExFalso (eqF (ap1 thmT finalProof) codeFalse) falseF) provesFalse)
          con_inst
