{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KrestProvCK -- clos Step 4, FAITHFUL :  ONE application of  thm13  to the
-- antecedent characteristic  Kr , collapsing the whole fixed-tail conjunction
-- to the single decidable atom  Kr x0 = O .
--
--   dKrestCK :
--     Deriv (imp charAtom
--                (eqF (ap1 thmT (ap1 (fst (thm12 Kr)) (var 0)))
--                     (ap2 sbf spec0 (codeFormula charAtom))))
--
-- where  charAtom = (Kr x0 = O)  and  ap2 sbf spec0 (codeFormula charAtom)
-- = code(Kr (num x0) = O)  ( the num-installed CK-atom code, EXACTLY the
-- antecedent  T4.EncodeStepCK.step2CK  produces ).
--
-- Built by  imp_thm13_singulary  ( = thm13 under the trivial hypothesis
-- impRefl charAtom , since  charAtom  IS  Kr x0 = O ), whose output code
-- codeFXeqY1 Kr (var 0) O  is bridged to  sbf spec0 (codeFormula charAtom)
-- by computing the substitution structurally ( sbf_step_atomic / sbt_step_ap1
-- / sbt_at_var_match / sbt_inert_NumCode ) plus the single  num O = O  rewrite
-- ( num_at_O ).   The conjunction NEVER enters the Sigma_1 lift -- thm13 fires
-- exactly ONCE, on  Kr .

open import T4.Base

module T4.KrestProvCK (Kr : Fun1) where

open import T4.Tags  using ( tag_ap1 ; tag_var ; tag_eq )
open import T4.Num   using ( num ; num_at_O )
open import T4.Code  using ( codeFun1 ; codeTerm ; codeFormula )
open import T4.ThmT  using ( thmT )
open import T4.SbF   using ( sbf )
open import T4.SbT   using ( sbt )
open import T4.SbStep using ( sbf_step_atomic ; sbt_step_ap1 ; sbt_inert_NumCode
                            ; NumCode ; ncO )
open import T4.SbtAtVar using ( sbt_at_var_match )

open import T4.Thm12.Thm13 using ( codeFXeqY1 )
open import T4.Thm12.All   using ( thm12 ; fst )
open import T4.Thm12.ImpThm13 using ( imp_thm13_singulary )
open import T4.Thm12.ImpHelpers using ( impRefl ; impLift )
open import T4.ImpExtras using ( imp_eqTrans_imp )

------------------------------------------------------------------------
-- The CK atom and the num-installation spec  ( = T4.EncodeStepCK's ).

charAtom : Formula
charAtom = eqF (ap1 Kr (var zero)) O

S0 : Term
S0 = ap1 num (var zero)
spec0 : Term
spec0 = ap2 Pair (natCode zero) S0

-- the proof index  w2 = D Kr x0 .
w2 : Term
w2 = ap1 (fst (thm12 Kr)) (var zero)

------------------------------------------------------------------------
-- SECTION 1.  Compute  sbf spec0 (codeFormula charAtom)  structurally.
-- (= the substitution  x0 |-> num x0  applied to the CK-atom code.)

lhs : Term            -- codeTerm (ap1 Kr (var 0))
lhs = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 Kr) (codeTerm (var zero)))

lhs' : Term           -- num-installed :  cAp1f Kr (num x0)
lhs' = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 Kr) S0)

eVar : Deriv (eqF (ap2 sbt spec0 (codeTerm (var zero))) S0)
eVar = sbt_at_var_match zero S0

eLHS : Deriv (eqF (ap2 sbt spec0 lhs) lhs')
eLHS = sbt_step_ap1 zero S0 Kr (codeTerm (var zero)) S0 eVar

eRHS : Deriv (eqF (ap2 sbt spec0 O) O)
eRHS = sbt_inert_NumCode O ncO zero S0

-- sbf  over the atomic node :  sbf spec0 (code(Kr x0 = O)) = cEqTm lhs' O .
computeSbf :
  Deriv (eqF (ap2 sbf spec0 (codeFormula charAtom))
             (ap2 Pair (natCode tag_eq) (ap2 Pair lhs' O)))
computeSbf = sbf_step_atomic zero S0 lhs O lhs' O eLHS eRHS

------------------------------------------------------------------------
-- SECTION 2.  Bridge  codeFXeqY1 Kr (var 0) O  ->  sbf spec0 (code charAtom) .
-- They differ ONLY in the RHS slot :  num O  ( thm13 )  vs  O  ( sbf ) ;
-- num_at_O  rewrites  num O = O .

eFx :
  Deriv (eqF (codeFXeqY1 Kr (var zero) O)
             (ap2 Pair (natCode tag_eq) (ap2 Pair lhs' O)))
eFx = congR Pair (natCode tag_eq) (congR Pair lhs' num_at_O)

bridgeEq :
  Deriv (eqF (codeFXeqY1 Kr (var zero) O)
             (ap2 sbf spec0 (codeFormula charAtom)))
bridgeEq = ruleTrans eFx (ruleSym computeSbf)

------------------------------------------------------------------------
-- SECTION 3.  clos Step 4 :  thm13 on  Kr , under  charAtom  ( = impRefl ).

dKrestCK :
  Deriv (imp charAtom
             (eqF (ap1 thmT w2) (ap2 sbf spec0 (codeFormula charAtom))))
dKrestCK =
  imp_eqTrans_imp
    (imp_thm13_singulary Kr (var zero) O charAtom (impRefl charAtom))
    (impLift {charAtom} bridgeEq)
