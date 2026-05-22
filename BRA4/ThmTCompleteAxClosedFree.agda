{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ThmTCompleteAxClosedFree -- per-axiom completeness lemmas for
-- the axiom cases that DO NOT require any  Closed  witness on Term
-- arguments AND whose closure output is a fully-reduced codeFormula
-- of the schema :
--
--   ax_o t  : single Term arg, sb only at var 0.
--   ax_u t  : single Term arg, sb only at var 0.
--
-- These don't need Closed because they have only ONE sb wrap (at var 0)
-- and the schema's var-0 positions become the term arg directly via
-- substT 0 t (var 0) = t  (definitional).  No further sb wraps to
-- destabilise the substituted term.
--
-- ax_C / ax_R_base / ax_R_step closures expose Fst/Snd projections of
-- their  extra : Term  argument inside outputRHS , so the schema
-- output is NOT definitionally a codeFormula(SCHEMA) ; they need an
-- axFst/axSnd reduction chain.  Handled in BRA4.ThmTCompleteAxFunctor .

module BRA4.ThmTCompleteAxClosedFree where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Encode
open import BRA4.ThmT      using ( thmT )
open import BRA4.SbF       using ( sbf )
open import BRA4.SbT       using ( sbt )
open import BRA4.SbfAtClosures using ( sbContract )
open import BRA4.SbDerived using ( module Derive )

open import BRA4.ThmTAtSb  using ( thmT_at_sb )
open import BRA4.ThmTAtAx1 using ( thmT_at_axN1 )
open import BRA4.ThmTAtAx2 using ( thmT_at_axN2 )

open import BRA3.Church          using ( pi )

open Derive sbt sbf sbContract

------------------------------------------------------------------------
-- Generic helper : chain  thmT_at_axN  +  thmT_at_sb  +  sbfEq_codeFormula 0 t SCHEMA .
--
-- For a single Term parameter at var 0, this delivers
--   thmT (encode_sb 0 (codeTerm t) packAx<i>) = codeFormula (substF 0 t SCHEMA) .
--
-- substF 0 t SCHEMA  then reduces (definitionally) to the conclusion of
-- the axiom rule, so the same type is reported either way.

private
  -- Wrap-and-push: given  schema_eq : thmT (packAx<i> O) = codeFormula SCHEMA ,
  -- produce  thmT (encode_sb 0 (codeTerm t) (packAx<i> O))
  --             = codeFormula (substF 0 t SCHEMA) .
  wrap_sb0 :
    (t : Term) (SCHEMA : Formula) (packAxBody : Term)
    (schema_eq : Deriv (eqF (ap1 thmT packAxBody) (codeFormula SCHEMA))) ->
    Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb)
                                  (ap2 pi (ap2 pi (natCode zero) (codeTerm t)) packAxBody)))
                (codeFormula (substF zero t SCHEMA)))
  wrap_sb0 t SCHEMA packAxBody schema_eq =
    let spec : Term
        spec = ap2 Pair (natCode zero) (codeTerm t)

        step_sb :
          Deriv (eqF (ap1 thmT (ap2 pi (natCode tag_sb)
                                       (ap2 pi spec packAxBody)))
                      (ap2 sbf spec (ap1 thmT packAxBody)))
        step_sb = thmT_at_sb spec packAxBody

        step_lift :
          Deriv (eqF (ap2 sbf spec (ap1 thmT packAxBody))
                      (ap2 sbf spec (codeFormula SCHEMA)))
        step_lift = congR sbf spec schema_eq

        step_codeF :
          Deriv (eqF (ap2 sbf spec (codeFormula SCHEMA))
                      (codeFormula (substF zero t SCHEMA)))
        step_codeF = sbfEq_codeFormula zero t SCHEMA
    in ruleTrans step_sb (ruleTrans step_lift step_codeF)

------------------------------------------------------------------------
-- ax_o t  :  P = atomic (eqn (ap1 o t) O) .  Schema  o(var 0) = O .

thmT_complete_ax_o :
  (t : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_o t))) (codeFormula (atomic (eqn (ap1 o t) O))))
thmT_complete_ax_o t =
  wrap_sb0 t (atomic (eqn (ap1 o (var zero)) O))
           (ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc zero)) O))
           (thmT_at_axN1 O)

------------------------------------------------------------------------
-- ax_u t  :  P = atomic (eqn (ap1 u t) t) .  Schema  u(var 0) = var 0 .

thmT_complete_ax_u :
  (t : Term) ->
  Deriv (eqF (ap1 thmT (encode (ax_u t))) (codeFormula (atomic (eqn (ap1 u t) t))))
thmT_complete_ax_u t =
  wrap_sb0 t (atomic (eqn (ap1 u (var zero)) (var zero)))
           (ap2 pi (natCode tag_ax) (ap2 pi (natCode (suc (suc zero))) O))
           (thmT_at_axN2 O)

