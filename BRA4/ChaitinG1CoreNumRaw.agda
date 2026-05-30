{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ChaitinG1CoreNumRaw -- Chaitin-Goedel-I, num-raw form, CGI_core_num_raw.
--
-- Wires the shipped pieces:
--   * BRA4.ChaitinG1DischargeKdef.DischargeKdef  -- supplies  dNeg_at_kmax
--   * BRA4.ChaitinG1ChainKdef.ChainKdef          -- supplies  dEval_witness
--   * a PARAMETER  dLenStarDef                   -- the size atom for gLcodeDef Lstar
--   * BRA4.CgiClash.cgiClash                     -- the integrated single-conjunct clash
-- to produce the documented num-raw Chaitin-Goedel-I conclusion.
--
-- ============================================================
-- Answer to the "informal-argument" question (from
-- BRA4/NEXT-SESSION-CGI-NUM-RAW.md).
-- ============================================================
--
-- The informal argument is:
--   "you assume thmT(w) to be of the form code(K(x_) > L*) -- here we use num x.
--    We take then the FIRST w1 such that thmT(w1) is of this form code(K(x'_) > L*).
--    We have a small program: enumerate thmT(0), thmT(1), ... until we get the
--    form code(K(_) > L*).  This small program describes x' and we get an
--    internal contradiction."
--
-- At which step is isNat (num_eq_code) silently introduced?  ANSWER: NONE of
-- them.  Tracing each step against the shipped formal machinery:
--
--   (1) "thmT(w) of the form code(K(x_) > L*) -- we use num x"
--       Hypothesis  Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)) .  Kcode Lstar
--       is a Fun1; x is a Term in the value slot; Fun1-evaluation gives
--       kdefSkel Lstar (ap1 num x).  No isNat -- `num` is the syntactic slot-
--       marker, not a numeral assertion.
--
--   (2) "We take the FIRST w1 ..."
--       FirstHit.Search over  hitKdef Lstar (outKdef Lstar) .  Subject readback
--       outKdef = decode . projKdef . thmT ; on a match, the slot is  num x'
--       and  decode (num t) = t  holds for ANY Term t (BRA4.Decode.decode_num_id),
--       not just numerals.  No isNat.
--
--   (3) "This small program describes x'."
--       dEval_witness : Deriv (eqF (ap2 evalU (ap1 parse (enc (gLcodeDef Lstar)))
--       nTerm) (ap1 s x')) -- a direct fact about gLcodeDef.  x' is just a Term
--       (whatever  outKdef Lstar k_max  reduces to).  No isNat.
--
--   (4) "And we get an internal contradiction."
--       The doc's Step 6 warning was that aligning codeTerm(parse(enc(gL))) and
--       num(parse(enc(gL))) might force num_eq_code at the program/fuel slot.
--       *** This is NOT realized. ***  BRA4.CgiClash.cgiClash performs the
--       alignment via  thmT_at_sb + passK : sbt_at_var_match rewrites the inner
--       var-leaves Pair(tag_var, natCode 0) / Pair(tag_var, natCode 1) DIRECTLY
--       to  ap1 num gL / ap1 num n0 .  The substituted code  KClosed  carries
--       cAp2f runProg (num gL) (num n0)  by  refl ; thm13_binary's output at
--       evalU matches by refl-after-num_at_S-on-the-output-slot.  No isNat
--       crosses the alignment.
--
-- So the informal argument is FORMALIZABLE WITHOUT  isNat / num_eq_code  at any
-- of the four steps.  The doc's worry about the program/fuel slot is dissolved
-- by  passK  (the substitution route).
--
-- ============================================================
-- What is shipped here.
-- ============================================================
--
-- Given:
--   * the K-form hypothesis  thmT w = ap1 (Kcode Lstar) x  on (w, x);
--   * closure facts on w (Closed w, sim_w) -- the genuine formal residual,
--     used by DischargeKdef to build  cl_kmax  + the StepU2MuCorrect
--     Construct (which needs k_max sub-stability);
--   * the size fact  dLenStarDef  for  gLcodeDef Lstar  (the only remaining
--     residual; the parallel  Size  module for the Kdef-shape program is a
--     separate, ~250-350 LoC piece of plug-context machinery -- see header
--     of BRA4/dLenStarDef.agda when shipped),
-- we build  CGI_core_num_raw :  Sigma Term (\ z -> Deriv (thmT z = codeFalse)) .
--
-- The doc proposed building  encoded_andI / encoded_negI / encoded_implI /
-- encoded_implE  combinators (~200 LoC).  That is OVERSPECIFIED: cgiClash
-- already encapsulates that work via  thmT_at_sb + passK + encoded_mp +
-- chaitin_G1_assembly  (one node application, no compound encoded combinators
-- needed).  The encoded_andI/negI/implI route is what we'd need if we tried
-- to thread thmT_complete_rec; that's what the previous handoff hit a wall
-- on, and exactly what the user pointed out as the wrong design.

module BRA4.ChaitinG1CoreNumRaw where

open import BRA4.Base
open import BRA4.Code            using ( codeFalse ; codeFun1 )
open import BRA4.Tags            using ( tag_eq ; tag_ap1 ; tag_s )
open import BRA4.ThmT            using ( thmT )
open import BRA4.Num             using ( num ; num_at_O ; num_at_S )
open import BRA4.DefWit          using ( cEqTm )
open import BRA4.Kdef            using ( Kcode )
open import BRA4.KdefDiag        using ( gLcodeDef )
open import BRA4.KFormula        using ( szLeqFun ; szLeqApp )
open import BRA4.KGodel1BridgeDef using ( Lstar )
open import BRA4.CgiClash        using ( SomeProof ; mkProof ; cgiClash
                                       ; szAtomT ; cAp1f )
open import BRA4.ProgEnc         using ( enc )
open import BRA4.Thm12.Thm13     using ( codeFXeqY1 ; thm13_singulary )
open import BRA4.Thm12.All       using ( thm12 ; fst )
open import BRA4.dLenStarDef     using ( dLenStarDef )

import BRA4.ChaitinG1DischargeKdef
import BRA4.ChaitinG1ChainKdef

open import BRA3.RuleInst2       using ( simSubstT )
open import BRA4.CloseW          using ( closeW ; cl_w_sub0 ; cl_w_sub1 ; cl_w_sim )

------------------------------------------------------------------------
-- Local Sigma  (BRA3/BRA4 do not export a global Sigma; see Thm12.All for
-- the same pattern).

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor mkSigma
  field
    fst : A
    snd : B fst
open Sigma public

------------------------------------------------------------------------
-- The canonical short program NAME (the encoding of the diagonal loop
-- gLcodeDef Lstar  whose size  dLenStarDef  asserts fits  L0 = Lstar ).

gLnameDef : Term
gLnameDef = enc (gLcodeDef Lstar)

------------------------------------------------------------------------
-- The closed size-formula code that cgiClash expects from  dSize .

szLeqClosedDef : Term
szLeqClosedDef = cEqTm (cAp1f (szLeqFun Lstar) (ap1 num gLnameDef)) (cAp1f s O)

------------------------------------------------------------------------
-- Sigma1-completeness internalisation of the size fact.   Parallel to
-- BRA4.CgiTheorem.dSize but at  gLnameDef := enc (gLcodeDef Lstar) .
--  dLenStarDef  (BRA4.dLenStarDef) discharges the residual size fact at
-- the Kdef-shape  Lstar  via the parallel  Size  module BRA4.GLCodePDef.

cSizeProofDef : Term
cSizeProofDef = ap1 (fst (thm12 (szLeqFun Lstar))) gLnameDef

dSizeDef : Deriv (eqF (ap1 thmT cSizeProofDef) szLeqClosedDef)
dSizeDef =
  let -- RHS bridge:  num (s 0) -> code(s)(num 0) -> code(s) 0 .
      bRHS : Deriv (eqF (ap1 num (ap1 s O)) (cAp1f s O))
      bRHS = ruleTrans (num_at_S O)
               (congR Pair (natCode tag_ap1) (congR Pair (natCode tag_s) num_at_O))

      bridge : Deriv (eqF (codeFXeqY1 (szLeqFun Lstar) gLnameDef (ap1 s O))
                          szLeqClosedDef)
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp1f (szLeqFun Lstar) (ap1 num gLnameDef)) bRHS)
  in ruleTrans (thm13_singulary (szLeqFun Lstar) gLnameDef (ap1 s O) dLenStarDef)
               bridge

------------------------------------------------------------------------
-- THE THEOREM  CGI_core_num_raw  (EXACT FIXED-TARGET signature).
--
-- No closure hypothesis on w, no isNat, no Con, no codeFormula.
--
-- Strategy:  apply  ruleInst 1 O  then  ruleInst 0 O  to the user's
-- hyp, getting a Deriv about  closeW w := substT 0 O (substT 1 O w)
-- (closed at vars 0 and 1 by construction).   The three closure facts
-- DischargeKdef wants on  w  are then trivial structurally (BRA4.CloseW
-- supplies them as  cl_w_sub0 / cl_w_sub1 / cl_w_sim ).

CGI_core_num_raw :
  (w x : Term) ->
  Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)) ->
  Sigma Term (\ z -> Deriv (eqF (ap1 thmT z) codeFalse))
CGI_core_num_raw w x hyp =
  let -- Step 1.  ruleInst (suc zero) O on hyp:  substitute var 1 -> O .
      hyp1 :
        Deriv (eqF (ap1 thmT (substT (suc zero) O w))
                    (ap1 (Kcode Lstar) (substT (suc zero) O x)))
      hyp1 = ruleInst (suc zero) O hyp

      -- Step 2.  ruleInst zero O on hyp1:  substitute var 0 -> O .
      hyp2 :
        Deriv (eqF (ap1 thmT (closeW w)) (ap1 (Kcode Lstar) (closeW x)))
      hyp2 = ruleInst zero O hyp1

      -- The three substitution-stability facts on  closeW w  are
      -- structural (BRA4.CloseW), independent of  w 's free vars.

      -- Step 3.  Wire through the closed-input version with all closure
      -- facts derived from CloseW.

      open BRA4.ChaitinG1DischargeKdef.DischargeKdef
             (closeW w) (closeW x) hyp2
             (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( k_max ; x' ; dNeg_at_kmax )

      open BRA4.ChaitinG1ChainKdef.ChainKdef
             (closeW w) (closeW x) hyp2
             (cl_w_sub0 w) (cl_w_sub1 w) (cl_w_sim w)
        using ( nTerm ; dEval_witness )

      proof : SomeProof
      proof = cgiClash Lstar gLnameDef nTerm x' k_max cSizeProofDef
                dNeg_at_kmax dSizeDef dEval_witness
  in mkSigma (SomeProof.pf proof) (SomeProof.isPf proof)
