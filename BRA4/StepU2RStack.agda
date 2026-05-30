{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.StepU2RStack -- the continuation transformer Stack for the
-- R-case completeness proof (Layer-1 CK-machine).
--
-- Architecture: BRA4/STEPU2-STACK-HANDOFF.md.
--
-- The K-wall in the R-case is resolved by making the motive's K a
-- DERIVED Term function of the induction variable, via a Stack : Fun2
-- whose recurrence aligns with the operational descent of R.  At
-- ruleIndNat 2 on y, the IH's K and the use-site's K coincide
-- VERBATIM by the Stack recurrence -- no kappend, no K-substitution.
--
-- Params encoding: params = pi y_top (pi K_outer x)
--   top  params = Fst params           (= y_top, the outer recursion depth)
--   K0   params = Fst (Snd params)     (= K_outer, the outer kont)
--   x0   params = Snd (Snd params)     (= x, the outer R first arg)
--
-- Stack recursion on descent depth d:
--   Stack params O      = K_outer
--   Stack params (s d') = kons (frmApp2 h1c (h2 x (sub y_top (s d'))))
--                              (Stack params d')
--
-- where h1c = mcode2 h1 (closed by NoVar_mcode2).
--
-- This file ships Stack + its closed-form R-base/R-step laws + the
-- NoVar witness for mcode2.  The high-level Stack-unfold-at-current
-- lemma (which bridges via sub arithmetic under `leq (s y) y_top`)
-- is in BRA4.StepU2CorrectR.

module BRA4.StepU2RStack where

open import BRA4.Base
open import BRA4.Tags
  using ( tag_s ; tag_o ; tag_u ; tag_C ; tag_v ; tag_R )
open import BRA4.EvalU
  using ( mcode1 ; mcode2 ; frmApp2 ; kons ; tagApp2 )
open import BRA4.EvalU public
  using ( mcode1 ; mcode2 )

open import BRA3.Church   using ( pi ; sub )
open import BRA3.Fan      using ( Lift1 ; Lift2 ; Fan ; Lift1_eq ; Lift2_eq ; Fan_eq )
open import BRA3.PairAlgebra using ( axFst ; axSnd )

open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; NoVarAnd ; mkAnd ; NoVar_natCode
        ; constTermFun1 ; constTermFun1_eq )

------------------------------------------------------------------------
-- Section 1.  NoVar witnesses for the closed codes  mcode1 / mcode2 .

NoVar_mcode1 : (f : Fun1) -> NoVar (mcode1 f)
NoVar_mcode2 : (g : Fun2) -> NoVar (mcode2 g)

NoVar_mcode1 s = mkAnd (NoVar_natCode tag_s) tt
NoVar_mcode1 o = mkAnd (NoVar_natCode tag_o) tt
NoVar_mcode1 u = mkAnd (NoVar_natCode tag_u) tt
NoVar_mcode1 (C g h1 h2) =
  mkAnd (NoVar_natCode tag_C)
    (mkAnd (NoVar_mcode2 g)
       (mkAnd (NoVar_mcode1 h1) (NoVar_mcode1 h2)))

NoVar_mcode2 v = mkAnd (NoVar_natCode tag_v) tt
NoVar_mcode2 (R g h1 h2) =
  mkAnd (NoVar_natCode tag_R)
    (mkAnd (NoVar_mcode1 g)
       (mkAnd (NoVar_mcode2 h1) (NoVar_mcode2 h2)))

------------------------------------------------------------------------
-- Section 2.  Stack as a Fun2, parametric in (h1, h2) at the meta level.
--
-- The h1c constant is woven into Stack's h2' body via constTermFun1.
-- The h2 evaluation appears as the inner Fun2 of a 3-deep Fan/Lift
-- composition.

module StackOf (h1 h2 : Fun2) where

  -- The frame's h1c is the closed mcode2 of the meta h1 Fun2.
  h1c : Term
  h1c = mcode2 h1

  NoVar_h1c : NoVar h1c
  NoVar_h1c = NoVar_mcode2 h1

  ------------------------------------------------------------------
  -- Param projections at the META level (taking a Term params and
  -- returning a Term via Fst / Snd compositions).  These are NOT BRA
  -- functions -- they describe the Term arithmetic that the BRA
  -- expressions below should compute to.

  -- top : Fun1 = compose1U Fst Snd... no -- top params = Fst params, so
  -- the Fun1 extracting top is just Fst.

  -- K0 : Fun1 = compose1U Fst Snd  (extracts Fst (Snd params)).

  -- x0 : Fun1 = compose1U Snd Snd  (extracts Snd (Snd params)).

  ------------------------------------------------------------------
  -- The three components of Stack as a BRA R-recursion.

  -- Component g : Fun1.  Extracts K_outer from params for the R-base case.
  StackG : Fun1
  StackG = compose1U Fst Snd

  -- Component h1' : Fun2.  Builds  kons frame prev .
  -- kons = pi (s O) (pi frame prev) = pi (natCode 1) (pi frame prev).
  -- h1' = Fan (Lift2 (constN 1)) pi pi.
  StackH1 : Fun2
  StackH1 = Fan (Lift2 (constN 1)) pi pi

  -- Component h2' : Fun2.  Builds the frame at descent depth d:
  --   h2'(params, d) = frmApp2 h1c (h2 x (sub y_top (s d)))
  --                  = pi (natCode tagApp2)
  --                       (pi h1c (h2 (Snd (Snd params)) (sub (Fst params) (s d))))
  --
  -- Layered build:
  --   subIdx : Fun2.  subIdx(params, d) = sub (Fst params) (s d).
  --   extractX : Fun2.  extractX(params, d) = Snd (Snd params).
  --   h2call : Fun2.  h2call(params, d) = ap2 h2 (extractX) (subIdx) = h2 x (sub top (s d)).
  --   h1cFun2 : Fun2.  h1cFun2(params, d) = h1c.
  --   inner : Fun2.  inner(params, d) = pi h1c (h2 x ...).
  --   tagFun2 : Fun2.  tagFun2(params, d) = natCode tagApp2.
  --   StackH2 : Fun2.  StackH2(params, d) = pi (natCode tagApp2) inner.

  subIdx : Fun2
  subIdx = Fan (Lift1 Fst) (Lift2 s) sub

  extractX : Fun2
  extractX = Lift1 (compose1U Snd Snd)

  h2call : Fun2
  h2call = Fan extractX subIdx h2

  h1cFun2 : Fun2
  h1cFun2 = Lift1 (constTermFun1 h1c)

  inner : Fun2
  inner = Fan h1cFun2 h2call pi

  tagFun2 : Fun2
  tagFun2 = Lift1 (constN tagApp2)

  StackH2 : Fun2
  StackH2 = Fan tagFun2 inner pi

  ------------------------------------------------------------------
  -- The Stack itself.

  Stack : Fun2
  Stack = R StackG StackH1 StackH2

  ------------------------------------------------------------------
  -- Section 3.  Stack closed forms.
  --
  --   Stack params O      = K_outer        [Stack-base]
  --   Stack params (s d') = kons (h2'(params, d')) (Stack params d')   [Stack-step-raw]
  --
  -- Then we unfold h2'(params, d') to its concrete frmApp2 shape
  -- (Stack-step-frame).

  -- Stack-base : ap2 Stack params O = ap1 (compose1U Fst Snd) params .
  -- By ax_R_base.  Then the user simplifies via axComp + axFst + axSnd
  -- to get K_outer for concrete params.
  Stack-base : (params : Term) ->
    Deriv (eqF (ap2 Stack params O) (ap1 StackG params))
  Stack-base params = ax_R_base StackG StackH1 StackH2 params

  Stack-base-at-K0 : (y_top K_outer x : Term) ->
    Deriv (eqF (ap2 Stack (ap2 pi y_top (ap2 pi K_outer x)) O) K_outer)
  Stack-base-at-K0 y_top K_outer x =
    let params : Term
        params = ap2 pi y_top (ap2 pi K_outer x)
        e1 : Deriv (eqF (ap2 Stack params O) (ap1 (compose1U Fst Snd) params))
        e1 = Stack-base params
        e2 : Deriv (eqF (ap1 (compose1U Fst Snd) params) (ap1 Fst (ap1 Snd params)))
        e2 = axComp Fst Snd params
        e3 : Deriv (eqF (ap1 Snd params) (ap2 pi K_outer x))
        e3 = axSnd y_top (ap2 pi K_outer x)
        e4 : Deriv (eqF (ap1 Fst (ap1 Snd params)) (ap1 Fst (ap2 pi K_outer x)))
        e4 = cong1 Fst e3
        e5 : Deriv (eqF (ap1 Fst (ap2 pi K_outer x)) K_outer)
        e5 = axFst K_outer x
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e4 e5))

  -- Stack-step-raw : the bare ax_R_step on Stack.
  Stack-step-raw : (params d : Term) ->
    Deriv (eqF (ap2 Stack params (ap1 s d))
               (ap2 StackH1 (ap2 StackH2 params d) (ap2 Stack params d)))
  Stack-step-raw params d = ax_R_step StackG StackH1 StackH2 params d

  ------------------------------------------------------------------
  -- StackH1 unfolding: ap2 StackH1 frame prev = kons frame prev .

  StackH1-eq : (frame prev : Term) ->
    Deriv (eqF (ap2 StackH1 frame prev) (kons frame prev))
  StackH1-eq frame prev =
    let -- ap2 (Fan f g pi) a b = ap2 pi (ap2 f a b) (ap2 g a b)
        e1 : Deriv (eqF (ap2 StackH1 frame prev)
                        (ap2 pi (ap2 (Lift2 (constN 1)) frame prev)
                                (ap2 pi frame prev)))
        e1 = Fan_eq (Lift2 (constN 1)) pi pi frame prev
        -- ap2 (Lift2 f) a b = ap1 f b
        e2a : Deriv (eqF (ap2 (Lift2 (constN 1)) frame prev) (ap1 (constN 1) prev))
        e2a = Lift2_eq (constN 1) frame prev
        -- ap1 (constN 1) prev = natCode 1 = ap1 s O
        e2b : Deriv (eqF (ap1 (constN 1) prev) (ap1 s O))
        e2b = constN_eq 1 prev
        e2 : Deriv (eqF (ap2 (Lift2 (constN 1)) frame prev) (ap1 s O))
        e2 = ruleTrans e2a e2b
        -- Rewrite the LHS of the outer pi using e2.
        e3 : Deriv (eqF (ap2 pi (ap2 (Lift2 (constN 1)) frame prev) (ap2 pi frame prev))
                        (ap2 pi (ap1 s O) (ap2 pi frame prev)))
        e3 = congL pi (ap2 pi frame prev) e2
    in ruleTrans e1 e3

  ------------------------------------------------------------------
  -- StackH2 unfolding: ap2 StackH2 params d = frmApp2 h1c (h2 x_param idx)
  --   where x_param = Snd (Snd params), idx = sub (Fst params) (s d).
  --
  -- Five subequalities (one per Fan/Lift component), then chain.

  -- tagFun2 evaluates to natCode tagApp2 at any (params, d).
  StackH2-tag : (params d : Term) ->
    Deriv (eqF (ap2 tagFun2 params d) (natCode tagApp2))
  StackH2-tag params d =
    let e1 : Deriv (eqF (ap2 (Lift1 (constN tagApp2)) params d)
                         (ap1 (constN tagApp2) params))
        e1 = Lift1_eq (constN tagApp2) params d
        e2 : Deriv (eqF (ap1 (constN tagApp2) params) (natCode tagApp2))
        e2 = constN_eq tagApp2 params
    in ruleTrans e1 e2

  -- h1cFun2 evaluates to h1c at any (params, d).
  StackH2-h1c : (params d : Term) ->
    Deriv (eqF (ap2 h1cFun2 params d) h1c)
  StackH2-h1c params d =
    let e1 : Deriv (eqF (ap2 (Lift1 (constTermFun1 h1c)) params d)
                         (ap1 (constTermFun1 h1c) params))
        e1 = Lift1_eq (constTermFun1 h1c) params d
        e2 : Deriv (eqF (ap1 (constTermFun1 h1c) params) h1c)
        e2 = constTermFun1_eq h1c NoVar_h1c params
    in ruleTrans e1 e2

  -- extractX evaluates to Snd (Snd params).
  StackH2-x : (params d : Term) ->
    Deriv (eqF (ap2 extractX params d) (ap1 Snd (ap1 Snd params)))
  StackH2-x params d =
    let e1 : Deriv (eqF (ap2 (Lift1 (compose1U Snd Snd)) params d)
                         (ap1 (compose1U Snd Snd) params))
        e1 = Lift1_eq (compose1U Snd Snd) params d
        e2 : Deriv (eqF (ap1 (compose1U Snd Snd) params)
                         (ap1 Snd (ap1 Snd params)))
        e2 = axComp Snd Snd params
    in ruleTrans e1 e2

  -- subIdx evaluates to sub (Fst params) (s d).
  StackH2-subIdx : (params d : Term) ->
    Deriv (eqF (ap2 subIdx params d) (ap2 sub (ap1 Fst params) (ap1 s d)))
  StackH2-subIdx params d =
    let e1 : Deriv (eqF (ap2 (Fan (Lift1 Fst) (Lift2 s) sub) params d)
                         (ap2 sub (ap2 (Lift1 Fst) params d)
                                  (ap2 (Lift2 s) params d)))
        e1 = Fan_eq (Lift1 Fst) (Lift2 s) sub params d
        e2a : Deriv (eqF (ap2 (Lift1 Fst) params d) (ap1 Fst params))
        e2a = Lift1_eq Fst params d
        e2b : Deriv (eqF (ap2 (Lift2 s) params d) (ap1 s d))
        e2b = Lift2_eq s params d
        e3 : Deriv (eqF (ap2 sub (ap2 (Lift1 Fst) params d) (ap2 (Lift2 s) params d))
                         (ap2 sub (ap1 Fst params) (ap1 s d)))
        e3 = ruleTrans (congL sub (ap2 (Lift2 s) params d) e2a)
                       (congR sub (ap1 Fst params) e2b)
    in ruleTrans e1 e3

  -- h2call evaluates to ap2 h2 (Snd (Snd params)) (sub (Fst params) (s d)).
  StackH2-h2call : (params d : Term) ->
    Deriv (eqF (ap2 h2call params d)
                (ap2 h2 (ap1 Snd (ap1 Snd params))
                         (ap2 sub (ap1 Fst params) (ap1 s d))))
  StackH2-h2call params d =
    let e1 : Deriv (eqF (ap2 (Fan extractX subIdx h2) params d)
                         (ap2 h2 (ap2 extractX params d) (ap2 subIdx params d)))
        e1 = Fan_eq extractX subIdx h2 params d
        e2 : Deriv (eqF (ap2 h2 (ap2 extractX params d) (ap2 subIdx params d))
                         (ap2 h2 (ap1 Snd (ap1 Snd params))
                                  (ap2 sub (ap1 Fst params) (ap1 s d))))
        e2 = ruleTrans (congL h2 (ap2 subIdx params d) (StackH2-x params d))
                       (congR h2 (ap1 Snd (ap1 Snd params)) (StackH2-subIdx params d))
    in ruleTrans e1 e2

  -- inner : ap2 inner params d = pi h1c (h2 x_param subIdx_val).
  StackH2-inner : (params d : Term) ->
    Deriv (eqF (ap2 inner params d)
                (ap2 pi h1c
                  (ap2 h2 (ap1 Snd (ap1 Snd params))
                           (ap2 sub (ap1 Fst params) (ap1 s d)))))
  StackH2-inner params d =
    let e1 : Deriv (eqF (ap2 (Fan h1cFun2 h2call pi) params d)
                         (ap2 pi (ap2 h1cFun2 params d) (ap2 h2call params d)))
        e1 = Fan_eq h1cFun2 h2call pi params d
        e2 : Deriv (eqF (ap2 pi (ap2 h1cFun2 params d) (ap2 h2call params d))
                         (ap2 pi h1c
                           (ap2 h2 (ap1 Snd (ap1 Snd params))
                                    (ap2 sub (ap1 Fst params) (ap1 s d)))))
        e2 = ruleTrans (congL pi (ap2 h2call params d) (StackH2-h1c params d))
                       (congR pi h1c (StackH2-h2call params d))
    in ruleTrans e1 e2

  -- StackH2 : the full frame builder.
  StackH2-eq : (params d : Term) ->
    Deriv (eqF (ap2 StackH2 params d)
                (frmApp2 h1c
                  (ap2 h2 (ap1 Snd (ap1 Snd params))
                           (ap2 sub (ap1 Fst params) (ap1 s d)))))
  StackH2-eq params d =
    let e1 : Deriv (eqF (ap2 (Fan tagFun2 inner pi) params d)
                         (ap2 pi (ap2 tagFun2 params d) (ap2 inner params d)))
        e1 = Fan_eq tagFun2 inner pi params d
        e2 : Deriv (eqF (ap2 pi (ap2 tagFun2 params d) (ap2 inner params d))
                         (ap2 pi (natCode tagApp2) (ap2 inner params d)))
        e2 = congL pi (ap2 inner params d) (StackH2-tag params d)
        e3 : Deriv (eqF (ap2 pi (natCode tagApp2) (ap2 inner params d))
                         (ap2 pi (natCode tagApp2)
                                  (ap2 pi h1c
                                    (ap2 h2 (ap1 Snd (ap1 Snd params))
                                             (ap2 sub (ap1 Fst params) (ap1 s d))))))
        e3 = congR pi (natCode tagApp2) (StackH2-inner params d)
    in ruleTrans e1 (ruleTrans e2 e3)

  ------------------------------------------------------------------
  -- Section 4.  Stack-step : the operational successor law for Stack.
  --
  --   Stack params (s d) = kons
  --                          (frmApp2 h1c
  --                            (h2 (Snd (Snd params))
  --                                (sub (Fst params) (s d))))
  --                          (Stack params d)
  --
  -- This is ax_R_step composed with StackH1-eq and StackH2-eq.

  Stack-step : (params d : Term) ->
    Deriv (eqF (ap2 Stack params (ap1 s d))
                (kons (frmApp2 h1c
                        (ap2 h2 (ap1 Snd (ap1 Snd params))
                                 (ap2 sub (ap1 Fst params) (ap1 s d))))
                       (ap2 Stack params d)))
  Stack-step params d =
    let -- ax_R_step: Stack(params, s d) = ap2 StackH1 (StackH2 params d) (Stack params d)
        e1 : Deriv (eqF (ap2 Stack params (ap1 s d))
                         (ap2 StackH1 (ap2 StackH2 params d) (ap2 Stack params d)))
        e1 = Stack-step-raw params d

        -- StackH1-eq: ap2 StackH1 a b = kons a b
        e2 : Deriv (eqF (ap2 StackH1 (ap2 StackH2 params d) (ap2 Stack params d))
                         (kons (ap2 StackH2 params d) (ap2 Stack params d)))
        e2 = StackH1-eq (ap2 StackH2 params d) (ap2 Stack params d)

        -- StackH2-eq: rewrite the frame
        e3 : Deriv (eqF (kons (ap2 StackH2 params d) (ap2 Stack params d))
                         (kons (frmApp2 h1c
                                (ap2 h2 (ap1 Snd (ap1 Snd params))
                                         (ap2 sub (ap1 Fst params) (ap1 s d))))
                                (ap2 Stack params d)))
        e3 = -- kons f r = pi (s O) (pi f r); rewrite the inner pi's left arg
             let outerL : Term
                 outerL = ap1 s O
                 inner-left : Deriv (eqF (ap2 pi (ap2 StackH2 params d) (ap2 Stack params d))
                                          (ap2 pi (frmApp2 h1c
                                                    (ap2 h2 (ap1 Snd (ap1 Snd params))
                                                             (ap2 sub (ap1 Fst params) (ap1 s d))))
                                                   (ap2 Stack params d)))
                 inner-left = congL pi (ap2 Stack params d) (StackH2-eq params d)
             in congR pi outerL inner-left
    in ruleTrans e1 (ruleTrans e2 e3)

  ------------------------------------------------------------------
  -- Section 5.  Convenience : Stack-step at concrete params.
  --
  -- For caller convenience, expose the same lemma where  params  is
  -- already unpacked into (y_top, K_outer, x).

  Stack-step-at-params : (y_top K_outer x d : Term) ->
    let params = ap2 pi y_top (ap2 pi K_outer x)
    in Deriv (eqF (ap2 Stack params (ap1 s d))
                  (kons (frmApp2 h1c (ap2 h2 x (ap2 sub y_top (ap1 s d))))
                        (ap2 Stack params d)))
  Stack-step-at-params y_top K_outer x d =
    let params : Term
        params = ap2 pi y_top (ap2 pi K_outer x)
        e1 : Deriv (eqF (ap2 Stack params (ap1 s d))
                         (kons (frmApp2 h1c
                                (ap2 h2 (ap1 Snd (ap1 Snd params))
                                         (ap2 sub (ap1 Fst params) (ap1 s d))))
                                (ap2 Stack params d)))
        e1 = Stack-step params d

        -- Fst params = y_top
        eTop : Deriv (eqF (ap1 Fst params) y_top)
        eTop = axFst y_top (ap2 pi K_outer x)

        -- Snd params = pi K_outer x
        eSnd1 : Deriv (eqF (ap1 Snd params) (ap2 pi K_outer x))
        eSnd1 = axSnd y_top (ap2 pi K_outer x)

        -- Snd (Snd params) = x
        eX : Deriv (eqF (ap1 Snd (ap1 Snd params)) x)
        eX = ruleTrans (cong1 Snd eSnd1) (axSnd K_outer x)

        -- Rewrite sub (Fst params) (s d) -> sub y_top (s d)
        eSub : Deriv (eqF (ap2 sub (ap1 Fst params) (ap1 s d))
                           (ap2 sub y_top (ap1 s d)))
        eSub = congL sub (ap1 s d) eTop

        -- Rewrite ap2 h2 (Snd (Snd params)) (sub (Fst params) (s d))
        --   -> ap2 h2 x (sub y_top (s d))
        eH2 : Deriv (eqF (ap2 h2 (ap1 Snd (ap1 Snd params))
                                  (ap2 sub (ap1 Fst params) (ap1 s d)))
                          (ap2 h2 x (ap2 sub y_top (ap1 s d))))
        eH2 = ruleTrans (congL h2 (ap2 sub (ap1 Fst params) (ap1 s d)) eX)
                        (congR h2 x eSub)

        -- Wrap into frmApp2 + kons
        eFrame : Deriv (eqF (frmApp2 h1c
                              (ap2 h2 (ap1 Snd (ap1 Snd params))
                                       (ap2 sub (ap1 Fst params) (ap1 s d))))
                            (frmApp2 h1c (ap2 h2 x (ap2 sub y_top (ap1 s d)))))
        eFrame = -- frmApp2 = pi (natCode tagApp2) (pi h1c arg)
                 congR pi (natCode tagApp2)
                   (congR pi h1c eH2)

        -- Lift to kons-level
        eKons : Deriv (eqF (kons (frmApp2 h1c
                              (ap2 h2 (ap1 Snd (ap1 Snd params))
                                       (ap2 sub (ap1 Fst params) (ap1 s d))))
                              (ap2 Stack params d))
                          (kons (frmApp2 h1c (ap2 h2 x (ap2 sub y_top (ap1 s d))))
                                (ap2 Stack params d)))
        eKons = congR pi (ap1 s O) (congL pi (ap2 Stack params d) eFrame)
    in ruleTrans e1 eKons
