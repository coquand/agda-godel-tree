{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.PrCodeObj -- object Goedel coding of the FULL closed-term primitive-
-- recursive calculus, generalising T4.TrsCodeObj from the toy data algebra
-- {ze#, su#, ad#} to the genuine BRA term algebra.
--
-- ‼ SCOPE CORRECTION (2026-06-23).  The HANDOFF-DIAMOND-FULL-PR.md rule list
-- (I/Z/o/u/v/Fst/Snd/Const/C/Rb/Rs/Comp/Lift/Fan/Post) over-states the
-- signature: per BRA3.Term the PRIMITIVE function algebra is only
--     Fun1 = { s , o , u , C g h1 h2 }       Fun2 = { v , R g h1 h2 }
--     Term = { O , var , ap1 f t , ap2 g a b }
-- and every other combinator (I = u, Z = o, Const = w, Fst, Snd, compose1U,
-- Lift1, Lift2, Fan, Post, pi, ...) is DEFINED in BRA3.Church / PairAlgebra as
-- an Agda combinator of these primitives -- NOT a constructor and NOT a
-- separate rewrite rule.  The computation axioms of BRA3.Deriv are EXACTLY
-- six:  ax_o, ax_u, ax_v, ax_C, ax_R_base, ax_R_step.  So the closed-term
-- reduction system R_pr to internalise is:
--
--     (o)   ap1 o t            -> O
--     (u)   ap1 u t            -> t
--     (v)   ap2 v a b          -> b
--     (C)   ap1 (C g h1 h2) t  -> ap2 g (ap1 h1 t) (ap1 h2 t)
--     (Rb)  ap2 (R g h1 h2) x O      -> ap1 g x
--     (Rs)  ap2 (R g h1 h2) x (s n)  -> ap2 h1 (ap2 h2 x n) (ap2 (R g h1 h2) x n)
--
-- with the constructor  s  (no rule; the successor / normal-form former).
-- This is ~2x the toy, NOT the ~14-rule expansion the handoff implied.
--
-- Coding (UNIFORMLY tagged pairs, all object Terms; subterm/sub-funcode slots
-- are arbitrary object Terms so every statement is SCHEMATIC = universal):
--   Terms:
--     tmO          = Pair (natCode 0) O              (= pi O O = O, fold base)
--     tmAp1 f t     = Pair (natCode 1) (Pair f t)
--     tmAp2 g a b   = Pair (natCode 2) (Pair g (Pair a b))
--   Fun1 codes:
--     cSuc          = Pair (natCode 3) O             (successor  s )
--     cZero         = Pair (natCode 4) O             (zero functor  o )
--     cId           = Pair (natCode 5) O             (identity  u )
--     cComp g h1 h2 = Pair (natCode 6) (Pair g (Pair h1 h2))   (C g h1 h2)
--   Fun2 codes:
--     cProj         = Pair (natCode 7) O             (second projection  v )
--     cRec g h1 h2  = Pair (natCode 8) (Pair g (Pair h1 h2))   (R g h1 h2)
--   Projectors:  hd = Fst (head tag),  ar = Snd (argument bundle).
--
-- NB.  tmO is a TAGGED pair (head tag  O = natCode 0 ), not the bare  O ;
-- uniform tagging lets the fold dispatch on the head tag of EVERY former.
-- Everything here is proved from axFst / axSnd (Pair algebra) -- no induction;
-- this is the constructor/decoder interface (mirror of T4.TrsCodeObj).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.PrCodeObj where

open import T4.Base

------------------------------------------------------------------------
-- SECTION 0.  Tags (object Terms).

tgO : Term
tgO = natCode 0

tgAp1 : Term
tgAp1 = natCode 1

tgAp2 : Term
tgAp2 = natCode 2

tgSuc : Term
tgSuc = natCode 3

tgZero : Term
tgZero = natCode 4

tgId : Term
tgId = natCode 5

tgComp : Term
tgComp = natCode 6

tgProj : Term
tgProj = natCode 7

tgRec : Term
tgRec = natCode 8

------------------------------------------------------------------------
-- SECTION 1.  Constructors (object Terms).

-- Term constructors.
tmO : Term
tmO = ap2 Pair tgO O

tmAp1 : Term -> Term -> Term
tmAp1 f t = ap2 Pair tgAp1 (ap2 Pair f t)

tmAp2 : Term -> Term -> Term -> Term
tmAp2 g a b = ap2 Pair tgAp2 (ap2 Pair g (ap2 Pair a b))

-- Fun1 codes.
cSuc : Term
cSuc = ap2 Pair tgSuc O

cZero : Term
cZero = ap2 Pair tgZero O

cId : Term
cId = ap2 Pair tgId O

cComp : Term -> Term -> Term -> Term
cComp g h1 h2 = ap2 Pair tgComp (ap2 Pair g (ap2 Pair h1 h2))

-- Fun2 codes.
cProj : Term
cProj = ap2 Pair tgProj O

cRec : Term -> Term -> Term -> Term
cRec g h1 h2 = ap2 Pair tgRec (ap2 Pair g (ap2 Pair h1 h2))

------------------------------------------------------------------------
-- SECTION 2.  Projectors.

hd : Term -> Term
hd t = ap1 Fst t

ar : Term -> Term
ar t = ap1 Snd t

------------------------------------------------------------------------
-- SECTION 3.  Head-tag projection equations (universal in the subterm codes).

hd_tmO : Deriv (eqF (hd tmO) tgO)
hd_tmO = axFst tgO O

hd_tmAp1 : (f t : Term) -> Deriv (eqF (hd (tmAp1 f t)) tgAp1)
hd_tmAp1 f t = axFst tgAp1 (ap2 Pair f t)

hd_tmAp2 : (g a b : Term) -> Deriv (eqF (hd (tmAp2 g a b)) tgAp2)
hd_tmAp2 g a b = axFst tgAp2 (ap2 Pair g (ap2 Pair a b))

hd_cSuc : Deriv (eqF (hd cSuc) tgSuc)
hd_cSuc = axFst tgSuc O

hd_cZero : Deriv (eqF (hd cZero) tgZero)
hd_cZero = axFst tgZero O

hd_cId : Deriv (eqF (hd cId) tgId)
hd_cId = axFst tgId O

hd_cComp : (g h1 h2 : Term) -> Deriv (eqF (hd (cComp g h1 h2)) tgComp)
hd_cComp g h1 h2 = axFst tgComp (ap2 Pair g (ap2 Pair h1 h2))

hd_cProj : Deriv (eqF (hd cProj) tgProj)
hd_cProj = axFst tgProj O

hd_cRec : (g h1 h2 : Term) -> Deriv (eqF (hd (cRec g h1 h2)) tgRec)
hd_cRec g h1 h2 = axFst tgRec (ap2 Pair g (ap2 Pair h1 h2))

------------------------------------------------------------------------
-- SECTION 4.  Argument-bundle projection equations.

ar_tmO : Deriv (eqF (ar tmO) O)
ar_tmO = axSnd tgO O

ar_tmAp1 : (f t : Term) -> Deriv (eqF (ar (tmAp1 f t)) (ap2 Pair f t))
ar_tmAp1 f t = axSnd tgAp1 (ap2 Pair f t)

ar_tmAp2 : (g a b : Term) ->
           Deriv (eqF (ar (tmAp2 g a b)) (ap2 Pair g (ap2 Pair a b)))
ar_tmAp2 g a b = axSnd tgAp2 (ap2 Pair g (ap2 Pair a b))

ar_cComp : (g h1 h2 : Term) ->
           Deriv (eqF (ar (cComp g h1 h2)) (ap2 Pair g (ap2 Pair h1 h2)))
ar_cComp g h1 h2 = axSnd tgComp (ap2 Pair g (ap2 Pair h1 h2))

ar_cRec : (g h1 h2 : Term) ->
          Deriv (eqF (ar (cRec g h1 h2)) (ap2 Pair g (ap2 Pair h1 h2)))
ar_cRec g h1 h2 = axSnd tgRec (ap2 Pair g (ap2 Pair h1 h2))

------------------------------------------------------------------------
-- SECTION 5.  Component accessors (the sub-funcodes / subterms of a node),
-- mirror T4.TrsCodeObj.ad1 / ad2 (ruleTrans (cong1 Fst (ar_..)) (axFst ..)).

-- tmAp1 f t :  fun-head  f = Fst (ar) ,  arg  t = Snd (ar) .
ap1Fun : (f t : Term) -> Deriv (eqF (ap1 Fst (ar (tmAp1 f t))) f)
ap1Fun f t = ruleTrans (cong1 Fst (ar_tmAp1 f t)) (axFst f t)

ap1Arg : (f t : Term) -> Deriv (eqF (ap1 Snd (ar (tmAp1 f t))) t)
ap1Arg f t = ruleTrans (cong1 Snd (ar_tmAp1 f t)) (axSnd f t)

-- tmAp2 g a b :  fun-head  g = Fst (ar) ,  inner bundle  Pair a b = Snd (ar) .
ap2Fun : (g a b : Term) -> Deriv (eqF (ap1 Fst (ar (tmAp2 g a b))) g)
ap2Fun g a b = ruleTrans (cong1 Fst (ar_tmAp2 g a b)) (axFst g (ap2 Pair a b))

ap2Bundle : (g a b : Term) ->
            Deriv (eqF (ap1 Snd (ar (tmAp2 g a b))) (ap2 Pair a b))
ap2Bundle g a b = ruleTrans (cong1 Snd (ar_tmAp2 g a b)) (axSnd g (ap2 Pair a b))

ap2Arg1 : (g a b : Term) ->
          Deriv (eqF (ap1 Fst (ap1 Snd (ar (tmAp2 g a b)))) a)
ap2Arg1 g a b = ruleTrans (cong1 Fst (ap2Bundle g a b)) (axFst a b)

ap2Arg2 : (g a b : Term) ->
          Deriv (eqF (ap1 Snd (ap1 Snd (ar (tmAp2 g a b)))) b)
ap2Arg2 g a b = ruleTrans (cong1 Snd (ap2Bundle g a b)) (axSnd a b)

-- cComp g h1 h2 :  g = Fst (ar) ,  h1 = Fst (Snd (ar)) ,  h2 = Snd (Snd (ar)) .
compFun : (g h1 h2 : Term) -> Deriv (eqF (ap1 Fst (ar (cComp g h1 h2))) g)
compFun g h1 h2 = ruleTrans (cong1 Fst (ar_cComp g h1 h2)) (axFst g (ap2 Pair h1 h2))

compBundle : (g h1 h2 : Term) ->
             Deriv (eqF (ap1 Snd (ar (cComp g h1 h2))) (ap2 Pair h1 h2))
compBundle g h1 h2 = ruleTrans (cong1 Snd (ar_cComp g h1 h2)) (axSnd g (ap2 Pair h1 h2))

compH1 : (g h1 h2 : Term) ->
         Deriv (eqF (ap1 Fst (ap1 Snd (ar (cComp g h1 h2)))) h1)
compH1 g h1 h2 = ruleTrans (cong1 Fst (compBundle g h1 h2)) (axFst h1 h2)

compH2 : (g h1 h2 : Term) ->
         Deriv (eqF (ap1 Snd (ap1 Snd (ar (cComp g h1 h2)))) h2)
compH2 g h1 h2 = ruleTrans (cong1 Snd (compBundle g h1 h2)) (axSnd h1 h2)

-- cRec g h1 h2 :  same shape as cComp.
recFun : (g h1 h2 : Term) -> Deriv (eqF (ap1 Fst (ar (cRec g h1 h2))) g)
recFun g h1 h2 = ruleTrans (cong1 Fst (ar_cRec g h1 h2)) (axFst g (ap2 Pair h1 h2))

recBundle : (g h1 h2 : Term) ->
            Deriv (eqF (ap1 Snd (ar (cRec g h1 h2))) (ap2 Pair h1 h2))
recBundle g h1 h2 = ruleTrans (cong1 Snd (ar_cRec g h1 h2)) (axSnd g (ap2 Pair h1 h2))

recH1 : (g h1 h2 : Term) ->
        Deriv (eqF (ap1 Fst (ap1 Snd (ar (cRec g h1 h2)))) h1)
recH1 g h1 h2 = ruleTrans (cong1 Fst (recBundle g h1 h2)) (axFst h1 h2)

recH2 : (g h1 h2 : Term) ->
        Deriv (eqF (ap1 Snd (ap1 Snd (ar (cRec g h1 h2)))) h2)
recH2 g h1 h2 = ruleTrans (cong1 Snd (recBundle g h1 h2)) (axSnd h1 h2)
