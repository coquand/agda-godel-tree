{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ParseRoundtrip -- the load-bearing correctness of  BRA4.Parse :
-- on the CANONICAL prefix linearization of a term  t , the stack-machine
--  parse  rebuilds exactly  codeTerm t .
--
--   linT  : the meta-level (CPS / difference-list) PREFIX linearization
--           of a Term , with  linF1 / linF2  for the embedded Fun1 / Fun2 .
--           linT t rest = tokens(t) ++ rest .
--
--   push_T / push_F1 / push_F2 :  the compositional invariant, by
--           STRUCTURAL meta-induction:
--             parseS (linT t rest)   = pi (codeTerm t)  (parseS rest)
--             parseS (linF1 f rest)  = pi (codeFun1 f) (parseS rest)
--             parseS (linF2 g rest)  = pi (codeFun2 g) (parseS rest)
--           i.e. linearizing  X  and parsing prepends  code X  onto the
--           prior stack -- exactly the stack PUSH the step performs.
--
--   parse_roundtrip_term :  parse (linT t O) = codeTerm t
--           (rest = O => the final stack is the single element codeTerm t ;
--            parse = Fst o parseS reads it off).
--
-- This validates that the linear NAME (lenR-faithful, finite-per-length)
-- and the tree CODE  thmT  reads carry the same content -- the KR-A
-- name-format soundness that  rank / DefWit / con_inj build on.

module BRA4.ParseRoundtrip where

open import BRA4.Base
open import BRA4.Tags
open import BRA4.Code
open import BRA4.Parse

open import BRA3.Church       using ( pi )
open import BRA3.ChurchT117   using ( Fst )
open import BRA3.ChurchT116   using ( Snd )
open import BRA3.PairAlgebra  using ( axFst ; axSnd ; compose1U_eq )

------------------------------------------------------------------------
-- The PREFIX linearization (CPS / difference-list form).
--
-- A leaf token carries the code it pushes (cellLeaf ...); an arity
-- token carries the built-node tag (cellAr2 / cellAr3 ...).  Each
-- linX appends its tokens in PREFIX order in front of the suffix  rest .

linT  : Term -> Term -> Term
linF1 : Fun1 -> Term -> Term
linF2 : Fun2 -> Term -> Term

linT O           rest = ap2 pi (cellLeaf (codeTerm O)) rest
linT (var k)     rest = ap2 pi (cellLeaf (codeTerm (var k))) rest
linT (ap1 f t)   rest = ap2 pi (cellAr2 (natCode tag_ap1)) (linF1 f (linT t rest))
linT (ap2 g a b) rest = ap2 pi (cellAr3 (natCode tag_ap2)) (linF2 g (linT a (linT b rest)))

linF1 s          rest = ap2 pi (cellLeaf (codeFun1 s)) rest
linF1 o          rest = ap2 pi (cellLeaf (codeFun1 o)) rest
linF1 u          rest = ap2 pi (cellLeaf (codeFun1 u)) rest
linF1 (C g h1 h2) rest = ap2 pi (cellAr3 (natCode tag_C)) (linF2 g (linF1 h1 (linF1 h2 rest)))

linF2 v          rest = ap2 pi (cellLeaf (codeFun2 v)) rest
linF2 (R g h1 h2) rest = ap2 pi (cellAr3 (natCode tag_R)) (linF1 g (linF2 h1 (linF2 h2 rest)))

-- Top-level linearization (empty suffix).
linTop : Term -> Term
linTop t = linT t O

------------------------------------------------------------------------
-- Arity-2 assembly: given  PS = parseS rest'  proven equal to
--   pi q1 (pi q2 tail) , rewrite  parse_at_ar2 's raw RHS into
--   pi (pi p (pi q1 q2)) tail .

private
  ar2_collapse :
    (p rest' q1 q2 tail : Term) ->
    Deriv (eqF (ap1 parseS rest') (ap2 pi q1 (ap2 pi q2 tail))) ->
    Deriv (eqF (ap1 parseS (ap2 pi (cellAr2 p) rest'))
                (ap2 pi (ap2 pi p (ap2 pi q1 q2)) tail))
  ar2_collapse p rest' q1 q2 tail ps_eq =
    let PS : Term
        PS = ap1 parseS rest'

        PSval : Term
        PSval = ap2 pi q1 (ap2 pi q2 tail)

        raw : Deriv (eqF (ap1 parseS (ap2 pi (cellAr2 p) rest'))
                          (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst PS)
                                                    (ap1 Fst (ap1 Snd PS))))
                                  (ap1 Snd (ap1 Snd PS))))
        raw = parse_at_ar2 p rest'

        fst_ps : Deriv (eqF (ap1 Fst PS) q1)
        fst_ps = ruleTrans (cong1 Fst ps_eq) (axFst q1 (ap2 pi q2 tail))

        snd_ps : Deriv (eqF (ap1 Snd PS) (ap2 pi q2 tail))
        snd_ps = ruleTrans (cong1 Snd ps_eq) (axSnd q1 (ap2 pi q2 tail))

        fst_snd_ps : Deriv (eqF (ap1 Fst (ap1 Snd PS)) q2)
        fst_snd_ps = ruleTrans (cong1 Fst snd_ps) (axFst q2 tail)

        snd_snd_ps : Deriv (eqF (ap1 Snd (ap1 Snd PS)) tail)
        snd_snd_ps = ruleTrans (cong1 Snd snd_ps) (axSnd q2 tail)

        inner : Deriv (eqF (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS)))
                           (ap2 pi q1 q2))
        inner = ruleTrans (congL pi (ap1 Fst (ap1 Snd PS)) fst_ps)
                          (congR pi q1 fst_snd_ps)

        built : Deriv (eqF (ap2 pi p (ap2 pi (ap1 Fst PS) (ap1 Fst (ap1 Snd PS))))
                           (ap2 pi p (ap2 pi q1 q2)))
        built = congR pi p inner

        full : Deriv (eqF (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst PS)
                                                    (ap1 Fst (ap1 Snd PS))))
                                  (ap1 Snd (ap1 Snd PS)))
                          (ap2 pi (ap2 pi p (ap2 pi q1 q2)) tail))
        full = ruleTrans (congL pi (ap1 Snd (ap1 Snd PS)) built)
                         (congR pi (ap2 pi p (ap2 pi q1 q2)) snd_snd_ps)
    in ruleTrans raw full

  ar3_collapse :
    (p rest' q1 q2 q3 tail : Term) ->
    Deriv (eqF (ap1 parseS rest')
                (ap2 pi q1 (ap2 pi q2 (ap2 pi q3 tail)))) ->
    Deriv (eqF (ap1 parseS (ap2 pi (cellAr3 p) rest'))
                (ap2 pi (ap2 pi p (ap2 pi q1 (ap2 pi q2 q3))) tail))
  ar3_collapse p rest' q1 q2 q3 tail ps_eq =
    let PS : Term
        PS = ap1 parseS rest'

        raw : Deriv (eqF (ap1 parseS (ap2 pi (cellAr3 p) rest'))
                          (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst PS)
                                                    (ap2 pi (ap1 Fst (ap1 Snd PS))
                                                            (ap1 Fst (ap1 Snd (ap1 Snd PS))))))
                                  (ap1 Snd (ap1 Snd (ap1 Snd PS)))))
        raw = parse_at_ar3 p rest'

        fst_ps : Deriv (eqF (ap1 Fst PS) q1)
        fst_ps = ruleTrans (cong1 Fst ps_eq)
                           (axFst q1 (ap2 pi q2 (ap2 pi q3 tail)))

        snd_ps : Deriv (eqF (ap1 Snd PS) (ap2 pi q2 (ap2 pi q3 tail)))
        snd_ps = ruleTrans (cong1 Snd ps_eq)
                           (axSnd q1 (ap2 pi q2 (ap2 pi q3 tail)))

        fst_snd_ps : Deriv (eqF (ap1 Fst (ap1 Snd PS)) q2)
        fst_snd_ps = ruleTrans (cong1 Fst snd_ps) (axFst q2 (ap2 pi q3 tail))

        snd_snd_ps : Deriv (eqF (ap1 Snd (ap1 Snd PS)) (ap2 pi q3 tail))
        snd_snd_ps = ruleTrans (cong1 Snd snd_ps) (axSnd q2 (ap2 pi q3 tail))

        fst_snd_snd_ps : Deriv (eqF (ap1 Fst (ap1 Snd (ap1 Snd PS))) q3)
        fst_snd_snd_ps = ruleTrans (cong1 Fst snd_snd_ps) (axFst q3 tail)

        snd_snd_snd_ps : Deriv (eqF (ap1 Snd (ap1 Snd (ap1 Snd PS))) tail)
        snd_snd_snd_ps = ruleTrans (cong1 Snd snd_snd_ps) (axSnd q3 tail)

        -- inner2 = pi top2 top3 -> pi q2 q3
        inner2 : Deriv (eqF (ap2 pi (ap1 Fst (ap1 Snd PS))
                                    (ap1 Fst (ap1 Snd (ap1 Snd PS))))
                            (ap2 pi q2 q3))
        inner2 = ruleTrans (congL pi (ap1 Fst (ap1 Snd (ap1 Snd PS))) fst_snd_ps)
                           (congR pi q2 fst_snd_snd_ps)

        -- inner = pi top1 (pi top2 top3) -> pi q1 (pi q2 q3)
        inner : Deriv (eqF (ap2 pi (ap1 Fst PS)
                                   (ap2 pi (ap1 Fst (ap1 Snd PS))
                                           (ap1 Fst (ap1 Snd (ap1 Snd PS)))))
                           (ap2 pi q1 (ap2 pi q2 q3)))
        inner = ruleTrans (congL pi (ap2 pi (ap1 Fst (ap1 Snd PS))
                                            (ap1 Fst (ap1 Snd (ap1 Snd PS)))) fst_ps)
                          (congR pi q1 inner2)

        built : Deriv (eqF (ap2 pi p (ap2 pi (ap1 Fst PS)
                                             (ap2 pi (ap1 Fst (ap1 Snd PS))
                                                     (ap1 Fst (ap1 Snd (ap1 Snd PS))))))
                           (ap2 pi p (ap2 pi q1 (ap2 pi q2 q3))))
        built = congR pi p inner

        full : Deriv (eqF (ap2 pi (ap2 pi p (ap2 pi (ap1 Fst PS)
                                                    (ap2 pi (ap1 Fst (ap1 Snd PS))
                                                            (ap1 Fst (ap1 Snd (ap1 Snd PS))))))
                                  (ap1 Snd (ap1 Snd (ap1 Snd PS))))
                          (ap2 pi (ap2 pi p (ap2 pi q1 (ap2 pi q2 q3))) tail))
        full = ruleTrans (congL pi (ap1 Snd (ap1 Snd (ap1 Snd PS))) built)
                         (congR pi (ap2 pi p (ap2 pi q1 (ap2 pi q2 q3))) snd_snd_snd_ps)
    in ruleTrans raw full

------------------------------------------------------------------------
-- The compositional invariant (mutual structural meta-induction).

push_T  : (t : Term) (rest : Term) ->
  Deriv (eqF (ap1 parseS (linT t rest)) (ap2 pi (codeTerm t) (ap1 parseS rest)))
push_F1 : (f : Fun1) (rest : Term) ->
  Deriv (eqF (ap1 parseS (linF1 f rest)) (ap2 pi (codeFun1 f) (ap1 parseS rest)))
push_F2 : (g : Fun2) (rest : Term) ->
  Deriv (eqF (ap1 parseS (linF2 g rest)) (ap2 pi (codeFun2 g) (ap1 parseS rest)))

-- Term.

push_T O rest = parse_at_leaf (codeTerm O) rest
push_T (var k) rest = parse_at_leaf (codeTerm (var k)) rest
push_T (ap1 f t) rest =
  let -- parseS (linF1 f (linT t rest)) = pi (codeFun1 f) (pi (codeTerm t) (parseS rest))
      ps_eq : Deriv (eqF (ap1 parseS (linF1 f (linT t rest)))
                          (ap2 pi (codeFun1 f) (ap2 pi (codeTerm t) (ap1 parseS rest))))
      ps_eq = ruleTrans (push_F1 f (linT t rest))
                        (congR pi (codeFun1 f) (push_T t rest))
  in ar2_collapse (natCode tag_ap1) (linF1 f (linT t rest))
                  (codeFun1 f) (codeTerm t) (ap1 parseS rest) ps_eq
push_T (ap2 g a b) rest =
  let ps_eq : Deriv (eqF (ap1 parseS (linF2 g (linT a (linT b rest))))
                          (ap2 pi (codeFun2 g)
                                  (ap2 pi (codeTerm a)
                                          (ap2 pi (codeTerm b) (ap1 parseS rest)))))
      ps_eq = ruleTrans (push_F2 g (linT a (linT b rest)))
                        (congR pi (codeFun2 g)
                          (ruleTrans (push_T a (linT b rest))
                                     (congR pi (codeTerm a) (push_T b rest))))
  in ar3_collapse (natCode tag_ap2) (linF2 g (linT a (linT b rest)))
                  (codeFun2 g) (codeTerm a) (codeTerm b) (ap1 parseS rest) ps_eq

-- Fun1.

push_F1 s rest = parse_at_leaf (codeFun1 s) rest
push_F1 o rest = parse_at_leaf (codeFun1 o) rest
push_F1 u rest = parse_at_leaf (codeFun1 u) rest
push_F1 (C g h1 h2) rest =
  let ps_eq : Deriv (eqF (ap1 parseS (linF2 g (linF1 h1 (linF1 h2 rest))))
                          (ap2 pi (codeFun2 g)
                                  (ap2 pi (codeFun1 h1)
                                          (ap2 pi (codeFun1 h2) (ap1 parseS rest)))))
      ps_eq = ruleTrans (push_F2 g (linF1 h1 (linF1 h2 rest)))
                        (congR pi (codeFun2 g)
                          (ruleTrans (push_F1 h1 (linF1 h2 rest))
                                     (congR pi (codeFun1 h1) (push_F1 h2 rest))))
  in ar3_collapse (natCode tag_C) (linF2 g (linF1 h1 (linF1 h2 rest)))
                  (codeFun2 g) (codeFun1 h1) (codeFun1 h2) (ap1 parseS rest) ps_eq

-- Fun2.

push_F2 v rest = parse_at_leaf (codeFun2 v) rest
push_F2 (R g h1 h2) rest =
  let ps_eq : Deriv (eqF (ap1 parseS (linF1 g (linF2 h1 (linF2 h2 rest))))
                          (ap2 pi (codeFun1 g)
                                  (ap2 pi (codeFun2 h1)
                                          (ap2 pi (codeFun2 h2) (ap1 parseS rest)))))
      ps_eq = ruleTrans (push_F1 g (linF2 h1 (linF2 h2 rest)))
                        (congR pi (codeFun1 g)
                          (ruleTrans (push_F2 h1 (linF2 h2 rest))
                                     (congR pi (codeFun2 h1) (push_F2 h2 rest))))
  in ar3_collapse (natCode tag_R) (linF1 g (linF2 h1 (linF2 h2 rest)))
                  (codeFun1 g) (codeFun2 h1) (codeFun2 h2) (ap1 parseS rest) ps_eq

------------------------------------------------------------------------
-- parse_roundtrip_term :  parse (linT t O) = codeTerm t .

parse_roundtrip_term :
  (t : Term) ->
  Deriv (eqF (ap1 parse (linTop t)) (codeTerm t))
parse_roundtrip_term t =
  let e1 : Deriv (eqF (ap1 parse (linTop t)) (ap1 Fst (ap1 parseS (linTop t))))
      e1 = compose1U_eq Fst parseS (linTop t)

      e2 : Deriv (eqF (ap1 parseS (linTop t))
                      (ap2 pi (codeTerm t) (ap1 parseS O)))
      e2 = push_T t O

      e3 : Deriv (eqF (ap1 Fst (ap1 parseS (linTop t)))
                      (ap1 Fst (ap2 pi (codeTerm t) (ap1 parseS O))))
      e3 = cong1 Fst e2

      e4 : Deriv (eqF (ap1 Fst (ap2 pi (codeTerm t) (ap1 parseS O))) (codeTerm t))
      e4 = axFst (codeTerm t) (ap1 parseS O)
  in ruleTrans e1 (ruleTrans e3 e4)
