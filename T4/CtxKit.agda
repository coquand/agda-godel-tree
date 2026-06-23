{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CtxKit -- a small reusable Hilbert-context plumbing kit for working "in
-- context [A,B]" or "[A,B,C]" (2 / 3 nested antecedents): hypothesis projection,
-- context modus ponens, closed-fact lifting, and equational transitivity.
-- Used by the object course-of-values tag dispatch, where the tag equality and
-- the validity hypothesis must be threaded together (no deduction theorem).
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.CtxKit where

open import T4.Base

open import BRA3.Logic          using ( eqSymImp )
open import BRA3.Contrapositive using ( liftP ; bComb ; bCombTwo ; identP )

------------------------------------------------------------------------
-- Depth-2 context  [Ga,Gb] .

lift2 : (Ga Gb : Formula) {X : Formula} -> Deriv X -> Deriv (imp Ga (imp Gb X))
lift2 Ga Gb d = liftP Ga (liftP Gb d)

get2a : (Ga Gb : Formula) -> Deriv (imp Ga (imp Gb Ga))
get2a Ga Gb = axK Ga Gb

get2b : (Ga Gb : Formula) -> Deriv (imp Ga (imp Gb Gb))
get2b Ga Gb = liftP Ga (identP Gb)

-- modus ponens in context [Ga,Gb]
ap2c : {Ga Gb A B : Formula} ->
       Deriv (imp Ga (imp Gb (imp A B))) ->
       Deriv (imp Ga (imp Gb A)) ->
       Deriv (imp Ga (imp Gb B))
ap2c d1 d2 = bCombTwo d1 d2

trans2c : {Ga Gb : Formula} (a b c : Term) ->
          Deriv (imp Ga (imp Gb (eqF a b))) ->
          Deriv (imp Ga (imp Gb (eqF b c))) ->
          Deriv (imp Ga (imp Gb (eqF a c)))
trans2c {Ga} {Gb} a b c f g =
  let fflip : Deriv (imp Ga (imp Gb (eqF b a)))
      fflip = ap2c (lift2 Ga Gb (eqSymImp a b)) f
      lifted : Deriv (imp Ga (imp Gb (imp (eqF b c) (eqF a c))))
      lifted = ap2c (lift2 Ga Gb (ax_eqTrans b a c)) fflip
  in ap2c lifted g

------------------------------------------------------------------------
-- Depth-3 context  [Ga,Gb,Gc] .

lift3 : (Ga Gb Gc : Formula) {X : Formula} ->
        Deriv X -> Deriv (imp Ga (imp Gb (imp Gc X)))
lift3 Ga Gb Gc d = liftP Ga (liftP Gb (liftP Gc d))

get3a : (Ga Gb Gc : Formula) -> Deriv (imp Ga (imp Gb (imp Gc Ga)))
get3a Ga Gb Gc = bComb (liftP Ga (axK (imp Gc Ga) Gb)) (axK Ga Gc)

get3b : (Ga Gb Gc : Formula) -> Deriv (imp Ga (imp Gb (imp Gc Gb)))
get3b Ga Gb Gc = liftP Ga (axK Gb Gc)

get3c : (Ga Gb Gc : Formula) -> Deriv (imp Ga (imp Gb (imp Gc Gc)))
get3c Ga Gb Gc = liftP Ga (liftP Gb (identP Gc))

ap3c : {Ga Gb Gc A B : Formula} ->
       Deriv (imp Ga (imp Gb (imp Gc (imp A B)))) ->
       Deriv (imp Ga (imp Gb (imp Gc A))) ->
       Deriv (imp Ga (imp Gb (imp Gc B)))
ap3c {Ga} {Gb} {Gc} d1 d2 =
  bCombTwo (bCombTwo (liftP Ga (liftP Gb (axS Gc _ _))) d1) d2

trans3c : {Ga Gb Gc : Formula} (a b c : Term) ->
          Deriv (imp Ga (imp Gb (imp Gc (eqF a b)))) ->
          Deriv (imp Ga (imp Gb (imp Gc (eqF b c)))) ->
          Deriv (imp Ga (imp Gb (imp Gc (eqF a c))))
trans3c {Ga} {Gb} {Gc} a b c f g =
  let fflip : Deriv (imp Ga (imp Gb (imp Gc (eqF b a))))
      fflip = ap3c (lift3 Ga Gb Gc (eqSymImp a b)) f
      lifted : Deriv (imp Ga (imp Gb (imp Gc (imp (eqF b c) (eqF a c)))))
      lifted = ap3c (lift3 Ga Gb Gc (ax_eqTrans b a c)) fflip
  in ap3c lifted g

------------------------------------------------------------------------
-- Depth-4 context  [Ga,Gb,Gc,Gd] .

lift4 : (Ga Gb Gc Gd : Formula) {X : Formula} ->
        Deriv X -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd X))))
lift4 Ga Gb Gc Gd d = liftP Ga (liftP Gb (liftP Gc (liftP Gd d)))

get4a : (Ga Gb Gc Gd : Formula) -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd Ga))))
get4a Ga Gb Gc Gd =
  let inner1 : Deriv (imp Ga (imp Gc (imp Gd Ga)))
      inner1 = bComb (liftP Ga (axK (imp Gd Ga) Gc)) (axK Ga Gd)
  in bComb (liftP Ga (axK (imp Gc (imp Gd Ga)) Gb)) inner1

get4b : (Ga Gb Gc Gd : Formula) -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd Gb))))
get4b Ga Gb Gc Gd = liftP Ga (get3a Gb Gc Gd)

get4c : (Ga Gb Gc Gd : Formula) -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd Gc))))
get4c Ga Gb Gc Gd = lift2 Ga Gb (axK Gc Gd)

get4d : (Ga Gb Gc Gd : Formula) -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd Gd))))
get4d Ga Gb Gc Gd = lift3 Ga Gb Gc (identP Gd)

ap4c : {Ga Gb Gc Gd A B : Formula} ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp A B))))) ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd A)))) ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd B))))
ap4c {Ga} {Gb} {Gc} {Gd} {A} {B} d1 d2 =
  ap3c (ap3c (lift3 Ga Gb Gc (axS Gd A B)) d1) d2

trans4c : {Ga Gb Gc Gd : Formula} (a b c : Term) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF a b))))) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF b c))))) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF a c)))))
trans4c {Ga} {Gb} {Gc} {Gd} a b c f g =
  let fflip : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (eqF b a)))))
      fflip = ap4c (lift4 Ga Gb Gc Gd (eqSymImp a b)) f
      lifted : Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp (eqF b c) (eqF a c))))))
      lifted = ap4c (lift4 Ga Gb Gc Gd (ax_eqTrans b a c)) fflip
  in ap4c lifted g

------------------------------------------------------------------------
-- Depth-5 context  [Ga,Gb,Gc,Gd,Ge] .

lift5 : (Ga Gb Gc Gd Ge : Formula) {X : Formula} ->
        Deriv X -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge X)))))
lift5 Ga Gb Gc Gd Ge d = liftP Ga (lift4 Gb Gc Gd Ge d)

get5a : (Ga Gb Gc Gd Ge : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Ga)))))
get5a Ga Gb Gc Gd Ge =
  bComb (liftP Ga (axK (imp Gc (imp Gd (imp Ge Ga))) Gb)) (get4a Ga Gc Gd Ge)

get5b : (Ga Gb Gc Gd Ge : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Gb)))))
get5b Ga Gb Gc Gd Ge = liftP Ga (get4a Gb Gc Gd Ge)

get5c : (Ga Gb Gc Gd Ge : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Gc)))))
get5c Ga Gb Gc Gd Ge = lift2 Ga Gb (get3a Gc Gd Ge)

get5d : (Ga Gb Gc Gd Ge : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Gd)))))
get5d Ga Gb Gc Gd Ge = lift3 Ga Gb Gc (axK Gd Ge)

get5e : (Ga Gb Gc Gd Ge : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge Ge)))))
get5e Ga Gb Gc Gd Ge = lift4 Ga Gb Gc Gd (identP Ge)

ap5c : {Ga Gb Gc Gd Ge A B : Formula} ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp A B)))))) ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge A))))) ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge B)))))
ap5c {Ga} {Gb} {Gc} {Gd} {Ge} {A} {B} d1 d2 =
  ap4c (ap4c (lift4 Ga Gb Gc Gd (axS Ge A B)) d1) d2

trans5c : {Ga Gb Gc Gd Ge : Formula} (a b c : Term) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF a b)))))) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF b c)))))) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (eqF a c))))))
trans5c {Ga} {Gb} {Gc} {Gd} {Ge} a b c f g =
  let fflip = ap5c (lift5 Ga Gb Gc Gd Ge (eqSymImp a b)) f
      lifted = ap5c (lift5 Ga Gb Gc Gd Ge (ax_eqTrans b a c)) fflip
  in ap5c lifted g

------------------------------------------------------------------------
-- Depth-6 context  [Ga,Gb,Gc,Gd,Ge,Gf] .

lift6 : (Ga Gb Gc Gd Ge Gf : Formula) {X : Formula} ->
        Deriv X -> Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf X))))))
lift6 Ga Gb Gc Gd Ge Gf d = liftP Ga (lift5 Gb Gc Gd Ge Gf d)

get6a : (Ga Gb Gc Gd Ge Gf : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Ga))))))
get6a Ga Gb Gc Gd Ge Gf =
  bComb (liftP Ga (axK (imp Gc (imp Gd (imp Ge (imp Gf Ga)))) Gb)) (get5a Ga Gc Gd Ge Gf)

get6b : (Ga Gb Gc Gd Ge Gf : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Gb))))))
get6b Ga Gb Gc Gd Ge Gf = liftP Ga (get5a Gb Gc Gd Ge Gf)

get6c : (Ga Gb Gc Gd Ge Gf : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Gc))))))
get6c Ga Gb Gc Gd Ge Gf = lift2 Ga Gb (get4a Gc Gd Ge Gf)

get6d : (Ga Gb Gc Gd Ge Gf : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Gd))))))
get6d Ga Gb Gc Gd Ge Gf = lift3 Ga Gb Gc (get3a Gd Ge Gf)

get6e : (Ga Gb Gc Gd Ge Gf : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Ge))))))
get6e Ga Gb Gc Gd Ge Gf = lift4 Ga Gb Gc Gd (axK Ge Gf)

get6f : (Ga Gb Gc Gd Ge Gf : Formula) ->
        Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf Gf))))))
get6f Ga Gb Gc Gd Ge Gf = lift5 Ga Gb Gc Gd Ge (identP Gf)

ap6c : {Ga Gb Gc Gd Ge Gf A B : Formula} ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (imp A B))))))) ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf A)))))) ->
       Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf B))))))
ap6c {Ga} {Gb} {Gc} {Gd} {Ge} {Gf} {A} {B} d1 d2 =
  ap5c (ap5c (lift5 Ga Gb Gc Gd Ge (axS Gf A B)) d1) d2

trans6c : {Ga Gb Gc Gd Ge Gf : Formula} (a b c : Term) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF a b))))))) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF b c))))))) ->
          Deriv (imp Ga (imp Gb (imp Gc (imp Gd (imp Ge (imp Gf (eqF a c)))))))
trans6c {Ga} {Gb} {Gc} {Gd} {Ge} {Gf} a b c f g =
  let fflip = ap6c (lift6 Ga Gb Gc Gd Ge Gf (eqSymImp a b)) f
      lifted = ap6c (lift6 Ga Gb Gc Gd Ge Gf (ax_eqTrans b a c)) fflip
  in ap6c lifted g
