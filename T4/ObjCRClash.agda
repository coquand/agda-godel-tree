{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ObjCRClash -- head-stability, the clash, and the toy Con(T0) headline, on
-- the FROM-SCRATCH coded-derivation representation of T4.ObjCR (Theorem B of
-- T4/CON-T0-ARCHITECTURE.md at this layer, plus the consistency atom).
--
-- ze# is normal and su#-headed terms reduce only inside, so ze and su ze have
-- NO common reduct.  Combined with confluence (T4.ObjCR.confl) this gives
--
--   zeNotConvSuZe : Not (Conv ze (su ze))      ( = the toy  0 != s0 )
--
-- exactly the headline of T4.ChurchRosserProto, but now built on the strict
-- coded derivation trees `Der`/`Red` instead of the proto's merged `Par`.
--
-- Head-stability is proved by INVERSION on the strict `Red` family: the source
-- index pins which constructors are possible (only `rdZe` from ze, only `rdSu`
-- from su _), so the `Reds` recursion short-circuits structurally.  No
-- interpreter, no fuel.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ObjCRClash where

open import T4.ChurchRosserProto
  using ( Tm ; ze ; su ; ad
        ; Sigma ; mkSigma ; fst ; snd
        ; And ; mkAnd ; andL ; andR
        ; Empty ; Not ; emptyElim
        ; Eq ; refl ; eqTrans ; eqSubst
        ; zeNeqSu )

open import T4.ObjCR
  using ( Der ; Red ; rdZe ; rdSu
        ; Reds ; rsdone ; rsmore ; redsTrans ; red1
        ; confl ; ObjJoin )

------------------------------------------------------------------------
-- SECTION 0.  A local symmetry of Eq (proto exports trans/subst, not sym).

eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
eqSym {A} {x} e = eqSubst (\ z -> Eq z x) e refl

------------------------------------------------------------------------
-- SECTION 1.  Head-stability by inversion on the strict  Red  family.
--
-- From  ze  only  rdZe  applies (source index ze rules out every other
-- constructor), and it forces the target to be ze; so a whole chain from ze
-- ends at ze.  From  su _  only  rdSu  applies, forcing a su-head throughout.

redsZeInv : {w : Tm} -> Reds ze w -> Eq w ze
redsZeInv rsdone                = refl
redsZeInv (rsmore _ rdZe rest)  = redsZeInv rest

redsSuInv : {t w : Tm} -> Reds (su t) w -> Sigma Tm (\ t' -> Eq w (su t'))
redsSuInv {t} rsdone                  = mkSigma t refl
redsSuInv (rsmore _ (rdSu rp) rest)   = redsSuInv rest

------------------------------------------------------------------------
-- SECTION 2.  THE CLASH:  ze and su ze have no common reduct.

redsClash : {w : Tm} -> Reds ze w -> Reds (su ze) w -> Empty
redsClash {w} r0 rS =
  let e0 : Eq w ze
      e0 = redsZeInv r0
      eS : Sigma Tm (\ t' -> Eq w (su t'))
      eS = redsSuInv rS
  in zeNeqSu (eqTrans (eqSym e0) (snd eS))

zeNotJoinSuZe : Not (ObjJoin ze (su ze))
zeNotJoinSuZe (mkSigma w p) = redsClash (andL p) (andR p)

------------------------------------------------------------------------
-- SECTION 3.  ObjJoin is symmetric and transitive (transitivity via confl).

joinSym : {t u : Tm} -> ObjJoin t u -> ObjJoin u t
joinSym (mkSigma w p) = mkSigma w (mkAnd (andR p) (andL p))

joinTrans : {t u v : Tm} -> ObjJoin t u -> ObjJoin u v -> ObjJoin t v
joinTrans (mkSigma w1 p1) (mkSigma w2 p2) =
  let c = confl (andR p1) (andL p2)         -- u -> w1 and u -> w2 join at fst c
  in mkSigma (fst c)
       (mkAnd (redsTrans (andL p1) (andL (snd c)))
              (redsTrans (andR p2) (andR (snd c))))

------------------------------------------------------------------------
-- SECTION 4.  Convertibility and the toy Con(T0) headline.

data Conv : Tm -> Tm -> Set where
  cstep  : {p : Der} {t u : Tm} -> Red p t u     -> Conv t u
  crefl  : {t : Tm}                              -> Conv t t
  csym   : {t u : Tm}   -> Conv t u              -> Conv u t
  ctrans : {t u v : Tm} -> Conv t u -> Conv u v   -> Conv t v

-- Church-Rosser corollary: convertible terms are joinable.
convJoin : {t u : Tm} -> Conv t u -> ObjJoin t u
convJoin (cstep {p} {t} {u} r) = mkSigma u (mkAnd (red1 r) rsdone)
convJoin (crefl {t})           = mkSigma t (mkAnd rsdone rsdone)
convJoin (csym c)              = joinSym (convJoin c)
convJoin (ctrans c1 c2)        = joinTrans (convJoin c1) (convJoin c2)

-- THE CONSISTENCY ATOM:  0 is not convertible to s0  (toy Con(T0)).
zeNotConvSuZe : Not (Conv ze (su ze))
zeNotConvSuZe c = zeNotJoinSuZe (convJoin c)
